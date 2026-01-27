#!/usr/bin/env python3
"""Benchmark sync vs async link checking.

Tests various scenarios:
- Small corpus (current docs/)
- Large corpus (synthetic)
- Different file sizes
"""

import pathlib
import tempfile
import time

from . import check_links


def create_test_file(path: pathlib.Path, size: int, links: int = 10):
    """Create a markdown file with headers and links."""
    content = [f"# Test File {path.name}\n\n"]

    # Add headers
    for i in range(5):
        content.append(f"## Section {i}\n\n")
        content.append("x" * (size // 10) + "\n\n")

    # Add internal links
    for i in range(links // 2):
        content.append(f"[Link to section {i % 5}](#section-{i % 5})\n")

    # Add external links (to other files)
    for i in range(links // 2):
        content.append(f"[Link to other](./file_{i % 10}.md)\n")

    path.write_text("".join(content))


def create_corpus(temp_dir: pathlib.Path, n_files: int, file_size: int):
    """Create a test corpus."""
    for i in range(n_files):
        create_test_file(temp_dir / f"file_{i}.md", file_size)


def benchmark(name: str, func, iterations: int = 5) -> float:
    """Run benchmark, return median time."""
    times = []
    for _ in range(iterations):
        start = time.perf_counter()
        func()
        times.append(time.perf_counter() - start)
    median = sorted(times)[len(times) // 2]
    return median


def run_comparison(docs_root: pathlib.Path, iterations: int = 5):
    """Run sync vs async comparison."""
    print(f"\nBenchmarking {docs_root} ({iterations} iterations):")

    # Warm up
    check_links.collect_files_sync(docs_root)

    # Benchmark sync
    sync_time = benchmark("sync", lambda: check_links.collect_files_sync(docs_root), iterations)
    print(f"  Sync:  {sync_time:.3f}s")

    # Benchmark async
    import anyio
    async_time = benchmark(
        "async",
        lambda: anyio.run(check_links.collect_files_async, docs_root),
        iterations
    )
    print(f"  Async: {async_time:.3f}s")

    # Comparison
    speedup = sync_time / async_time if async_time > 0 else float('inf')
    print(f"  Speedup: {speedup:.2f}x")

    return sync_time, async_time


def simulate_io_latency_sync(docs_root: pathlib.Path, latency_ms: float = 5.0):
    """Sync version with simulated I/O latency."""
    files = {}
    errors = []
    for path in docs_root.rglob("*.md"):
        time.sleep(latency_ms / 1000)  # Simulate I/O latency
        path = pathlib.Path(check_links.os.path.normpath(path))
        content = path.read_text(encoding='utf-8')
        file_data, file_errors = check_links.process_content(path, content)
        files[path] = file_data
        errors.extend(file_errors)
    return files, errors


async def simulate_io_latency_async(docs_root: pathlib.Path, latency_ms: float = 5.0):
    """Async version with simulated I/O latency."""
    import anyio

    paths = list(docs_root.rglob("*.md"))
    io_sem = anyio.Semaphore(check_links.MAX_CONCURRENT_IO)
    results = []

    async def load_one(path: pathlib.Path):
        async with io_sem:
            await anyio.sleep(latency_ms / 1000)  # Simulate I/O latency
            content = path.read_text(encoding='utf-8')
        norm_path = pathlib.Path(check_links.os.path.normpath(path))
        file_data, errors = check_links.process_content(norm_path, content)
        results.append((norm_path, file_data, errors))

    async with anyio.create_task_group() as tg:
        for path in paths:
            tg.start_soon(load_one, path)

    files = {path: data for path, data, _ in results}
    errors = [e for _, _, errs in results for e in errs]
    return files, errors


def run_latency_comparison(docs_root: pathlib.Path, latency_ms: float = 5.0):
    """Compare sync vs async with simulated I/O latency."""
    import anyio

    n_files = len(list(docs_root.rglob("*.md")))
    print(f"\nSimulated {latency_ms}ms I/O latency ({n_files} files):")

    # Sync: sequential, total time = n_files * latency
    start = time.perf_counter()
    simulate_io_latency_sync(docs_root, latency_ms)
    sync_time = time.perf_counter() - start
    print(f"  Sync:  {sync_time:.3f}s (theoretical min: {n_files * latency_ms / 1000:.3f}s)")

    # Async: parallel I/O, total time ≈ latency * ceil(n_files / concurrency)
    start = time.perf_counter()
    anyio.run(simulate_io_latency_async, docs_root, latency_ms)
    async_time = time.perf_counter() - start
    theoretical_async = (n_files / check_links.MAX_CONCURRENT_IO) * latency_ms / 1000
    print(f"  Async: {async_time:.3f}s (theoretical min: {theoretical_async:.3f}s)")

    speedup = sync_time / async_time if async_time > 0 else float('inf')
    print(f"  Speedup: {speedup:.2f}x")

    return sync_time, async_time


def main():
    """Run benchmark suite."""
    print("=" * 60)
    print("Link Checker Benchmark: Sync vs Async")
    print("=" * 60)

    # Benchmark on actual docs/
    actual_docs = check_links.DOCS_ROOT.resolve()
    if actual_docs.exists():
        n_files = len(list(actual_docs.rglob("*.md")))
        print(f"\n[1] Actual docs/ ({n_files} files) - Hot Cache")
        run_comparison(actual_docs)

        # Test with simulated I/O latency (shows async advantage)
        print(f"\n[2] Simulated I/O Latency Test")
        run_latency_comparison(actual_docs, latency_ms=5.0)

    # Synthetic benchmarks
    test_cases = [
        (100, 1024, "100 files × 1KB"),
        (500, 1024, "500 files × 1KB"),
        (1000, 1024, "1000 files × 1KB"),
        (100, 10240, "100 files × 10KB"),
        (100, 102400, "100 files × 100KB"),
        (50, 1048576, "50 files × 1MB"),
    ]

    for n_files, file_size, desc in test_cases:
        print(f"\n[Synthetic] {desc}")
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = pathlib.Path(temp_dir)
            create_corpus(temp_path, n_files, file_size)
            run_comparison(temp_path, iterations=3)

    print("\n" + "=" * 60)
    print("Benchmark complete")
    print("=" * 60)


if __name__ == "__main__":
    main()
