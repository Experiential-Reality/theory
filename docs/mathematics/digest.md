---
status: REFERENCE
layer: meta
key_result: "Complete formula catalog — all BLD predictions in one file"
depends_on: [foundations/constants.md, foundations/key-formulas.md, STRUCTURE.md]
---

# BLD Theory: Mathematical Digest

Self-contained formula reference. Values cross-checked against markdown derivations, Lean proofs, and `tools/src/tools/bld.py`.
Zero free parameters — structural constants derived from axioms; reference scale v fixed by one measurement.

---

## 1. The Five Constants

| Sym | Value | Derivation | Key Identity |
|-----|-------|------------|-------------|
| **B** | 56 | 2 × dim(Spin(8)) = 2 × 28 | B = n(S + 1) |
| **L** | 20 | Riemann components: n²(n²−1)/12 | L = n²(n²−1)/12 |
| **n** | 4 | sl(2,ℂ) ⊂ sl(2,𝕆) reference fixing | K² = n |
| **K** | 2 | Killing form, bidirectional observation | K = 2 (unique giving α⁻¹ = 137) |
| **S** | 13 | Structural intervals: (B−n)/n | S = K² + (n−1)² |

Auxiliary:

| Sym | Value | Definition |
|-----|-------|------------|
| λ | 1/√20 ≈ 0.2236 | 1/√L (cascade coupling scale) |
| λ² | 1/20 = 0.05 | 1/L |
| v | 246.2196 GeV | Electroweak VEV (reference scale) |
| e | 2.71828... | Euler's number; emerges as lim(1+1/m)^m |

**The primordial identity:** α⁻¹(integer) = n×L + B + 1 = 80 + 56 + 1 = **137**

---

## 2. Composite Dictionary

All structurally meaningful BLD combinations. Matches `bld_composites()` in bld.py.

| Expression | Value | Where It Appears |
|------------|-------|------------------|
| n×L | 80 | α⁻¹ base, m_e correction, observer geometry |
| n×S | 52 | quark mass structure |
| n×B | 224 | flat plate Reynolds scaling |
| B×L | 1120 | Higgs 2nd-order correction denominator |
| n×L×S | 1040 | μ/e coupling correction |
| n×L×B | 4480 | sin²θ_W correction, weak coupling X |
| n×L×B² | 250880 | μ/e 3rd-order correction |
| n+L | 24 | strong coupling X, Hubble tension X |
| n+K | 6 | Feigenbaum intermediate |
| B+L | 76 | κ_W detection X, muon g-2 detection |
| B+K | 58 | — |
| n×L+B | 136 | structure without observer |
| n×L+B+1 | 137 | α⁻¹ integer part |
| S+1 | 14 | = B/n = dim(G₂) |
| S+n | 17 | τ/μ primordial, p/e generation base |
| S−1 | 12 | d/u interval correction |
| B−L | 36 | Reynolds base |
| B−L+1 | 37 | Reynolds correction denominator |
| B² | 3136 | Z mass correction |
| n² | 16 | α_s scaling |
| (n×L)² | 6400 | muon g-2 base, μ/e 2nd-order |
| n²×S | 208 | μ/e primordial, generation structure |
| n²×S−1 | 207 | μ/e phase-subtracted primordial |
| (n×L)²+n×S | 6452 | μ/e and W mass 2nd-order X |
| L+n+1 | 25 | θ₂₃ denominator, intermittency |
| B+n×S | 108 | proton confinement depth |
| (S+n)(B+n×S) | 1836 | p/e primordial |
| n+L+K | 26 | = B/2−K, Planck cascade exponent |
| B+L−K×n | 68 | Hubble cascade exponent |
| n(n−1)/2 | 6 | Lorentz dim, baryon asymmetry exponent |

K/X ratios (the correction terms):

| K/X | Value | Correction Type |
|-----|-------|-----------------|
| K/B | 2/56 ≈ 0.0357 | Boundary quantum (EM) |
| K/(n×L) | 2/80 = 0.025 | Geometric (Higgs self-coupling) |
| K/(n+L) | 2/24 ≈ 0.0833 | Strong coupling |
| K/(n×L×B) | 2/4480 ≈ 0.000446 | Weak mixing |
| K/(n×L−K) | 2/78 ≈ 0.0256 | Gravity (embedded) |
| K/S² | 2/169 ≈ 0.01183 | Neutron beam lifetime |

---

## 3. Derivation DAG

```
"Nothing" is self-contradictory
    │
    ▼
B must exist (primordial distinction)
    │
    ▼
traverse(−B, B) must CLOSE
    │
    ├── Closure requires division property ──► Hurwitz: only ℝ,ℂ,ℍ,𝕆
    ├── Closure requires B = 56 (richness) ──► Only Aut(𝕆) = G₂ suffices
    │
    ▼
OCTONIONS REQUIRED
    │
    ├── G₂ → fix reference → SU(3) ─────── color (strong force)
    ├── so(9,1) → so(3,1) ──────────────── n = 4 (spacetime)
    ├── Spin(8) triality ────────────────── 3 generations
    ├── 2 × dim(so(8)) = 56 ────────────── B = 56
    ├── n²(n²−1)/12 = 20 ──────────────── L = 20
    ├── Killing form bidirectional ──────── K = 2
    └── (B−n)/n = 13 ───────────────────── S = 13
         │
         ▼
    BLD Calculus + Lie Correspondence
         │
         ├── Integer Machine (primordial structure = integers)
         ├── Two-Reference Principle (observed = integer + K/X)
         └── Equation of Motion (geodesics on SO(8))
              │
              ▼
         ALL PREDICTIONS
```

---

## 4. K/X Correction Framework

**Universal pattern:** Observed = Primordial × ∏(1 ± K/Xᵢ)

| Sign | Meaning | When |
|------|---------|------|
| **+** | Incomplete traversal — something escapes detection | EM, weak |
| **−** | Complete traversal — all products detected | Strong, confined |
| **×** | Embedded observer — multiplicative correction | Gravity |

| Force | Carrier | Detection X | K/X | Sign |
|-------|---------|-------------|-----|------|
| EM | photon | B = 56 | 0.0357 | + (boundary crossing) |
| Weak | Z/W | n×L×B = 4480 | 0.00045 | + (full structure) |
| Strong | gluon | n+L = 24 | 0.0833 | − (confined, complete) |
| Gravity | metric | n×L−K = 78 | 0.0256 | × (embedded observer) |

---

## 5. Force Couplings

### Fine structure constant α⁻¹  [→ bld.py:247]

```
α⁻¹ = nL + B + 1 + K/B + n/((n−1)·nL·B) − (n−1)/((nL)²·B) − 1/(nL·B²) − e²(2B+n+K+2)/((2B+n+K+1)·(nL)²·B²)
```

| Term | Expression | Value |
|------|------------|-------|
| base | n×L + B + 1 | 137 |
| boundary quantum | +K/B | +0.035714 |
| outbound spatial | +n/((n−1)·nL·B) | +0.000298 |
| return spatial | −(n−1)/((nL)²·B) | −0.0000084 |
| return boundary | −1/(nL·B²) | −0.0000040 |
| accumulated | −e²·120/(119·(nL)²·B²) | −0.00000037 |
| **total** | | **137.035999177** |

Observed: 137.035999177 ± 0.000000021 (CODATA 2022). **Match.**

### Weak mixing angle sin²θ_W  [→ bld.py:401]

```
sin²θ_W = 3/S + K/(n·L·B) = 3/13 + 2/4480 = 0.23122
```

Observed: 0.23121 ± 0.00004 (PDG 2024). 0.2σ.

### Strong coupling α_s  [→ bld.py:428]

```
α_s⁻¹ = α⁻¹/n² − K/(n+L) = 137.036/16 − 2/24 = 8.481
```

Predicted α_s = 0.1179. Observed: 0.1179 ± 0.0010 (PDG 2024). 0.0σ.

---

## 6. Lepton Masses

### Muon/electron ratio  [→ bld.py:311]

```
μ/e = (n²S − 1) · nLS/(nLS + 1) · (1 − 1/((nL)² + nS)) · (1 − 1/(nL·B²)) · (1 + e²(S+1)/((nL)²·B²·S²))
    = 207 × 1040/1041 × 6451/6452 × 250879/250880 × (1 + 3.05×10⁻⁸)
    = 206.7682826
```

Observed: 206.7682827 ± 0.0000005 (CODATA 2022). 0.5 ppb.

### Tau/muon ratio  [→ bld.py:336]

```
τ/μ = 2πe · (n²S − 1)/(n²S) · (nL − 1)/(nL) · (1 + 2/(nLS))
    = 17.079 × 207/208 × 79/80 × 1042/1040
    = 16.81716
```

Observed: 16.81709 ± 0.0012. 4 ppm.

### Primordial integers

| Ratio | Primordial | Mode | Observed |
|-------|------------|------|----------|
| μ/e | n²S = 208 | Discrete (e-type) | 206.768 |
| τ/μ | S+n = 17 | Rotational (π-type, 2πe ≈ 17.08) | 16.817 |

---

## 7. Quark Masses

All ratios from BLD constants. Anchor: m_e = 0.511 MeV.  [→ bld.py:1707–1753]

| Quark | Ratio Formula | Ratio Value | Predicted | Observed | Err |
|-------|---------------|-------------|-----------|----------|-----|
| s | m_s/m_e = n²S − L − L/n | 183 | 93.5 MeV | 93.4 ± 8.6 | 0.1% |
| d | m_s/m_d = L + K/L | 20.1 | 4.65 MeV | 4.67 ± 0.48 | 0.4% |
| u | m_d/m_u = K·S/(S−1) | 2.167 | 2.16 MeV | 2.16 ± 0.49 | 0.0% |
| c | m_c/m_s = S + K/3 | 13.667 | 1276 MeV | 1270 ± 20 | 0.5% |
| b | m_b/m_c = 3 + K/(n+3) | 3.286 | 4193 MeV | 4180 ± 30 | 0.3% |
| t | m_t = v/√K · (1 − K/(n²S)) | — | 172.4 GeV | 172.69 ± 0.30 | 0.17% |

Top quark exception: decays before confining → couples directly to v/√K.

---

## 8. Boson Masses

### Higgs  [→ bld.py:289]

```
m_H = (v/2) · (1 + 1/B) · (1 − 1/(B·L))
    = 123.11 × 57/56 × 1119/1120
    = 125.20 GeV
```

Observed: 125.20 ± 0.11 GeV. **0.0σ.**

### Z boson  [→ bld.py:409]

```
m_Z = (v/e) · (137/136) · (1 − K/B²)
    = 90.58 × 1.00735 × 0.999362
    = 91.187 GeV
```

Observed: 91.1876 ± 0.0021 GeV. 0.3σ.

### W boson  [→ bld.py:418]

```
m_W = m_Z · √((S−3)/S) · (n²S + 1)/(n²S) · (1 + 1/((nL)² + nS))
    = 91.187 × √(10/13) × 209/208 × 6453/6452
    = 80.373 GeV
```

Observed: 80.377 ± 0.012 GeV. 0.3σ.

Note: W and muon share the same structures (208, 6452) with opposite signs.

---

## 9. Nucleon Mass

[→ bld.py:328]

```
m_p/m_e = (S + n)(B + nS) + K/S = 17 × 108 + 2/13 = 1836.154
```

Observed: 1836.15267 ± 0.00085 (CODATA 2022). 0.6 ppm.

---

## 10. Neutrino Sector

### PMNS mixing angles  [→ bld.py:351–372]

| Angle | Formula | Value | Observed | σ |
|-------|---------|-------|----------|---|
| sin²θ₁₂ | K²/S | 4/13 = 0.3077 | 0.307 ± 0.012 | 0.06 |
| sin²θ₁₃ | n²/(n−1)⁶ | 16/729 = 0.02195 | 0.02195 ± 0.00058 | 0.00 |
| sin²θ₂₃ | (S+1)/(L+n+1) | 14/25 = 0.560 | 0.561 ± 0.015 | 0.07 |

### CKM Cabibbo angle  [→ bld.py:1791]

```
|V_us| = sin(arctan((n−1)/S)) = sin(arctan(3/13)) = 0.2249
```

Observed: 0.2243 ± 0.0005. 1.2σ.

### Neutrino mass  [→ neutrino-masses.md]

```
m_νe = m_e · (K/B)² · K/(n·L) · (1 + K/(nL·B)) ≈ 16 meV
```

Consistent with KATRIN bound < 0.8 eV. Prediction: **normal ordering** (m₁ < m₂ < m₃).

### Mass-squared difference ratio  [→ bld.py:1778]

```
|Δm²₃₂|/|Δm²₂₁| = L + S = 33
```

Observed: 2.453×10⁻³/7.53×10⁻⁵ = 32.6 ± 1.0. 0.4σ.

---

## 11. Anomalous Measurements

### Muon g−2  [→ bld.py:375]

```
Δa_μ = α² · K²/((nL)²·S) · (B+L)/(B+L+K) × 10¹¹
     = (1/137.036)² × 4/(6400·13) × 76/78 × 10¹¹
     ≈ 250 × 10⁻¹¹
```

Observed: 249 ± 17 × 10⁻¹¹ (Fermilab). 0.06σ.

### Neutron beam lifetime  [→ bld.py:388]

```
τ_beam = τ_bottle · (1 + K/S²) = 877.8 × (1 + 2/169) = 888.2 s
```

Observed: 888.1 ± 2.0 s (PDG 2024). 0.05σ.

---

## 12. Higgs Couplings

Pattern: κ = 1 + K/X where X is the detection structure.  [→ bld.py:436–469]

| Channel | X | κ predicted | Observed |
|---------|---|-------------|----------|
| γ, Z (EM) | B = 56 | 1 + 2/56 = 1.036 | 1.05 ± 0.09 |
| b, c (hadronic) | n+L = 24 | 1 + 2/24 = 1.083 | 0.98 ± 0.13 |
| W | B+L = 76 | 1 + 2/76 = 1.026 | 1.04 ± 0.08 |
| λ (self-coupling) | n×L = 80 | 1 + 2/80 = **1.025** | [−1.6, 6.6] |

**Testable prediction:** κ_λ = 1.025 (HL-LHC, ~2040, ~5% precision).

---

## 13. Planck Scale / Gravity

[→ bld.py:297]

```
M_P = v · (λ²)⁻¹³ · √(5/14) · (nL−K+1)/(nL−K) · (1 + K·3/(nL·B²))
    = v · 20¹³ · √(5/14) · 79/78 · (1 + 6/250880)
    = 1.22089 × 10¹⁹ GeV
```

Where: exponent 13 on λ² gives effective √L exponent 26 = B/2 − K = n + L + K.

Observed: 1.22091 × 10¹⁹ ± 10¹⁶ GeV. 0.002%.

Einstein coupling: 8πG = K·n·π = 8π.  [→ bld.py:einstein_coupling]

---

## 14. Cosmology

### Energy budget  [→ bld.py:1606–1622]

Input: baryon fraction x = 1/L = 0.05.

| Component | Formula | Predicted | Observed |
|-----------|---------|-----------|----------|
| Ordinary matter | x = 1/L | 5.0% | 4.9 ± 0.1% |
| Dark matter | (L/n)·x + K·n·x² | 27.0% | 27 ± 1% |
| Dark energy | 1 − (1+L/n)·x − K·n·x² | 68.0% | 68 ± 1% |

### Hubble tension  [→ bld.py:1625, 1674]

```
H₀(CMB) = v · λ⁶⁸  (in natural units, converted)     = 67.2 km/s/Mpc
H₀(local) = H₀(CMB) · (1 + K/(n+L)) = H₀ × 13/12    = 72.8 km/s/Mpc
```

Cascade exponent: 68 = B + L − K·n.

CMB observed: 67.4 ± 0.5. Local observed: 73.0 ± 1.0.

### σ₈ tension  [→ bld.py:1635–1659]

```
σ₈(primordial) = L/(n+L)                    = 20/24 = 5/6 ≈ 0.833
σ₈(CMB)        = σ₈(prim) · (1 − K/(nL))   = (5/6)(78/80) = 13/16 = 0.8125
σ₈(local)      = σ₈(CMB) · (1 − K/(2L))    = (13/16)(19/20) = 247/320 ≈ 0.772
```

CMB observed: 0.811 ± 0.006. Local observed: 0.77 ± 0.02.

### Baryon asymmetry  [→ bld.py:1662]

```
η = (K/B) · (1/L)⁶ · S/(S−1) = (2/56) · (1/20)⁶ · 13/12 = 6.045 × 10⁻¹⁰
```

Where exponent 6 = n(n−1)/2 = dim(SO(3,1)).

Observed: 6.104 ± 0.058 × 10⁻¹⁰ (Planck 2018). 1.0σ.

---

## 15. Classical Physics / Turbulence

### Reynolds numbers  [→ bld.py:1537–1597]

| Geometry | Formula | Predicted | Observed |
|----------|---------|-----------|----------|
| Pipe | (nLB/K)·(B−L+2)/(B−L+1) = 2240·38/37 | 2300.5 | 2300 ± 1 |
| Flat plate | Re_pipe · n·B | 515,300 | 5×10⁵ ± 1.5×10⁴ |
| Sphere | Re_pipe · (n(L+K) − 1) | 200,100 | 2×10⁵ ± 10³ |
| Jet | Re_pipe / K | 1150 | 2000 ± 1000 |

### Kolmogorov exponent

```
−5/3 = −L/(n(n−1)) = −20/12     (exact rational)
```

### Intermittency correction

```
μ = 1/(L+n+1) = 1/25 = 0.04     (exact rational)
```

### She-Leveque structure functions  [→ bld.py:1565]

```
ζ_p = p/(n−1)² + K·(1 − (K/(n−1))^(p/(n−1)))
    = p/9 + 2·(1 − (2/3)^(p/3))
```

| p | Predicted | DNS data |
|---|-----------|----------|
| 1 | 0.364 | 0.37 ± 0.01 |
| 2 | 0.696 | 0.70 ± 0.01 |
| 3 | 1.000 | 1.000 ± 0.001 |
| 4 | 1.280 | 1.28 ± 0.02 |
| 5 | 1.538 | 1.54 ± 0.03 |
| 6 | 1.778 | 1.78 ± 0.04 |
| 7 | 2.001 | 2.00 ± 0.05 |
| 8 | 2.211 | 2.21 ± 0.07 |

### Feigenbaum constants  [→ bld.py:1546, 1555]

Intermediate: X = n + K + K/n + 1/L = 4 + 2 + 0.5 + 0.05 = 6.55

```
δ = √(L + K − K²/L + 1/eˣ) = √(20 + 2 − 0.2 + 0.00143) = 4.66920
α = K + 1/K + 1/((n+K)·B) − 1/((L+1−1/n²)·eˣ) = 2.50291
```

| Constant | Predicted | Observed | Accuracy |
|----------|-----------|----------|----------|
| δ | 4.66920 | 4.6692016091 ± 10⁻¹⁰ | 0.00003% |
| α | 2.50291 | 2.5029078750 ± 10⁻¹⁰ | 0.0000005% |

---

## 16. BLD Type System

| Constructor | Type Theory | BLD Primitive |
|-------------|-------------|---------------|
| Sum (τ₁ + τ₂) | Coproduct | **B** (Boundary) — partition |
| Function (τ₁ → τ₂) | Exponential | **L** (Link) — connection |
| Product (Πₙτ) | n-fold product | **D** (Dimension) — repetition |

**Mode count** (distinct from cardinality — linear in n, not exponential):

```
μ(1) = 1
μ(τ₁ + τ₂) = μ(τ₁) + μ(τ₂)
μ(τ₁ → τ₂) = μ(τ₂)^μ(τ₁)
μ(Πₙ τ) = n × μ(τ)            ← KEY: n×, not ^n
```

**α⁻¹ as type-level mode count:**

```
τ_geom  = Π₄(Π₂₀ 1)    →  μ = 4 × 20 = 80
τ_bound = Σ₅₆ 1          →  μ = 56
τ_trav  = 1               →  μ = 1
                              total = 137     [Lean: verified]
```

---

## 17. Integer Machine

Primordial structure stores integers. Continuous values emerge from K/X observation.

| Quantity | Primordial Integer | Expression | Observed | Gap |
|----------|--------------------|------------|----------|-----|
| α⁻¹ | 137 | nL + B + 1 | 137.036 | +K/B + spatial |
| μ/e | 208 | n²S | 206.768 | −1 phase, K/X cascade |
| τ/μ | 17 | S + n | 16.817 ≈ 2πe | Continuous limit |
| p/e | 1836 | (S+n)(B+nS) | 1836.153 | +K/S |
| m_s/m_e | 183 | n²S − L − L/n | ~183 | Phase transition |

Rule: 2πe ≈ 17.079 is the continuous limit of the integer 17.
e = lim(1 + 1/m)^m is the discrete → continuous boundary.

---

## 18. Force Geometry

### Division algebra tower

```
ℝ (1D) → ℂ (2D) → ℍ (4D) → 𝕆 (8D)
 │         │         │         │
 ▼         ▼         ▼         ▼
metric   U(1)     SU(2)     SU(3)
gravity   EM       weak     strong
```

| Algebra | Aut(A) | dim(Aut) | Gauge group | Generators |
|---------|--------|----------|-------------|------------|
| 𝕆 | G₂ | 14 | SU(3) (fix ref) | 8 |
| ℍ | SO(3) | 3 | SU(2) | 3 |
| ℂ | ℤ₂ | 0 | U(1) | 1 |

Gauge total: 8 + 3 + 1 = 12 of 28 generators in so(8).
Complement: 28 − 12 = 16 (matter + gravity degrees of freedom).

---

## 19. Complete Prediction Catalog

| # | Quantity | Formula Ref | Predicted | Observed | Error |
|---|----------|-------------|-----------|----------|-------|
| 1 | α⁻¹ | §5 | 137.035999177 | 137.035999177 | match |
| 2 | sin²θ_W | §5 | 0.23122 | 0.23121 ± 0.00004 | 0.2σ |
| 3 | α_s | §5 | 0.1179 | 0.1179 ± 0.0010 | 0.0σ |
| 4 | μ/e | §6 | 206.7682826 | 206.7682827 ± 5×10⁻⁷ | 0.2σ |
| 5 | τ/μ | §6 | 16.81716 | 16.81709 ± 0.0012 | 0.06σ |
| 6 | m_s/m_e | §7 | 183 | 182.8 ± 16.8 | 0.01σ |
| 7 | m_s/m_d | §7 | 20.1 | 20.0 ± 2.5 | 0.04σ |
| 8 | m_d/m_u | §7 | 2.167 | 2.16 ± 0.5 | 0.01σ |
| 9 | m_c/m_s | §7 | 13.667 | 13.6 ± 1.5 | 0.04σ |
| 10 | m_b/m_c | §7 | 3.286 | 3.29 ± 0.1 | 0.04σ |
| 11 | m_t | §7 | 172.4 GeV | 172.69 ± 0.30 | 0.9σ |
| 12 | m_H | §8 | 125.20 GeV | 125.20 ± 0.11 | 0.0σ |
| 13 | m_Z | §8 | 91.187 GeV | 91.1876 ± 0.0021 | 0.3σ |
| 14 | m_W | §8 | 80.373 GeV | 80.377 ± 0.012 | 0.3σ |
| 15 | m_p/m_e | §9 | 1836.154 | 1836.15267 ± 0.00085 | 1.4σ |
| 16 | sin²θ₁₂ | §10 | 0.3077 | 0.307 ± 0.012 | 0.06σ |
| 17 | sin²θ₁₃ | §10 | 0.02195 | 0.02195 ± 0.00058 | 0.00σ |
| 18 | sin²θ₂₃ | §10 | 0.560 | 0.561 ± 0.015 | 0.07σ |
| 19 | \|V_us\| | §10 | 0.2249 | 0.2243 ± 0.0005 | 1.2σ |
| 20 | Δm²₃₂/Δm²₂₁ | §10 | 33 | 32.6 ± 1.0 | 0.4σ |
| 21 | Δa_μ | §11 | 250×10⁻¹¹ | 249 ± 17 | 0.06σ |
| 22 | τ_beam | §11 | 888.2 s | 888.1 ± 2.0 | 0.05σ |
| 23 | κ_γ | §12 | 1.036 | 1.05 ± 0.09 | 0.2σ |
| 24 | κ_λ | §12 | **1.025** | [−1.6, 6.6] | **PREDICTED** |
| 25 | M_P | §13 | 1.221×10¹⁹ | 1.221×10¹⁹ | 0.002% |
| 26 | Ω_b | §14 | 5.0% | 4.9 ± 0.1% | 1.0σ |
| 27 | Ω_DM | §14 | 27.0% | 27 ± 1% | 0.0σ |
| 28 | Ω_Λ | §14 | 68.0% | 68 ± 1% | 0.0σ |
| 29 | H₀(CMB) | §14 | 67.2 | 67.4 ± 0.5 | 0.4σ |
| 30 | H₀(local) | §14 | 72.8 | 73.0 ± 1.0 | 0.2σ |
| 31 | σ₈(CMB) | §14 | 0.8125 | 0.811 ± 0.006 | 0.3σ |
| 32 | η_baryon | §14 | 6.045×10⁻¹⁰ | 6.104 ± 0.058 | 1.0σ |
| 33 | Re_pipe | §15 | 2300.5 | 2300 ± 1 | 0.5σ |
| 34 | Kolmogorov | §15 | −5/3 | −5/3 | exact |
| 35 | ζ_p (p=3) | §15 | 1.000 | 1.000 ± 0.001 | 0σ |
| 36 | δ_Feig | §15 | 4.66920 | 4.66920161 | 0.00003% |
| 37 | α_Feig | §15 | 2.50291 | 2.50290788 | 5×10⁻⁷% |
| 38 | m_νe | §10 | ~16 meV | < 800 meV | **PREDICTED** |
| 39 | mass ordering | §10 | NORMAL | TBD (JUNO) | **PREDICTED** |

---

## 20. Structural Identities

```
K² = n                                  4 = 4
S = K² + (n−1)²                         4 + 9 = 13
S + 1 = B/n = dim(G₂)                   14 = 56/4 = 14
B = n(S + 1)                            4 × 14 = 56
n + L + K = B/2 − K = 26                26 = 26  (Planck cascade)
B + L − Kn = 68                         (Hubble cascade)
n²S − 1 = 207                           (μ/e primordial after phase)
(S + n)(B + nS) = 1836                  (p/e primordial)
(B−L+2)/(B−L+1) = 38/37                (Reynolds correction)
n(n−1)/2 = 6                            (Lorentz dim, baryon exponent)
λ²·(nL) = (1/20)·80 = 4 = K² = n      (coupling × geometry = observation)
```

---

## Source Files

| Section | Primary source |
|---------|---------------|
| Constants | bld.py:24–29, constants.md |
| Composites | bld.py:472–501 |
| DAG | STRUCTURE.md |
| α⁻¹ | bld.py:247–277, fine-structure-consistency.md |
| Leptons | bld.py:311–348, lepton-masses.md |
| Quarks | bld.py:1707–1753, quark-masses.md |
| Bosons | bld.py:289–425, boson-masses.md |
| Neutrinos | bld.py:351–372, 1761–1796, neutrino-mixing.md |
| Anomalous | bld.py:375–393 |
| Higgs κ | bld.py:436–469, higgs-couplings.md |
| Planck | bld.py:297–308, planck-derivation.md |
| Cosmology | bld.py:1606–1699 |
| Turbulence | bld.py:1537–1597 |
| Type system | bld-calculus.md, lean/BLD/ |
