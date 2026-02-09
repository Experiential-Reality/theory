import Lake
open Lake DSL

package bld where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib BLD where
  roots := #[`BLD]
