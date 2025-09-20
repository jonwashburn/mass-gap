import Lake
open Lake DSL

-- Configure the Lean toolchain
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0-rc1"

package ymPlus where
  -- Lean compiler options
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Main library combining RS and YM
lean_lib YMPlus where
  roots := #[`YMPlus]

-- RS Framework (Recognition Science)
lean_lib RSFramework where
  roots := #[`RSFramework]

-- YM Framework (Yang-Mills)
lean_lib YMFramework where  
  roots := #[`YMFramework]

-- Unified proof
lean_lib UnifiedProof where
  roots := #[`UnifiedProof]

-- Executable for verification
lean_exe verify where
  root := `Main
