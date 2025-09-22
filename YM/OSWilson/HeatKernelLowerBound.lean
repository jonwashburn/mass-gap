import YM.RealityAdapters

/-!
Interface constants for the explicit Doeblin/heat‑kernel minorization used by
the OS/Wilson lattice derivations. This file intentionally avoids any geometric
or analytic placeholders and only exposes the concrete `(θ_*, t₀)` interface
consumed by downstream modules.
-/

namespace YM.OSWilson.HeatKernelLowerBound

noncomputable section

/-!
Interface/Doeblin parameters `(θ_*, t₀)` are provided by `YM.RealityAdapters`.
We re-export the interface to ensure all constants are threaded from there.
-/
abbrev InterfaceParams := YM.RealityAdapters.InterfaceParams

noncomputable def defaultParams : InterfaceParams := YM.RealityAdapters.defaultParams

end -- noncomputable section

end YM.OSWilson.HeatKernelLowerBound


