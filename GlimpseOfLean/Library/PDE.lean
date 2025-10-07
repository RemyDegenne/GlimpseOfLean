import Mathlib

-- missing from Mathlib (we have Fin0 and Fin1)
noncomputable
def continuousMultilinearCurryFin2 (𝕜 : Type*) (G : Type*) (G' : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] :
    ContinuousMultilinearMap 𝕜 (fun i : Fin 2 ↦ G) G' →ₗᵢ[𝕜] G →L[𝕜] G →L[𝕜] G' :=
  let b := continuousMultilinearCurryLeftEquiv 𝕜 (n := 1) (fun _ ↦ G) G'
  let a := continuousMultilinearCurryFin1 𝕜 G G'
  (a.toLinearIsometry.postcomp (E := G)).comp b.toLinearIsometry
