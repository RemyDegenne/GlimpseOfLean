import GlimpseOfLean.Library.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
noncomputable section

/-! # Partial Differential Equations

-/

open Module InnerProductSpace
open scoped ContDiff

namespace Tutorial

#check ContinuousMultilinearMap
#check FormalMultilinearSeries
#check iteratedFDerivWithin
#check ftaylorSeriesWithin
#check ContDiffOn

macro "ℝ[" n:term "]" : term => `(EuclideanSpace ℝ (Fin $n))
macro "∂[" i:term "]" : term => `(fun f x => fderiv ℝ f x (EuclideanSpace.single $i (1:ℝ)))
prefix:max " ∇ " => gradient
prefix:max " 𝕕 " => deriv

section Definitions

variable {𝕜 E G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 G] {U : Set E} {f : E → G} {x : E} {n : ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E G} -- ∀ n : ℕ, E[×n]→L[𝕜] G
  {F : FormalMultilinearSeries 𝕜 E G → E → G}

/-- A PDE has order at most `n` if its value on a function `f` at a point `x` depends only on
the derivatives of `f` at `x` up to order `n`. -/
structure IsOrder (n : ℕ) (F : FormalMultilinearSeries 𝕜 E G → E → G) : Prop where
  congr {p q : FormalMultilinearSeries 𝕜 E G} (hpq : ∀ m ≤ n, p m = q m) : F p = F q

structure IsClassicalSolution (F : FormalMultilinearSeries 𝕜 E G → E → G) (n : ℕ∞) (U : Set E)
    (f : E → G) : Prop where
  condDiffOn : ContDiffOn 𝕜 n f U
  eq_zero : ∀ x ∈ U, F (ftaylorSeriesWithin 𝕜 f U x) x = 0

end Definitions

section Real

variable {n : ℕ}
  {U : Set ℝ[n]} {f : ℝ[n] → ℝ} {x : ℝ[n]}
  {p : ℝ[n] → FormalMultilinearSeries ℝ ℝ[n] ℝ}
  {F : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ}

local notation "e(" n ") " => stdOrthonormalBasis ℝ ℝ[n]

#check finrank_euclideanSpace_fin

def laplaceEquation (n : ℕ) : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ := fun p _ ↦
  ∑ i : Fin (finrank ℝ ℝ[n]), p 2 ![e(n) i, e(n) i]

#check laplacian

lemma isOrder_laplaceEquation : IsOrder 2 (laplaceEquation n) where
  congr {p q} hpq := by unfold laplaceEquation; rw [hpq 2 le_rfl]

lemma ContDiffOn.isClassicalSolution_laplaceEquation_iff (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    IsClassicalSolution (laplaceEquation n) 2 U f ↔ ∀ x ∈ U, Δ f x = 0 := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have h_eq := h.eq_zero x hx
    simp only [laplaceEquation, ftaylorSeriesWithin] at h_eq
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    suffices iteratedFDerivWithin ℝ 2 f U x = iteratedFDeriv ℝ 2 f x by simpa [this] using h_eq
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn _ hx]
    exact h.condDiffOn.contDiffAt (hU.mem_nhds hx)
  · refine ⟨hf, fun x hx ↦ ?_⟩
    simp only [laplaceEquation, ftaylorSeriesWithin]
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis] at h
    suffices iteratedFDerivWithin ℝ 2 f U x = iteratedFDeriv ℝ 2 f x by simpa [this] using h x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn (hf.contDiffAt (hU.mem_nhds hx)) hx]

lemma isClassicalSolution_laplaceEquation_iff (hU : IsOpen U) :
    IsClassicalSolution (laplaceEquation n) 2 U f ↔ ContDiffOn ℝ 2 f U ∧ ∀ x ∈ U, Δ f x = 0 := by
  refine ⟨fun h ↦ ⟨h.condDiffOn, ?_⟩, fun ⟨hf, hΔ⟩ ↦ ?_⟩
  · rwa [← ContDiffOn.isClassicalSolution_laplaceEquation_iff hU h.condDiffOn]
  · rwa [ContDiffOn.isClassicalSolution_laplaceEquation_iff hU hf]

end Real

end Tutorial
