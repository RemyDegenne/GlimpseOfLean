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

/-- `ℝ[n]` is notation for `EuclideanSpace ℝ (Fin n)` -/
macro "ℝ[" n:term "]" : term => `(EuclideanSpace ℝ (Fin $n))
/-- `∂[i] f` is notation for the partial derivative of `f` with respect to the `i`-th variable -/
macro "∂[" i:term "]" : term => `(fun f x => fderiv ℝ f x (EuclideanSpace.single $i (1:ℝ)))
/-- `∇ f` is notation for the gradient of `f` -/
prefix:max " ∇ " => gradient
/-- `𝕕 f` is notation for the derivative of `f` -/
prefix:max " 𝕕 " => deriv

section Definitions

variable {𝕜 E G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 G] {U : Set E} {u : E → G} {x : E} {n : ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E G} -- ∀ n : ℕ, E[×n]→L[𝕜] G
  {F : FormalMultilinearSeries 𝕜 E G → E → G}

/-- A PDE has order at most `n` if its value on a function `u` at a point `x` depends only on
the derivatives of `u` at `x` up to order `n`. -/
structure IsOrder (n : ℕ) (F : FormalMultilinearSeries 𝕜 E G → E → G) : Prop where
  congr {p q : FormalMultilinearSeries 𝕜 E G} (hpq : ∀ m ≤ n, p m = q m) : F p = F q

structure IsClassicalSolution (F : FormalMultilinearSeries 𝕜 E G → E → G) (n : ℕ∞) (U : Set E)
    (u : E → G) : Prop where
  condDiffOn : ContDiffOn 𝕜 n u U
  eq_zero : ∀ x ∈ U, F (ftaylorSeriesWithin 𝕜 u U x) x = 0

end Definitions

section Real

variable {n : ℕ} {U : Set ℝ[n]} {u f g : ℝ[n] → ℝ} {x : ℝ[n]}
  {p : ℝ[n] → FormalMultilinearSeries ℝ ℝ[n] ℝ} {F : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ}

local notation "e" => stdOrthonormalBasis ℝ _

#check finrank_euclideanSpace_fin

def laplaceEquation (n : ℕ) : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ :=
  fun p _ ↦ ∑ i : Fin (finrank ℝ ℝ[n]), p 2 ![e i, e i]

#check laplacian

lemma isOrder_two_laplaceEquation : IsOrder 2 (laplaceEquation n) where
  congr {p q} hpq := by unfold laplaceEquation; rw [hpq 2 le_rfl]

lemma ContDiffOn.isClassicalSolution_laplaceEquation_iff (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) :
    IsClassicalSolution (laplaceEquation n) 2 U u ↔ ∀ x ∈ U, Δ u x = 0 := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have h_eq := h.eq_zero x hx
    simp only [laplaceEquation, ftaylorSeriesWithin] at h_eq
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    suffices iteratedFDerivWithin ℝ 2 u U x = iteratedFDeriv ℝ 2 u x by simpa [this] using h_eq
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn _ hx]
    exact h.condDiffOn.contDiffAt (hU.mem_nhds hx)
  · refine ⟨hu, fun x hx ↦ ?_⟩
    simp only [laplaceEquation, ftaylorSeriesWithin]
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis] at h
    suffices iteratedFDerivWithin ℝ 2 u U x = iteratedFDeriv ℝ 2 u x by simpa [this] using h x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn (hu.contDiffAt (hU.mem_nhds hx)) hx]

lemma isClassicalSolution_laplaceEquation_iff (hU : IsOpen U) :
    IsClassicalSolution (laplaceEquation n) 2 U u ↔ ContDiffOn ℝ 2 u U ∧ ∀ x ∈ U, Δ u x = 0 := by
  refine ⟨fun h ↦ ⟨h.condDiffOn, ?_⟩, fun ⟨hu, hΔ⟩ ↦ ?_⟩
  · rwa [← ContDiffOn.isClassicalSolution_laplaceEquation_iff hU h.condDiffOn]
  · rwa [ContDiffOn.isClassicalSolution_laplaceEquation_iff hU hu]

def poissonEquation (n : ℕ) (f : ℝ[n] → ℝ) : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ :=
  fun p x ↦ - ∑ i : Fin (finrank ℝ ℝ[n]), p 2 ![e i, e i] - f x

lemma ContDiffOn.isClassicalSolution_poissonEquation_iff (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) :
    IsClassicalSolution (poissonEquation n f) 2 U u ↔ ∀ x ∈ U, - Δ u x = f x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have h_eq := h.eq_zero x hx
    simp only [poissonEquation, ftaylorSeriesWithin] at h_eq
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp only
    rw [← sub_eq_zero]
    suffices iteratedFDerivWithin ℝ 2 u U x = iteratedFDeriv ℝ 2 u x by simpa [this] using h_eq
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn _ hx]
    exact h.condDiffOn.contDiffAt (hU.mem_nhds hx)
  · refine ⟨hu, fun x hx ↦ ?_⟩
    simp only [poissonEquation, ftaylorSeriesWithin]
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis] at h
    rw [sub_eq_zero]
    suffices iteratedFDerivWithin ℝ 2 u U x = iteratedFDeriv ℝ 2 u x by simpa [this] using h x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn (hu.contDiffAt (hU.mem_nhds hx)) hx]

end Real

end Tutorial
