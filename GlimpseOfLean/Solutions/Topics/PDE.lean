import GlimpseOfLean.Library.Basic
import Mathlib

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
noncomputable section

/-! # Differential calculus and Partial Differential Equations

-/

open Module InnerProductSpace EuclideanSpace
open scoped ContDiff

namespace Tutorial

section AbstractPDE

-- Let 𝕜 be a nontrivially normed field. (for example ℝ)
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
-- Let E, G be normed spaces over 𝕜.
variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]
-- Let `U` be a subset of `E`, `u` be a function from `E` to `G`, `x` be a point in `E`,
  {U : Set E} {u : E → G} {x : E}
-- Let `F` be a function that takes a formal multilinear series and a point in `E` and returns
-- a value in `G`. This is how we could represent a generic PDE.
  {F : FormalMultilinearSeries 𝕜 E G → E → G}

/-- A PDE has order at most `n` if its value on a function `u` at a point `x` depends only on
the derivatives of `u` at `x` up to order `n`. -/
structure IsOrder (n : ℕ) (F : FormalMultilinearSeries 𝕜 E G → E → G) : Prop where
  congr {p q : FormalMultilinearSeries 𝕜 E G} (hpq : ∀ m ≤ n, p m = q m) : F p = F q

/-- A function `u` is a classical solution of a PDE if it is sufficiently smooth and satisfies
the PDE at every point in the domain. -/
structure IsClassicalSolution (F : FormalMultilinearSeries 𝕜 E G → E → G) (n : ℕ∞) (U : Set E)
    (u : E → G) : Prop where
  condDiffOn : ContDiffOn 𝕜 n u U
  eq_zero : ∀ x ∈ U, F (ftaylorSeriesWithin 𝕜 u U x) x = 0

#check ContinuousMultilinearMap
#check FormalMultilinearSeries
#check iteratedFDerivWithin
#check ftaylorSeriesWithin
#check ContDiffOn

end AbstractPDE

section Real

/-- `ℝ[n]` is notation for `EuclideanSpace ℝ (Fin n)` -/
macro "ℝ[" n:term "]" : term => `(EuclideanSpace ℝ (Fin $n))
/-- Notation for the standard orthonormal basis of `ℝ[n]` -/
local notation "e" => stdOrthonormalBasis ℝ _

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} {U : Set ℝ[n]} {u f g : ℝ[n] → ℝ} {x : ℝ[n]}
  {p : ℝ[n] → FormalMultilinearSeries ℝ ℝ[n] ℝ} {F : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ}

#check finrank_euclideanSpace_fin

/-- The Laplace equation. -/
def laplaceEquation (n : ℕ) : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ :=
  fun p _ ↦ ∑ i : Fin (finrank ℝ ℝ[n]), p 2 ![e i, e i]

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

lemma isClassicalSolution_laplaceEquation_iff_harmonicOnNhd (hU : IsOpen U) :
    IsClassicalSolution (laplaceEquation n) 2 U u ↔ HarmonicOnNhd u U := by
  rw [isClassicalSolution_laplaceEquation_iff hU]
  refine ⟨fun ⟨hu, hΔ⟩ x hxU ↦ ?_, fun h ↦ ⟨fun x hxU ↦ ?_, fun x hxU ↦ ?_⟩⟩
  · refine ⟨ContDiffWithinAt.contDiffAt (s := U) (hu x hxU) (hU.mem_nhds hxU), ?_⟩
    rw [Filter.EventuallyEq, eventually_nhds_iff]
    exact ⟨U, hΔ, hU, hxU⟩
  · exact (h x hxU).1.contDiffWithinAt
  · exact Filter.EventuallyEq.eq_of_nhds (h x hxU).2

/-- The Poisson equation. -/
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

/-- The Heat equation using the abstract formalism. -/
def heatEquation (n : ℕ) : FormalMultilinearSeries ℝ ℝ[n+1] ℝ → ℝ[n+1] → ℝ :=
  fun p xt ↦ p 1 ![e ⟨n, by simp⟩]
    - ∑ i : Fin (finrank ℝ ℝ[n+1]) with i ≤ ⟨n, by simp⟩, p 2 ![e i, e i]

/-- A more direct (and practical?) definition of classical solutions to the heat equation. -/
def isClassicalHeatSolution (n : ℕ) (U : Set ℝ[n]) (u : ℝ[n] → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun xt : ℝ[n] × ℝ ↦ u xt.1 xt.2) (U ×ˢ Set.Ici 0)
    ∧ ∀ x ∈ U, ∀ t, 0 ≤ t → deriv (fun s ↦ u x s) t - Δ (fun y ↦ u y t) x = 0

end Real

section LowDimensional

example (y : ℝ → ℝ) (ydiff : Differentiable ℝ y) (hy : deriv y = y) :
    ∃ C, y = fun x ↦ C * Real.exp x := by
  use y 0
  let g : ℝ → ℝ := y * fun x ↦ Real.exp (-x)
  have diffg : Differentiable ℝ g := by fun_prop
  have hg : deriv g = deriv y * (fun x ↦ Real.exp (-x)) + y * (fun x ↦ - Real.exp (-x)) := by
    ext x
    unfold g
    rw [deriv_mul]
    congr
    · change deriv (Real.exp ∘ fun x => (-x)) x = _
      rw [deriv_comp]
      simp only [Real.deriv_exp, deriv_neg'', mul_neg, mul_one]
      · fun_prop
      · fun_prop
    · exact ydiff.differentiableAt
    · fun_prop
  have hg' : deriv g = 0 := by
    rw [hy] at hg
    ext x
    simp [g, hg]
  have fact : ∀ x u, g x = g u := is_const_of_deriv_eq_zero (f := g) diffg (by simp [hg'])
  have g0 : g 0 = y 0 := by simp [g]
  have fact' (x) : g x = g 0 := fact x 0
  rw [g0] at fact'
  unfold g at fact'
  ext x
  specialize fact' x
  rw [← fact']
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← Real.exp_add]
  simp

example {x y : ℝ} : deriv (fun x : ℝ ↦ x ^ 2 + y ^ 2) x = 2 * x := by
 simp

end LowDimensional

/-- `∂[i] f` is notation for the partial derivative of `f` with respect to the `i`-th variable -/
macro "∂[" i:term "]" : term => `(fun f x => fderiv ℝ f x (EuclideanSpace.single $i (1:ℝ)))
/-- `∇ f` is notation for the gradient of `f` -/
prefix:max " ∇ " => gradient
/-- `𝕕 f` is notation for the derivative of `f` -/
prefix:max " 𝕕 " => deriv

end Tutorial
