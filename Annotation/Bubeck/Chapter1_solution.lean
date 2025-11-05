import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

open InnerProductSpace

-- Separation Theorem
theorem separation_theorem {n : ℕ} (𝒳 : Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n)) (h_closed : IsClosed 𝒳) (h_convex : Convex ℝ 𝒳)
    (h_notin : x₀ ∉ 𝒳) :
  ∃ (w : EuclideanSpace ℝ (Fin n)) (t : ℝ),
    (⟪w, x₀⟫_ℝ < t) ∧ (∀ x ∈ 𝒳, t ≤ ⟪w, x⟫_ℝ) := by
  classical
  -- Apply geometric Hahn–Banach separation for a point and a closed convex set
  obtain ⟨f, t, hlt, hle⟩ :=
    geometric_hahn_banach_point_closed (E := EuclideanSpace ℝ (Fin n))
      h_convex h_closed h_notin
  -- Use the Riesz representation to identify the functional with an inner product by some vector w
  refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f, t, ?_, ?_⟩
  · -- Left strict inequality
    simpa [InnerProductSpace.toDual_symm_apply] using hlt
  · -- Right non-strict inequality for all x ∈ 𝒳
    intro x hx
    have hx' : t < f x := hle x hx
    have : t ≤ f x := le_of_lt hx'
    simpa [InnerProductSpace.toDual_symm_apply] using this

-- Supporting Hyperplane Theorem
theorem supporting_hyperplane_theorem {n : ℕ} (𝒳 : Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n)) (h_convex : Convex ℝ 𝒳)
    (h_closed : IsClosed 𝒳) (h_notin : x₀ ∉ 𝒳) (h_nonempty : 𝒳.Nonempty) :
  ∃ (w : EuclideanSpace ℝ (Fin n)), w ≠ 0 ∧
    (∀ x ∈ 𝒳, ⟪w, x₀⟫_ℝ ≤ ⟪w, x⟫_ℝ) := by
  classical
  -- Apply strict separation of the point and the closed convex set
  obtain ⟨w, t, hlt, hle⟩ := separation_theorem (𝒳 := 𝒳) (x₀ := x₀) h_closed h_convex h_notin
  have hw_ne : w ≠ 0 := by
    intro hzero
    have hpos : (0 : ℝ) < t := by simpa [hzero, inner_zero_left] using hlt
    rcases h_nonempty with ⟨x, hx⟩
    have htle : t ≤ ⟪w, x⟫_ℝ := hle x hx
    have hle0 : t ≤ 0 := by simpa [hzero, inner_zero_left] using htle
    exact (not_lt_of_ge hle0) hpos
  refine ⟨w, hw_ne, ?_⟩
  intro x hx
  have := hle x hx
  have : ⟪w, x₀⟫_ℝ ≤ ⟪w, x⟫_ℝ := by exact le_trans (le_of_lt hlt) this
  exact this

-- Definition of subgradient
def IsSubgradient {n : ℕ} (𝒳 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ 𝒳 ∧ ∀ y ∈ 𝒳, f x - f y ≤ ⟪g, (x - y)⟫_ℝ

-- Set of subgradients (denoted ∂f(x) in the text)
def SubgradientSet {n : ℕ} (𝒳 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {g | IsSubgradient 𝒳 f x g}

-- Existence of subgradients proposition
theorem existence_of_subgradients {n : ℕ} (𝒳 : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
  -- Part 1: If all points have non-empty subgradient sets, then f is convex
  (∀ x ∈ 𝒳, (SubgradientSet 𝒳 f x).Nonempty → ConvexOn ℝ 𝒳 f) ∧
  -- Part 2: If f is convex, then interior points have non-empty subgradient sets
  (ConvexOn ℝ 𝒳 f → ∀ x ∈ interior 𝒳, (SubgradientSet 𝒳 f x).Nonempty) ∧
  -- Part 3: If f is convex and differentiable at x, then the gradient is in the subgradient set
  (ConvexOn ℝ 𝒳 f → ∀ x ∈ 𝒳, HasFDerivAt f (fderiv ℝ f x) x →
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x) ∈
    SubgradientSet 𝒳 f x) :=
sorry
