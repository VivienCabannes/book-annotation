import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Basic

open InnerProductSpace


/-!
# Chapter 1 — Introduction
-/

/-- Notations -/
notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

noncomputable def grad {n : ℕ} (f : ℝ^n → ℝ) (x : ℝ^n) : ℝ^n :=
  (InnerProductSpace.toDual ℝ (ℝ^n)).symm (fderiv ℝ f x)

-- Theorem 1.1: Separation Theorem
theorem separation_theorem {n : ℕ} (𝒳 : Set (ℝ^n)) (x₀ : ℝ^n)
    (h_closed : IsClosed 𝒳) (h_convex : Convex ℝ 𝒳) (h_notin : x₀ ∉ 𝒳) :
  ∃ (w : ℝ^n) (t : ℝ),
    (⟪w, x₀⟫_ℝ < t) ∧ (∀ x ∈ 𝒳, t ≤ ⟪w, x⟫_ℝ) :=
by
  sorry

-- Theorem 1.2: Supporting Hyperplane Theorem
theorem supporting_hyperplane_theorem {n : ℕ} (𝒳 : Set (ℝ^n)) (x₀ : ℝ^n)
    (h_convex : Convex ℝ 𝒳) (h_boundary : x₀ ∈ frontier 𝒳) :
  ∃ (w : ℝ^n), w ≠ 0 ∧
    (∀ x ∈ 𝒳, ⟪w, x₀⟫_ℝ ≤ ⟪w, x⟫_ℝ) :=
by
  sorry

-- Definition 1.2: Subgradient
def IsSubgradient {n : ℕ} (𝒳 : Set (ℝ^n)) (f : ℝ^n → ℝ) (x : ℝ^n) (g : ℝ^n) :
   Prop := x ∈ 𝒳 ∧ ∀ y ∈ 𝒳, f x - f y ≤ ⟪g, (x - y)⟫_ℝ

-- Definition 1.2: Set of subgradients
def SubgradientSet {n : ℕ} (𝒳 : Set (ℝ^n)) (f : ℝ^n → ℝ) (x : ℝ^n) :
    Set (ℝ^n) := {g | IsSubgradient 𝒳 f x g}

-- Proposition 1.1: Existence of subgradients
theorem existence_of_subgradients {n : ℕ} (𝒳 : Set (ℝ^n)) (f : ℝ^n → ℝ) :
  ((∀ x ∈ 𝒳, (SubgradientSet 𝒳 f x).Nonempty) → ConvexOn ℝ 𝒳 f) ∧
  (ConvexOn ℝ 𝒳 f → ∀ x ∈ interior 𝒳, (SubgradientSet 𝒳 f x).Nonempty) ∧
  (ConvexOn ℝ 𝒳 f → ∀ x ∈ 𝒳, HasFDerivAt f (fderiv ℝ f x) x → grad f x ∈ SubgradientSet 𝒳 f x) :=
by
  sorry

-- Proposition 1.2: Local minima are global minima
theorem local_minima_are_global {n : ℕ}  {x : ℝ^n} (𝒳 : Set (ℝ^n)) (f : ℝ^n → ℝ)
  (h_conv : ConvexOn ℝ 𝒳 f) (hx : x ∈ 𝒳) (h_local : IsLocalMin f x) :
    ∀ y ∈ 𝒳, f x ≤ f y :=
by
  sorry

-- Proposition 1.2: Global minimum characterization via subgradient
theorem global_min_iff_zero_in_subgradient {n : ℕ} {x : ℝ^n} (𝒳 : Set (ℝ^n)) (f : ℝ^n → ℝ)
  (h_conv : ConvexOn ℝ 𝒳 f) (hx : x ∈ 𝒳) :
    (∀ y ∈ 𝒳, f x ≤ f y) ↔ (0 ∈ SubgradientSet 𝒳 f x) :=
by
  sorry

-- Proposition 1.3: First-order optimality condition
theorem first_order_optimality_condition {n : ℕ} {x : ℝ^n} (𝒳 : Set (ℝ^n)) (f : ℝ^n → ℝ)
  (h_closed : IsClosed 𝒳) (h_conv : Convex ℝ 𝒳) (h_fconv : ConvexOn ℝ 𝒳 f) (hx : x ∈ 𝒳)
  (h_diff : HasFDerivAt f (fderiv ℝ f x) x) :
    (∀ y ∈ 𝒳, f x ≤ f y) ↔ (∀ y ∈ 𝒳, ⟪grad f x, x - y⟫_ℝ ≤ 0) :=
by
  sorry
