/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Dual spaces and locally convex topologies  (book §1.5, pp. 39–45)

Everything in §1.5 is standard functional analysis available in Mathlib; this file records the
correspondence and restates the results in the book's form.

* Definitions 1.5.1/1.5.2 (locally convex spaces, weak topologies): `LocallyConvexSpace`,
  `WeakBilin`, `WeakSpace`, `WeakDual`.
* **Theorem 1.5.8** (Banach–Alaoglu): `DF.banach_alaoglu` (`WeakDual.isCompact_closedBall`).
* **Theorem 1.5.9** (metrizability of the dual ball for separable spaces):
  `DF.dual_ball_metrizable` (`WeakDual.metrizable_of_isCompact`).
* **Corollary 1.5.16** (Hahn–Banach separation): `DF.separation_closed_convex`
  (`geometric_hahn_banach_closed_point`).
* **Theorem 1.5.12** (Krein–Milman): `DF.krein_milman_nonempty`, `DF.krein_milman`.

No `Statement` props are introduced in this file.
-/
import Mathlib

open Set Metric

namespace DF

/-- **Theorem 1.5.8** (Banach–Alaoglu): the closed unit ball of the dual of a normed space is
weak-∗ compact. -/
theorem banach_alaoglu (𝕜 V : Type*) [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] :
    IsCompact (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 V) 1) :=
  WeakDual.isCompact_closedBall 0 1

/-- **Theorem 1.5.9**: for separable `V`, the dual unit ball with the weak-∗ topology is
metrizable. -/
theorem dual_ball_metrizable (𝕜 V : Type*) [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    [TopologicalSpace.SeparableSpace V] :
    TopologicalSpace.MetrizableSpace (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 V) 1) :=
  WeakDual.metrizable_of_isCompact 𝕜 V _ (banach_alaoglu 𝕜 V)

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

omit [T2Space E] in
/-- **Corollary 1.5.16** (separation of a point from a closed convex set). -/
theorem separation_closed_convex {K : Set E} (hK : Convex ℝ K) (hKc : IsClosed K) {y : E}
    (hy : y ∉ K) : ∃ (ℓ : StrongDual ℝ E) (a : ℝ), (∀ x ∈ K, ℓ x < a) ∧ a < ℓ y :=
  geometric_hahn_banach_closed_point hK hKc hy

/-- **Theorem 1.5.12(a)** (Krein–Milman): a nonempty compact convex set has an extreme point. -/
theorem krein_milman_nonempty {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) :
    (K.extremePoints ℝ).Nonempty :=
  hK.extremePoints_nonempty hne

/-- **Theorem 1.5.12(b)** (Krein–Milman): a compact convex set is the closed convex hull of its
extreme points. -/
theorem krein_milman {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) :
    closure (convexHull ℝ (K.extremePoints ℝ)) = K :=
  closure_convexHull_extremePoints hK hconv

end DF
