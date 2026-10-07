/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.7: invariance of topological entropy under conjugacy (Proposition 3.7.7)

Main results:
* `DF.htop_le_of_semiconj` — if `h : X → Y` is a uniformly continuous surjection with
  `h ∘ S = R ∘ h`, then `h_top(R) ≤ h_top(S)`;
* `DF.htop_eq_of_conj`, `DF.entropyMetricIndependence` — **Proposition 3.7.7** in the form of
  conjugacy invariance; this proves `DF.EntropyMetricIndependenceStatement`. (Applied to the
  identity map between two metrics generating the same compact topology, it also gives the
  metric independence.)
-/
import DamanikFillman.Ch3.Entropy

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology
open scoped ENNReal

namespace DF

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]

/-- Entropy does not increase under uniformly continuous semiconjugacies onto. -/
theorem htop_le_of_semiconj [Nonempty X] [Nonempty Y] {S : X → X} {R : Y → Y}
    (hS : Continuous S) (hR : Continuous R) {h : X → Y} (hh : UniformContinuous h)
    (hsurj : Surjective h) (hconj : ∀ x, h (S x) = R (h x)) : htop R ≤ htop S := by
  classical
  have hit : ∀ m x, R^[m] (h x) = h (S^[m] x) := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [iterate_succ_apply, iterate_succ_apply, ← hconj, ih]
  refine iSup₂_le fun ε hε => ?_
  obtain ⟨δ', hδ', hδ'h⟩ := Metric.uniformContinuous_iff.1 hh ε hε
  set δ := δ' / 2
  have hδ : 0 < δ := half_pos hδ'
  -- covers are pushed forward
  have hcov : ∀ n, covNum R n ε ≤ covNum S n δ := by
    intro n
    obtain ⟨C, hC, hcard⟩ := covNum_spec hS n hδ
    rw [← hcard]
    refine (covNum_le (C := C.image (fun s => h '' s)) ⟨fun y => ?_, ?_⟩).trans Finset.card_image_le
    · obtain ⟨x, rfl⟩ := hsurj y
      obtain ⟨s, hs, hxs⟩ := hC.1 x
      exact ⟨_, Finset.mem_image_of_mem _ hs, x, hxs, rfl⟩
    · intro t ht y hy y' hy'
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      have hd := hC.2 s hs x hx x' hx'
      refine dynDist_le hε.le fun m => ?_
      rw [hit, hit]
      exact (hδ'h ((dist_le_dynDist m x x').trans_lt (hd.trans_lt (half_lt_self hδ')))).le
  have hlim : hEps R ε ≤ hEps S δ := by
    refine le_of_tendsto_of_tendsto' (tendsto_hEps hR hε) (tendsto_hEps hS hδ) fun n => ?_
    have h1 : (1 : ℝ) ≤ covNum R n ε := by exact_mod_cast one_le_covNum hR n hε
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by exact_mod_cast hcov n))
      (Nat.cast_nonneg _)
  exact (ENNReal.ofReal_le_ofReal hlim).trans (le_iSup₂ (f := fun δ (_ : 0 < δ) =>
    ENNReal.ofReal (hEps S δ)) δ hδ)

/-- **Proposition 3.7.7**: topologically conjugate systems have the same topological entropy. -/
theorem htop_eq_of_conj [Nonempty X] [Nonempty Y] {S : X → X} {R : Y → Y} (hS : Continuous S)
    (h : X ≃ₜ Y) (hconj : ∀ x, h (S x) = R (h x)) : htop S = htop R := by
  have hR : Continuous R := by
    have : R = h ∘ S ∘ h.symm := by
      funext y; simp only [comp_apply]; rw [hconj, Homeomorph.apply_symm_apply]
    rw [this]; exact h.continuous.comp (hS.comp h.symm.continuous)
  have hconj' : ∀ y, h.symm (R y) = S (h.symm y) := fun y => by
    rw [h.symm_apply_eq, hconj, Homeomorph.apply_symm_apply]
  exact le_antisymm
    (htop_le_of_semiconj hR hS (CompactSpace.uniformContinuous_of_continuous h.symm.continuous)
      h.symm.surjective hconj')
    (htop_le_of_semiconj hS hR (CompactSpace.uniformContinuous_of_continuous h.continuous)
      h.surjective hconj)

/-- `DF.EntropyMetricIndependenceStatement` holds. -/
theorem entropyMetricIndependence : EntropyMetricIndependenceStatement :=
  fun _ _ _ _ _ _ _ _ _ _ h hS hconj => htop_eq_of_conj hS h hconj

end DF
