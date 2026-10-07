/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Bounded operators, resolvents, spectra  (book §1.3 pp. 15–23 and §1.4 pp. 24–37)

Most of §1.3 is standard Banach-algebra theory available in Mathlib; we record the
correspondence and prove the statements in the book's normalisation.

Correspondence with Mathlib
* Prop. 1.3.5 (`B(V,W)` is a Banach space, absolutely summable series converge):
  `ContinuousLinearMap.toNormedAddCommGroup`, `ContinuousLinearMap.completeSpace`,
  `Summable.of_norm`.
* Thm. 1.3.3 (BLT): `ContinuousLinearMap.extend` / `DenseInducing.extend`.
* Thm. 1.3.6 (openness of the invertible elements): `Units.add`, `Units.isOpen`; Neumann series
  `geom_series_eq_inverse` (see `DF.neumann_series` below).
* Def. 1.3.7: `spectrum ℂ A`, `resolventSet ℂ A`; book's `R(A,z) = (A - z)⁻¹` is `DF.res A z`.
* Prop. 1.3.9: `spectrum.isCompact`, `spectrum.nonempty`, `spectrum.norm_le_norm_of_mem`.
* Prop. 1.3.10: `spectrum.map_polynomial_aeval`.
* Thm. 1.3.11 (Gelfand's formula): `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`.
* Prop. 1.4.2 (Riesz): `InnerProductSpace.toDual`; Def. 1.4.3/Prop. 1.4.5: `ContinuousLinearMap.adjoint`.
* Prop. 1.4.7: `IsSelfAdjoint.mem_spectrum_eq_re`, `IsStarNormal.spectralRadius_eq_nnnorm`.
* Thm. 1.4.8 (orthogonal projections): `Submodule.orthogonalProjection`,
  `Submodule.starProjection`.
* Thm. 1.4.11 (continuous functional calculus): `cfc`.

Proved here
* `DF.res_sub_res` — first resolvent identity (1.3.15);
* `DF.res_sub_res'` — second resolvent identity (1.3.16);
* `DF.neumann_series` — the Neumann series in the proof of Thm. 1.3.6;
* `DF.inv_norm_res_le_infDist` — Exercise 1.3.11, `‖R(A,z)‖ ≥ 1/dist(z, σ(A))`;
* `DF.norm_res_eq` — Theorem 1.4.13, `‖R(A,z)‖ = 1/dist(z, σ(A))` for normal `A`;
* `DF.infDist_mul_norm_le`, `DF.exists_unit_norm_sub_lt` — Corollary 1.4.21;
* `DF.IsWeylSequence`, `DF.mem_spectrum_of_isWeylSequence`, `DF.exists_isWeylSequence` —
  Definition 1.4.19 and Theorem 1.4.20;
* `DF.spectrum_subset_of_strong_limit` — Corollary 1.4.22;
* `DF.discSpectrum`, `DF.essSpectrum` — discrete and essential spectrum (Def. 1.3.7).

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Basic

noncomputable section

open scoped InnerProductSpace NNReal ENNReal Topology
open Filter Metric Set

namespace DF

/-! ### Resolvents in a ring -/

section Ring

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The book's resolvent `R(A, z) = (A - z)⁻¹` (1.3.14).  (Mathlib's `resolvent A z` is
`(z - A)⁻¹ = -R(A,z)`.) -/
def res (A : R) (z : ℂ) : R := Ring.inverse (A - algebraMap ℂ R z)

omit [Algebra ℂ R] in
lemma inverse_neg' (x : R) : Ring.inverse (-x) = -Ring.inverse x := by
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    rw [← Units.val_neg, Ring.inverse_unit, Ring.inverse_unit]; simp
  · have h' : ¬IsUnit (-x) := fun h' => h (by simpa using h'.neg)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', neg_zero]

lemma res_eq_neg_resolvent (A : R) (z : ℂ) : res A z = -resolvent A z := by
  unfold res resolvent
  rw [← neg_sub, inverse_neg']

/-- `z ∈ ρ(A)` iff `A - z` is invertible. -/
lemma mem_resolventSet_iff (A : R) (z : ℂ) :
    z ∈ resolventSet ℂ A ↔ IsUnit (A - algebraMap ℂ R z) := by
  rw [spectrum.mem_resolventSet_iff]
  exact ⟨fun h => by simpa using h.neg, fun h => by simpa using h.neg⟩

lemma mem_resolventSet_iff_notMem {A : R} {z : ℂ} :
    z ∈ resolventSet ℂ A ↔ z ∉ spectrum ℂ A :=
  spectrum.mem_resolventSet_iff.trans spectrum.notMem_iff.symm

lemma isUnit_sub_of_mem_resolventSet {A : R} {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    IsUnit (A - algebraMap ℂ R z) := (mem_resolventSet_iff A z).1 hz

lemma sub_mul_res {A : R} {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    (A - algebraMap ℂ R z) * res A z = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_sub_of_mem_resolventSet hz)

lemma res_mul_sub {A : R} {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    res A z * (A - algebraMap ℂ R z) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_sub_of_mem_resolventSet hz)

omit [Algebra ℂ R] in
/-- Abstract identity behind both resolvent identities: `u⁻¹ - v⁻¹ = u⁻¹ (v - u) v⁻¹`. -/
lemma inverse_sub_inverse {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    Ring.inverse u - Ring.inverse v = Ring.inverse u * (v - u) * Ring.inverse v := by
  rw [mul_sub, sub_mul, Ring.inverse_mul_cancel _ hu, one_mul, mul_assoc,
    Ring.mul_inverse_cancel _ hv, mul_one]

omit [Algebra ℂ R] in
lemma inverse_sub_inverse' {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    Ring.inverse u - Ring.inverse v = Ring.inverse v * (v - u) * Ring.inverse u := by
  rw [mul_sub, sub_mul, Ring.inverse_mul_cancel _ hv, one_mul, mul_assoc,
    Ring.mul_inverse_cancel _ hu, mul_one]

/-- **First resolvent identity** (1.3.15). -/
theorem res_sub_res {A : R} {z z' : ℂ} (hz : z ∈ resolventSet ℂ A)
    (hz' : z' ∈ resolventSet ℂ A) :
    res A z - res A z' = (z - z') • (res A z * res A z') ∧
      res A z - res A z' = (z - z') • (res A z' * res A z) := by
  have h1 := inverse_sub_inverse (isUnit_sub_of_mem_resolventSet hz)
    (isUnit_sub_of_mem_resolventSet hz')
  have h2 := inverse_sub_inverse' (isUnit_sub_of_mem_resolventSet hz)
    (isUnit_sub_of_mem_resolventSet hz')
  have hd : (A - algebraMap ℂ R z') - (A - algebraMap ℂ R z) = algebraMap ℂ R (z - z') := by
    rw [map_sub]; abel
  rw [hd] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [res, res, h1, ← Algebra.commutes, mul_assoc, ← Algebra.smul_def]
  · rw [res, res, h2, ← Algebra.commutes, mul_assoc, ← Algebra.smul_def]

/-- **Second resolvent identity** (1.3.16). -/
theorem res_sub_res' {A B : R} {z : ℂ} (hA : z ∈ resolventSet ℂ A)
    (hB : z ∈ resolventSet ℂ B) :
    res A z - res B z = res A z * (B - A) * res B z ∧
      res A z - res B z = res B z * (B - A) * res A z := by
  have hd : (B - algebraMap ℂ R z) - (A - algebraMap ℂ R z) = B - A := by abel
  have h1 := inverse_sub_inverse (isUnit_sub_of_mem_resolventSet hA)
    (isUnit_sub_of_mem_resolventSet hB)
  have h2 := inverse_sub_inverse' (isUnit_sub_of_mem_resolventSet hA)
    (isUnit_sub_of_mem_resolventSet hB)
  rw [hd] at h1 h2
  exact ⟨h1, h2⟩

end Ring

/-! ### Neumann series and the norm of the resolvent -/

section Banach

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R] [NormOneClass R]

omit [NormedAlgebra ℂ R] [NormOneClass R] in
/-- **Neumann series** (proof of Theorem 1.3.6): if `‖C‖ < 1` then `∑ Cⁿ = (1 - C)⁻¹`. -/
theorem neumann_series (C : R) (hC : ‖C‖ < 1) :
    IsUnit (1 - C) ∧ ∑' n : ℕ, C ^ n = Ring.inverse (1 - C) :=
  ⟨(Units.oneSub C hC).isUnit, geom_series_eq_inverse C hC⟩

/-- **Exercise 1.3.11**: for `z ∈ ρ(A)`, `‖R(A,z)‖⁻¹ ≤ dist(z, σ(A))`. -/
theorem inv_norm_res_le_infDist (A : R) {z : ℂ} (hz : z ∈ resolventSet ℂ A)
    (hne : (spectrum ℂ A).Nonempty) :
    ‖res A z‖⁻¹ ≤ infDist z (spectrum ℂ A) := by
  rw [le_infDist hne]
  intro w hw
  by_contra hlt
  push_neg at hlt
  -- `A - w = (A - z) + (z - w)` is invertible by `Units.add`.
  set u : Rˣ := (isUnit_sub_of_mem_resolventSet hz).unit
  have hu : (↑u⁻¹ : R) = res A z := by
    rw [res, ← Ring.inverse_unit]; rfl
  have hsmall : ‖algebraMap ℂ R (z - w)‖ < ‖(↑u⁻¹ : R)‖⁻¹ := by
    rw [hu, norm_algebraMap', ← dist_eq_norm]
    exact hlt
  have hunit : IsUnit (A - algebraMap ℂ R w) := by
    have := (u.add _ hsmall).isUnit
    simp only [Units.val_add, IsUnit.unit_spec, u] at this
    convert this using 1
    rw [map_sub]; abel
  exact hw ((mem_resolventSet_iff A w).2 hunit)

end Banach

/-! ### Self-adjoint (normal) operators on a Hilbert space -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The resolvent of a normal operator via the functional calculus. -/
lemma res_eq_cfc (A : H →L[ℂ] H) [IsStarNormal A] {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    res A z = cfc (fun w : ℂ => (w - z)⁻¹) A := by
  have hne : ∀ w ∈ spectrum ℂ A, w - z ≠ 0 := by
    intro w hw h
    rw [sub_eq_zero] at h
    exact (mem_resolventSet_iff_notMem.1 hz) (h ▸ hw)
  have h1 : cfc (fun w : ℂ => w - z) A = A - algebraMap ℂ (H →L[ℂ] H) z := by
    rw [cfc_sub (a := A) (fun w => w) (fun _ => z), cfc_id' ℂ A, cfc_const z A]
  rw [cfc_inv (a := A) (fun w => w - z) hne, h1]
  rfl

/-- **Theorem 1.4.13**: for normal (in particular self-adjoint) `A` and `z ∈ ρ(A)`,
`‖R(A,z)‖ = 1 / dist(z, σ(A))`. -/
theorem norm_res_eq [Nontrivial H] (A : H →L[ℂ] H) [IsStarNormal A] {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) :
    ‖res A z‖ = (infDist z (spectrum ℂ A))⁻¹ := by
  have hcpt : IsCompact (spectrum ℂ A) := spectrum.isCompact A
  have hne : (spectrum ℂ A).Nonempty := spectrum.nonempty A
  obtain ⟨x0, hx0, hdist⟩ := hcpt.exists_infDist_eq_dist hne z
  have hcont : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (spectrum ℂ A) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun w hw h => ?_
    rw [sub_eq_zero] at h
    exact (mem_resolventSet_iff_notMem.1 hz) (h ▸ hw)
  have hG := IsGreatest.norm_cfc (fun w : ℂ => (w - z)⁻¹) A hcont
  rw [← res_eq_cfc A hz] at hG
  have hG' : IsGreatest ((fun w => ‖(w - z)⁻¹‖) '' spectrum ℂ A) (infDist z (spectrum ℂ A))⁻¹ := by
    refine ⟨⟨x0, hx0, ?_⟩, ?_⟩
    · simp only [norm_inv]
      rw [hdist, dist_comm, dist_eq_norm]
    · rintro _ ⟨w, hw, rfl⟩
      simp only [norm_inv]
      have hpos : 0 < ‖w - z‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        rintro rfl
        exact mem_resolventSet_iff_notMem.1 hz hw
      have hle : infDist z (spectrum ℂ A) ≤ ‖w - z‖ := by
        rw [← dist_eq_norm, dist_comm]; exact infDist_le_dist_of_mem hw
      have h0 : 0 < infDist z (spectrum ℂ A) := by
        rw [hdist]
        refine dist_pos.2 fun h => ?_
        exact mem_resolventSet_iff_notMem.1 hz (h ▸ hx0)
      exact inv_anti₀ h0 hle
  exact hG.unique hG'

/-- First half of **Corollary 1.4.21** (for normal `A`):
`dist(z, σ(A)) ‖v‖ ≤ ‖(A - z) v‖`. -/
theorem infDist_mul_norm_le [Nontrivial H] (A : H →L[ℂ] H) [IsStarNormal A] (z : ℂ) (v : H) :
    infDist z (spectrum ℂ A) * ‖v‖ ≤ ‖(A - algebraMap ℂ (H →L[ℂ] H) z) v‖ := by
  by_cases hz : z ∈ spectrum ℂ A
  · rw [infDist_zero_of_mem hz, zero_mul]; exact norm_nonneg _
  have hz' : z ∈ resolventSet ℂ A := mem_resolventSet_iff_notMem.2 hz
  have hv : v = res A z ((A - algebraMap ℂ (H →L[ℂ] H) z) v) := by
    rw [← ContinuousLinearMap.mul_apply, res_mul_sub hz', ContinuousLinearMap.one_apply]
  have hd : infDist z (spectrum ℂ A) * ‖res A z‖ ≤ 1 := by
    rw [norm_res_eq A hz']; exact mul_inv_le_one
  calc infDist z (spectrum ℂ A) * ‖v‖
      ≤ infDist z (spectrum ℂ A) * (‖res A z‖ * ‖(A - algebraMap ℂ (H →L[ℂ] H) z) v‖) := by
        gcongr
        · exact infDist_nonneg
        · conv_lhs => rw [hv]
          exact (res A z).le_opNorm _
    _ = (infDist z (spectrum ℂ A) * ‖res A z‖) * ‖(A - algebraMap ℂ (H →L[ℂ] H) z) v‖ := by
        ring
    _ ≤ 1 * ‖(A - algebraMap ℂ (H →L[ℂ] H) z) v‖ := by gcongr
    _ = _ := one_mul _

/-- Second half of **Corollary 1.4.21**, on the resolvent set (normal `A`). -/
theorem exists_unit_norm_sub_lt_of_mem_resolventSet [Nontrivial H] (A : H →L[ℂ] H)
    [IsStarNormal A] {z : ℂ} (hz : z ∈ resolventSet ℂ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : H, ‖v‖ = 1 ∧
      ‖(A - algebraMap ℂ (H →L[ℂ] H) z) v‖ < infDist z (spectrum ℂ A) + ε := by
  set d := infDist z (spectrum ℂ A)
  have hd0 : 0 < d := by
    have hne : (spectrum ℂ A).Nonempty := spectrum.nonempty A
    rw [← (spectrum.isCompact A).isClosed.notMem_iff_infDist_pos hne]
    exact mem_resolventSet_iff_notMem.1 hz
  have hR : ‖res A z‖ = d⁻¹ := norm_res_eq A hz
  have hr : (d + ε)⁻¹ < ‖res A z‖ := by
    rw [hR]; exact inv_strictAnti₀ hd0 (by linarith)
  obtain ⟨u, hu1, hu⟩ := (res A z).exists_lt_apply_of_lt_opNorm hr
  set w := res A z u
  have hw0 : 0 < ‖w‖ := lt_trans (by positivity) hu
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0.ne']
  · have : (A - algebraMap ℂ (H →L[ℂ] H) z) (‖w‖⁻¹ • w) = (‖w‖⁻¹ : ℂ) • u := by
      rw [show (‖w‖⁻¹ • w : H) = ((‖w‖⁻¹ : ℝ) : ℂ) • w from (Complex.coe_smul _ _).symm,
        map_smul]
      simp only [w, ← ContinuousLinearMap.mul_apply, sub_mul_res hz,
        ContinuousLinearMap.one_apply, Complex.ofReal_inv]
    rw [this, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_eq_div]
    rw [div_lt_iff₀ hw0]
    calc ‖u‖ < 1 := hu1
      _ = (d + ε) * (d + ε)⁻¹ := (mul_inv_cancel₀ (by positivity)).symm
      _ ≤ (d + ε) * ‖w‖ := by gcongr

/-- Second half of **Corollary 1.4.21** for self-adjoint `A` and arbitrary `z`:
`inf_{‖v‖=1} ‖(A - z) v‖ ≤ dist(z, σ(A))`. -/
theorem exists_unit_norm_sub_lt [Nontrivial H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : H, ‖v‖ = 1 ∧
      ‖(A - algebraMap ℂ (H →L[ℂ] H) z) v‖ < infDist z (spectrum ℂ A) + ε := by
  have : IsStarNormal A := hA.isStarNormal
  by_cases hz : z ∈ spectrum ℂ A
  · -- `z` is real; perturb into the upper half plane.
    set δ := ε / 3
    have hδ : 0 < δ := by positivity
    set z' : ℂ := z + (δ : ℂ) * Complex.I
    have hz'im : z'.im ≠ 0 := by
      simp only [z', Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
      rw [hA.im_eq_zero_of_mem_spectrum hz, zero_add]; exact hδ.ne'
    have hz' : z' ∈ resolventSet ℂ A :=
      mem_resolventSet_iff_notMem.2 fun h => hz'im (hA.im_eq_zero_of_mem_spectrum h)
    obtain ⟨v, hv1, hv⟩ := exists_unit_norm_sub_lt_of_mem_resolventSet A hz' hδ
    have hdist : infDist z' (spectrum ℂ A) ≤ δ := by
      refine (infDist_le_dist_of_mem hz).trans ?_
      simp [z', dist_eq_norm, Complex.norm_real, abs_of_pos hδ]
    refine ⟨v, hv1, ?_⟩
    rw [infDist_zero_of_mem hz, zero_add]
    have hsplit : (A - algebraMap ℂ (H →L[ℂ] H) z) v =
        (A - algebraMap ℂ (H →L[ℂ] H) z') v + ((δ : ℂ) * Complex.I) • v := by
      simp only [z', map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      abel
    rw [hsplit]
    calc ‖(A - algebraMap ℂ (H →L[ℂ] H) z') v + ((δ : ℂ) * Complex.I) • v‖
        ≤ ‖(A - algebraMap ℂ (H →L[ℂ] H) z') v‖ + ‖((δ : ℂ) * Complex.I) • v‖ := norm_add_le _ _
      _ < (δ + δ) + δ := by
          refine add_lt_add_of_lt_of_le (by linarith) (le_of_eq ?_)
          rw [norm_smul, hv1, mul_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_of_nonneg hδ.le]
      _ = ε := by ring
  · exact exists_unit_norm_sub_lt_of_mem_resolventSet A (mem_resolventSet_iff_notMem.2 hz) hε

/-! ### Weyl sequences -/

/-- **Definition 1.4.19**: a Weyl sequence for `A` at `z`. -/
def IsWeylSequence (A : H →L[ℂ] H) (z : ℂ) (ψ : ℕ → H) : Prop :=
  (∀ n, ‖ψ n‖ = 1) ∧
    Tendsto (fun n => ‖(A - algebraMap ℂ (H →L[ℂ] H) z) (ψ n)‖) atTop (𝓝 0)

/-- **Theorem 1.4.20**, first part: if there is a Weyl sequence at `z`, then `z ∈ σ(A)`. -/
theorem mem_spectrum_of_isWeylSequence {A : H →L[ℂ] H} {z : ℂ} {ψ : ℕ → H}
    (hψ : IsWeylSequence A z ψ) : z ∈ spectrum ℂ A := by
  intro hz
  have hlim : Tendsto (fun n => ‖res A z‖ * ‖(A - algebraMap ℂ (H →L[ℂ] H) z) (ψ n)‖) atTop
      (𝓝 0) := by simpa using hψ.2.const_mul ‖res A z‖
  have hge : ∀ n, (1 : ℝ) ≤ ‖res A z‖ * ‖(A - algebraMap ℂ (H →L[ℂ] H) z) (ψ n)‖ := by
    intro n
    have hv : ψ n = res A z ((A - algebraMap ℂ (H →L[ℂ] H) z) (ψ n)) := by
      rw [← ContinuousLinearMap.mul_apply, res_mul_sub hz, ContinuousLinearMap.one_apply]
    calc (1 : ℝ) = ‖ψ n‖ := (hψ.1 n).symm
      _ ≤ _ := by conv_lhs => rw [hv]
                  exact (res A z).le_opNorm _
  have := ge_of_tendsto' hlim hge
  norm_num at this

/-- **Theorem 1.4.20**, converse for self-adjoint operators. -/
theorem exists_isWeylSequence [Nontrivial H] {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ A) : ∃ ψ : ℕ → H, IsWeylSequence A z ψ := by
  have h := fun n : ℕ => exists_unit_norm_sub_lt hA z (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose ψ hψ1 hψ using h
  refine ⟨ψ, hψ1, ?_⟩
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := hψ n
  rw [infDist_zero_of_mem hz, zero_add] at this
  exact this.le

/-- **Theorem 1.4.20** for self-adjoint `A`: `z ∈ σ(A)` iff there is a Weyl sequence at `z`. -/
theorem mem_spectrum_iff_exists_isWeylSequence [Nontrivial H] {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (z : ℂ) :
    z ∈ spectrum ℂ A ↔ ∃ ψ : ℕ → H, IsWeylSequence A z ψ :=
  ⟨exists_isWeylSequence hA, fun ⟨_, h⟩ => mem_spectrum_of_isWeylSequence h⟩

/-- A strong limit of self-adjoint operators is self-adjoint. -/
lemma isSelfAdjoint_of_strong_limit {An : ℕ → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hAn : ∀ n, IsSelfAdjoint (An n)) (hlim : ∀ ψ, Tendsto (fun n => An n ψ) atTop (𝓝 (A ψ))) :
    IsSelfAdjoint A := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have h1 : Tendsto (fun n => ⟪An n x, y⟫_ℂ) atTop (𝓝 ⟪A x, y⟫_ℂ) :=
    (hlim x).inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪x, An n y⟫_ℂ) atTop (𝓝 ⟪x, A y⟫_ℂ) :=
    tendsto_const_nhds.inner (hlim y)
  have h3 : (fun n => ⟪An n x, y⟫_ℂ) = fun n => ⟪x, An n y⟫_ℂ :=
    funext fun n => (hAn n).isSymmetric x y
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Corollary 1.4.22**: if self-adjoint `A_n → A` strongly, then
`σ(A) ⊆ ⋂ₙ closure (⋃_{k ≥ n} σ(A_k))`. -/
theorem spectrum_subset_of_strong_limit [Nontrivial H] {An : ℕ → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hAn : ∀ n, IsSelfAdjoint (An n)) (hlim : ∀ ψ, Tendsto (fun n => An n ψ) atTop (𝓝 (A ψ))) :
    spectrum ℂ A ⊆ ⋂ n, closure (⋃ k ≥ n, spectrum ℂ (An k)) := by
  have hA := isSelfAdjoint_of_strong_limit hAn hlim
  intro E hE
  simp only [mem_iInter]
  intro n
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨ψ, hψ1, hψ⟩ := exists_unit_norm_sub_lt hA E (half_pos hε)
  rw [infDist_zero_of_mem hE, zero_add] at hψ
  have hconv : Tendsto (fun k => ‖(An k - algebraMap ℂ (H →L[ℂ] H) E) ψ‖) atTop
      (𝓝 ‖(A - algebraMap ℂ (H →L[ℂ] H) E) ψ‖) := by
    have h := ((hlim ψ).sub_const ((algebraMap ℂ (H →L[ℂ] H) E) ψ)).norm
    simpa only [_root_.sub_apply] using h
  have hev := (hconv.eventually (gt_mem_nhds hψ)).and (eventually_ge_atTop n)
  obtain ⟨k, hk, hkn⟩ := hev.exists
  have : IsStarNormal (An k) := (hAn k).isStarNormal
  have hd := infDist_mul_norm_le (An k) E ψ
  rw [hψ1, mul_one] at hd
  obtain ⟨b, hb, hdb⟩ := (infDist_lt_iff (spectrum.nonempty (An k))).1 (hd.trans_lt hk)
  exact ⟨b, mem_iUnion₂.2 ⟨k, hkn, hb⟩, hdb.trans (half_lt_self hε)⟩

/-! ### Discrete and essential spectrum -/

/-- The **discrete spectrum** (Definition 1.3.7): isolated eigenvalues of finite multiplicity. -/
def discSpectrum (A : H →L[ℂ] H) : Set ℂ :=
  {z | z ∈ spectrum ℂ A ∧ LinearMap.ker ((A - algebraMap ℂ (H →L[ℂ] H) z : H →L[ℂ] H) : H →ₗ[ℂ] H) ≠ ⊥ ∧
    FiniteDimensional ℂ
      (LinearMap.ker ((A - algebraMap ℂ (H →L[ℂ] H) z : H →L[ℂ] H) : H →ₗ[ℂ] H)) ∧
    ∃ δ > 0, ball z δ ∩ spectrum ℂ A = {z}}

/-- The **essential spectrum** `σ_ess(A) = σ(A) ∖ σ_disc(A)`. -/
def essSpectrum (A : H →L[ℂ] H) : Set ℂ := spectrum ℂ A \ discSpectrum A

lemma discSpectrum_subset (A : H →L[ℂ] H) : discSpectrum A ⊆ spectrum ℂ A := fun _ h => h.1

lemma essSpectrum_subset (A : H →L[ℂ] H) : essSpectrum A ⊆ spectrum ℂ A := sdiff_subset

end Hilbert

end DF
