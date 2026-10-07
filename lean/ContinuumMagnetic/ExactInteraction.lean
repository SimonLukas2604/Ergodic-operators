/-
# Paper III: the exact interaction as a two-dimensional Weyl series

Abstract core of §3 ("The exact interaction and the physical fibres", "Covariance of the
exact interaction", "The discrete Fourier transform") and of §4.2, equation
`(eq:full-lattice-generators)`.

Setting.  `H` is a complex Hilbert space, `T₁ T₂` are unitaries with
`T₁ T₂ = e(γ) T₂ T₁` (`c-eq:translations`), `S_m = T₂^{m₂} T₁^{m₁}`, `A` is a bounded operator
commuting with `T₁, T₂`, and `φ_m = S_m φ₀` is a Hilbert basis.  The exact coefficients are
`f_{r,q} = ⟨A φ_{(r,q)}, φ₀⟩` (`c-eq:exact-coefficients`, inner product linear in the first
slot); with Mathlib's convention this is `⟪φ₀, A φ_{(r,q)}⟫_ℂ`.

Results.
* `magS_mul` : `S_j S_l = e(γ j₁ l₂) S_{j+l}` (§3, "Covariance");
* `inner_magS_exact` : `w_{jl} = ⟪φ_j, A φ_l⟫ = e(-γ j₁(l₂-j₂)) f_{l-j}` (`c-eq:magnetic-cocycle`);
* `exactCoeff_neg` : `f_{-r,-q} = e(-γrq) conj f_{r,q}` for self-adjoint `A`
  (`c-eq:twisted-adjoint`), hence `selfAdjoint_weylSymbol`;
* `exact_interaction_eq_op2` : `Φ⁻¹ A Φ = op2 (-γ) (weylSymbol γ f)` where `Φ δ_m = φ_m`
  (§4.2, the identity `c_{r,q} e^{πiαrq} e^{2πiαnq} = f_{r,q} e^{-2πiγnq}`);
  no relabelling of indices is needed;
* `norm_le_tsum_exactCoeff` : `‖A‖ ≤ ∑ |f_{r,q}|`.
-/
import ContinuumMagnetic.AffineIsland

noncomputable section

open AMO
open scoped ComplexConjugate InnerProductSpace

namespace CMS

/-! ### A group-theoretic commutation lemma -/

/-- If `x y = c y x` with `c` commuting with `x, y`, then `x^a y^b = c^{ab} y^b x^a`. -/
lemma zpow_mul_zpow_of_comm {G : Type*} [Group G] {x y c : G} (hcx : Commute c x)
    (hcy : Commute c y) (h : x * y = c * (y * x)) (a b : ℤ) :
    x ^ a * y ^ b = c ^ (a * b) * (y ^ b * x ^ a) := by
  have h1 : SemiconjBy x y (c * y) := by
    unfold SemiconjBy; rw [h, mul_assoc]
  have h2 : x * y ^ b = c ^ b * y ^ b * x := by
    have := h1.zpow_right b
    unfold SemiconjBy at this
    rw [this, hcy.mul_zpow]
  have h3 : SemiconjBy (y ^ b) (c ^ b * x) x := by
    unfold SemiconjBy
    rw [h2, ← mul_assoc, ((hcy.zpow_left b).zpow_right b).eq]
  have h4 := h3.zpow_right a
  unfold SemiconjBy at h4
  rw [← h4, ((hcx.zpow_left b)).mul_zpow, ← zpow_mul, mul_comm b a, ← mul_assoc,
    ← ((hcy.zpow_left (a * b)).zpow_right b).eq, mul_assoc]

/-! ### Scalar unitaries -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma e_mem_unitary (t : ℝ) : e t ∈ unitary ℂ := by
  rw [Unitary.mem_iff]
  have : star (e t) * e t = 1 := by
    rw [show star (e t) = conj (e t) from rfl, conj_e, ← e_add, neg_add_cancel, e_zero]
  exact ⟨this, by rw [mul_comm, this]⟩

/-- The scalar unitary `e(t) · 1`. -/
def phaseU (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (t : ℝ) :
    unitary (H →L[ℂ] H) :=
  ⟨e t • (1 : H →L[ℂ] H), Unitary.smul_mem_of_mem (e_mem_unitary t) (Submonoid.one_mem _)⟩

@[simp] lemma coe_phaseU (t : ℝ) : ((phaseU H t : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
    e t • (1 : H →L[ℂ] H) := rfl

lemma phaseU_apply (t : ℝ) (x : H) : (phaseU H t : H →L[ℂ] H) x = e t • x := rfl

lemma phaseU_mul (s t : ℝ) : phaseU H s * phaseU H t = phaseU H (s + t) := by
  apply Subtype.ext
  change (e s • (1 : H →L[ℂ] H)) * (e t • 1) = e (s + t) • 1
  rw [smul_mul_smul_comm, one_mul, e_add]

lemma phaseU_zero : phaseU H 0 = 1 := by
  apply Subtype.ext
  change e 0 • (1 : H →L[ℂ] H) = 1
  rw [e_zero, one_smul]

lemma phaseU_inv (t : ℝ) : (phaseU H t)⁻¹ = phaseU H (-t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [phaseU_mul, add_neg_cancel, phaseU_zero]

lemma phaseU_zpow (t : ℝ) (n : ℤ) : phaseU H t ^ n = phaseU H (n * t) := by
  induction n using Int.induction_on with
  | zero => simp [phaseU_zero]
  | succ k ih =>
    rw [zpow_add_one, ih, phaseU_mul]; congr 1; push_cast; ring
  | pred k ih =>
    rw [zpow_sub_one, ih, phaseU_inv, phaseU_mul]; congr 1; push_cast; ring

lemma phaseU_commute (t : ℝ) (U : unitary (H →L[ℂ] H)) : Commute (phaseU H t) U := by
  apply Subtype.ext
  change (e t • (1 : H →L[ℂ] H)) * U = U * (e t • 1)
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- The operator relation `T₁T₂ = e(γ) T₂T₁` in the unitary group. -/
lemma comm_rel_of_op {γ : ℝ} {T₁ T₂ : unitary (H →L[ℂ] H)}
    (h : (T₁ : H →L[ℂ] H) * T₂ = e γ • ((T₂ : H →L[ℂ] H) * T₁)) :
    T₁ * T₂ = phaseU H γ * (T₂ * T₁) := by
  apply Subtype.ext
  change (T₁ : H →L[ℂ] H) * T₂ = (e γ • (1 : H →L[ℂ] H)) * (T₂ * T₁)
  rw [h, smul_mul_assoc, one_mul]

lemma unitary_mul_apply (U V : unitary (H →L[ℂ] H)) (x : H) :
    ((U * V : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x = (U : H →L[ℂ] H) ((V : H →L[ℂ] H) x) := rfl

lemma inner_unitary_map (U : unitary (H →L[ℂ] H)) (x y : H) :
    ⟪(U : H →L[ℂ] H) x, (U : H →L[ℂ] H) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.mul_apply, Unitary.coe_star_mul_self, ContinuousLinearMap.one_apply]

/-! ### Magnetic translations -/

/-- The magnetic translations `S_m = T₂^{m₂} T₁^{m₁}` (`c-eq:translations`). -/
def magS (T₁ T₂ : unitary (H →L[ℂ] H)) (m : ℤ × ℤ) : unitary (H →L[ℂ] H) :=
  T₂ ^ m.2 * T₁ ^ m.1

/-- **Composition law** (§3, "Covariance of the exact interaction"):
`S_j S_l = e(γ j₁ l₂) S_{j+l}`. -/
theorem magS_mul {γ : ℝ} {T₁ T₂ : unitary (H →L[ℂ] H)}
    (hT : T₁ * T₂ = phaseU H γ * (T₂ * T₁)) (j l : ℤ × ℤ) :
    magS T₁ T₂ j * magS T₁ T₂ l = phaseU H (γ * j.1 * l.2) * magS T₁ T₂ (j + l) := by
  have key := zpow_mul_zpow_of_comm (phaseU_commute γ T₁) (phaseU_commute γ T₂) hT j.1 l.2
  rw [phaseU_zpow] at key
  unfold magS
  calc T₂ ^ j.2 * T₁ ^ j.1 * (T₂ ^ l.2 * T₁ ^ l.1)
      = T₂ ^ j.2 * (T₁ ^ j.1 * T₂ ^ l.2) * T₁ ^ l.1 := by group
    _ = T₂ ^ j.2 * (phaseU H (↑(j.1 * l.2) * γ) * (T₂ ^ l.2 * T₁ ^ j.1)) * T₁ ^ l.1 := by
        rw [key]
    _ = phaseU H (↑(j.1 * l.2) * γ) * (T₂ ^ j.2 * T₂ ^ l.2 * (T₁ ^ j.1 * T₁ ^ l.1)) := by
        rw [← mul_assoc, ← (phaseU_commute _ _).eq]; group
    _ = _ := by
        rw [← zpow_add, ← zpow_add]
        congr 1
        · congr 1; push_cast; ring

/-- `S_l = e(-γ j₁ (l₂ - j₂)) S_j S_{l-j}`, i.e. `S_j^{-1} S_l = e(-γ j₁(l₂-j₂)) S_{l-j}`. -/
lemma magS_eq_mul {γ : ℝ} {T₁ T₂ : unitary (H →L[ℂ] H)}
    (hT : T₁ * T₂ = phaseU H γ * (T₂ * T₁)) (j l : ℤ × ℤ) :
    magS T₁ T₂ l =
      phaseU H (-γ * j.1 * (l.2 - j.2)) * (magS T₁ T₂ j * magS T₁ T₂ (l - j)) := by
  rw [magS_mul hT, ← mul_assoc, phaseU_mul, add_sub_cancel]
  convert (one_mul _).symm
  convert phaseU_zero (H := H)
  simp only [Prod.snd_sub, Int.cast_sub]; ring

/-- Operators commuting with a unitary commute with its whole centralizer subgroup. -/
def commutantSubgroup (A : H →L[ℂ] H) : Subgroup (unitary (H →L[ℂ] H)) where
  carrier := {U | Commute A (U : H →L[ℂ] H)}
  one_mem' := Commute.one_right A
  mul_mem' := fun ha hb => Commute.mul_right ha hb
  inv_mem' := by
    intro U (hU : Commute A (U : H →L[ℂ] H))
    change Commute A ((U⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
    rw [← Unitary.star_eq_inv, Unitary.coe_star]
    have h1 : star (U : H →L[ℂ] H) * U = 1 := Unitary.star_mul_self_of_mem U.2
    have h2 : (U : H →L[ℂ] H) * star (U : H →L[ℂ] H) = 1 := Unitary.mul_star_self_of_mem U.2
    unfold Commute SemiconjBy
    calc A * star (U : H →L[ℂ] H) = star (U : H →L[ℂ] H) * U * A * star (U : H →L[ℂ] H) := by
          rw [h1, one_mul]
      _ = star (U : H →L[ℂ] H) * (A * U) * star (U : H →L[ℂ] H) := by rw [hU.eq]; noncomm_ring
      _ = star (U : H →L[ℂ] H) * A := by rw [mul_assoc, mul_assoc, h2, mul_one]

lemma commute_magS {T₁ T₂ : unitary (H →L[ℂ] H)} {A : H →L[ℂ] H}
    (h₁ : Commute A (T₁ : H →L[ℂ] H)) (h₂ : Commute A (T₂ : H →L[ℂ] H)) (m : ℤ × ℤ) :
    Commute A (magS T₁ T₂ m : H →L[ℂ] H) := by
  have : magS T₁ T₂ m ∈ commutantSubgroup A :=
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ h₂ _) (Subgroup.zpow_mem _ h₁ _)
  exact this

/-! ### The exact coefficients and their covariance -/

/-- The exact interaction coefficients `f_m = ⟨A φ_m, φ₀⟩` (paper, linear in the first slot),
i.e. `⟪φ₀, A φ_m⟫_ℂ` in Mathlib's convention (`c-eq:exact-coefficients`). -/
def exactCoeff (T₁ T₂ : unitary (H →L[ℂ] H)) (A : H →L[ℂ] H) (φ₀ : H) : Symbol :=
  fun m => ⟪φ₀, A ((magS T₁ T₂ m : H →L[ℂ] H) φ₀)⟫_ℂ

section Covariance

variable {γ : ℝ} {T₁ T₂ : unitary (H →L[ℂ] H)} (hT : T₁ * T₂ = phaseU H γ * (T₂ * T₁))
  {A : H →L[ℂ] H} (h₁ : Commute A (T₁ : H →L[ℂ] H)) (h₂ : Commute A (T₂ : H →L[ℂ] H)) (φ₀ : H)

include hT h₁ h₂

/-- **Magnetic cocycle** (`c-eq:magnetic-cocycle`): with `φ_m = S_m φ₀`,
`w_{jl} = ⟪φ_j, A φ_l⟫_ℂ = e(-γ j₁ (l₂ - j₂)) f_{l-j}`. -/
theorem inner_magS_exact (j l : ℤ × ℤ) :
    ⟪(magS T₁ T₂ j : H →L[ℂ] H) φ₀, A ((magS T₁ T₂ l : H →L[ℂ] H) φ₀)⟫_ℂ =
      e (-γ * j.1 * (l.2 - j.2)) * exactCoeff T₁ T₂ A φ₀ (l - j) := by
  rw [magS_eq_mul hT j l, unitary_mul_apply, phaseU_apply, unitary_mul_apply, map_smul,
    ← ContinuousLinearMap.mul_apply A, (commute_magS h₁ h₂ j).eq, ContinuousLinearMap.mul_apply,
    inner_smul_right, inner_unitary_map]
  rfl

/-- **Twisted adjointness** (`c-eq:twisted-adjoint`): if `A` is self-adjoint then
`f_{-r,-q} = e(-γ r q) conj f_{r,q}`. -/
theorem exactCoeff_neg (hA : IsSelfAdjoint A) (p : ℤ × ℤ) :
    exactCoeff T₁ T₂ A φ₀ (-p) = e (-γ * p.1 * p.2) * conj (exactCoeff T₁ T₂ A φ₀ p) := by
  have h := inner_magS_exact hT h₁ h₂ φ₀ p 0
  have h0 := inner_magS_exact hT h₁ h₂ φ₀ 0 p
  have hsa : ⟪(magS T₁ T₂ p : H →L[ℂ] H) φ₀, A ((magS T₁ T₂ 0 : H →L[ℂ] H) φ₀)⟫_ℂ =
      conj ⟪(magS T₁ T₂ 0 : H →L[ℂ] H) φ₀, A ((magS T₁ T₂ p : H →L[ℂ] H) φ₀)⟫_ℂ := by
    have hA' : ContinuousLinearMap.adjoint A = A := hA
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right A, hA']
  rw [h, h0, zero_sub] at hsa
  simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, zero_mul, e_zero, one_mul,
    sub_zero] at hsa
  have he : e (-γ * p.1 * p.2) * e (-γ * p.1 * (0 - p.2)) = 1 := by
    rw [← e_add, ← e_zero]; congr 1; ring
  calc exactCoeff T₁ T₂ A φ₀ (-p)
      = e (-γ * p.1 * p.2) * (e (-γ * p.1 * (0 - p.2)) * exactCoeff T₁ T₂ A φ₀ (-p)) := by
        rw [← mul_assoc, he, one_mul]
    _ = _ := by simpa using congrArg (e (-γ * p.1 * p.2) * ·) hsa

/-- **Hermiticity of the symbol.** If `A` is self-adjoint, the Weyl symbol
`c_{r,q} = e(γrq/2) f_{r,q}` is self-adjoint in the sense of Paper I. -/
theorem selfAdjoint_weylSymbol (hA : IsSelfAdjoint A) :
    SymbolSelfAdjoint (weylSymbol γ (exactCoeff T₁ T₂ A φ₀)) := by
  intro p
  simp only [weylSymbol, exactCoeff_neg hT h₁ h₂ φ₀ hA p, map_mul, conj_e, ← mul_assoc,
    ← e_add, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  congr 2; ring

end Covariance

/-! ### The two-dimensional Weyl series -/

/-- `‖op2 α R‖ ≤ ∑ |R_{r,q}|`. -/
theorem norm_op2_le (α : ℝ) {R : Symbol} (hR : SymbolSummable R) :
    ‖op2 α R‖ ≤ ∑' p, ‖R p‖ := by
  refine tsum_of_norm_bounded hR.hasSum (fun p => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_W2_le _ _ _)

lemma inner_delta_left {ι : Type*} [DecidableEq ι] (i : ι) (u : L2 ι) :
    ⟪delta i, u⟫_ℂ = u i := by
  rw [delta, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, one_mul, mul_one]

set_option maxHeartbeats 800000 in
/-- Matrix entries of the two-dimensional Weyl series:
`⟪δ_j, op2 α R δ_l⟫ = R_{l-j} e(α m₁m₂/2 + α m₂ j₁)`, `m = l - j`. -/
theorem inner_delta_op2 (α : ℝ) {R : Symbol} (hR : SymbolSummable R) (j l : ℤ × ℤ) :
    ⟪delta j, op2 α R (delta l)⟫_ℂ =
      R (l - j) * e (α * (l - j).1 * (l - j).2 / 2 + (l - j).2 * j.1 * α) := by
  have hs := summable_op2 α hR
  have h1 : op2 α R (delta l) = ∑' p : ℤ × ℤ, R p • W2 α p.1 p.2 (delta l) :=
    (ContinuousLinearMap.apply ℂ (L2 (ℤ × ℤ)) (delta l)).map_tsum hs
  have hs' : Summable fun p : ℤ × ℤ => R p • W2 α p.1 p.2 (delta l) :=
    (ContinuousLinearMap.apply ℂ (L2 (ℤ × ℤ)) (delta l)).summable hs
  rw [h1, ← innerSL_apply_apply ℂ, (innerSL ℂ (delta j)).map_tsum hs']
  simp only [innerSL_apply_apply, inner_smul_right, inner_delta_left, W2_apply]
  rw [tsum_eq_single (l - j)]
  · rw [show j + ((l - j).1, (l - j).2) = l by ext <;> simp]
    simp only [delta, lp.single_apply_self, mul_one]
  · intro p hp
    have : j + (p.1, p.2) ≠ l := fun h => hp (by rw [← h]; ext <;> simp)
    simp only [delta, lp.single_apply_ne _ _ _ this, mul_zero]

/-- Two bounded operators on `ℓ²(ι)` agreeing on all `δ_i` are equal. -/
lemma clm_ext_delta {ι : Type*} [DecidableEq ι] {T T' : L2 ι →L[ℂ] L2 ι}
    (h : ∀ i, T (delta i) = T' (delta i)) : T = T' := by
  ext1 u
  have hu := lp.hasSum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num) u
  have hsingle : ∀ i, lp.single 2 i (u i) = u i • delta i := by
    intro i; rw [delta, ← lp.single_smul, smul_eq_mul, mul_one]
  simp_rw [hsingle] at hu
  have h1 := hu.mapL T
  have h2 := hu.mapL T'
  simp only [map_smul] at h1 h2
  simp only [h] at h1
  exact h1.unique h2

lemma L2_ext_inner {ι : Type*} [DecidableEq ι] {u v : L2 ι}
    (h : ∀ i, ⟪delta i, u⟫_ℂ = ⟪delta i, v⟫_ℂ) : u = v := by
  ext i; simpa [inner_delta_left] using h i

/-! ### The main identity -/

/-- **The exact interaction is the two-dimensional Weyl series** (§3 and §4.2,
`eq:full-lattice-generators`).  Let `b` be a Hilbert basis of `H` with `b m = S_m φ₀`, and
`Φ = b.repr.symm : ℓ²(ℤ²) → H` the unitary with `Φ δ_m = φ_m`.  If `A` commutes with the magnetic
translations and its exact coefficients `f` are absolutely summable, then
`Φ⁻¹ A Φ = op2 α (weylSymbol γ f)` with `α = freq γ = -γ`, i.e. `= ∑ c_{r,q} W̃_{r,q}` with
`c_{r,q} = e^{πiγrq} f_{r,q}`.  No relabelling of indices is needed: the matrix entries on both
sides are `e(-γ j₁ (l₂ - j₂)) f_{l-j}`. -/
theorem exact_interaction_eq_op2 {γ : ℝ} {T₁ T₂ : unitary (H →L[ℂ] H)}
    (hT : T₁ * T₂ = phaseU H γ * (T₂ * T₁)) {A : H →L[ℂ] H}
    (h₁ : Commute A (T₁ : H →L[ℂ] H)) (h₂ : Commute A (T₂ : H →L[ℂ] H)) {φ₀ : H}
    (b : HilbertBasis (ℤ × ℤ) ℂ H) (hb : ∀ m, b m = (magS T₁ T₂ m : H →L[ℂ] H) φ₀)
    (hf : SymbolSummable (exactCoeff T₁ T₂ A φ₀)) :
    (b.repr.toContinuousLinearEquiv : H →L[ℂ] L2 (ℤ × ℤ)) ∘L A ∘L
        (b.repr.symm.toContinuousLinearEquiv : L2 (ℤ × ℤ) →L[ℂ] H) =
      op2 (freq γ) (weylSymbol γ (exactCoeff T₁ T₂ A φ₀)) := by
  have hc : SymbolSummable (weylSymbol γ (exactCoeff T₁ T₂ A φ₀)) := by
    have hn : ∀ p, ‖weylSymbol γ (exactCoeff T₁ T₂ A φ₀) p‖ = ‖exactCoeff T₁ T₂ A φ₀ p‖ := by
      intro p; simp [weylSymbol]
    unfold SymbolSummable; simp_rw [hn]; exact hf
  refine clm_ext_delta fun l => L2_ext_inner fun j => ?_
  rw [inner_delta_op2 _ hc, inner_delta_left]
  change (b.repr (A (b.repr.symm (delta l)))) j = _
  rw [delta, b.repr_symm_single, b.repr_apply_apply, hb, hb, inner_magS_exact hT h₁ h₂,
    weylSymbol, freq, show ∀ a b c : ℂ, a * b * c = b * (a * c) from fun a b c => by ring,
    ← e_add]
  rw [mul_comm]
  congr 2
  try simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

/-- **Norm bound.** Under the hypotheses of `exact_interaction_eq_op2`,
`‖A‖ ≤ ∑_{r,q} |f_{r,q}|`. -/
theorem norm_le_tsum_exactCoeff {γ : ℝ} {T₁ T₂ : unitary (H →L[ℂ] H)}
    (hT : T₁ * T₂ = phaseU H γ * (T₂ * T₁)) {A : H →L[ℂ] H}
    (h₁ : Commute A (T₁ : H →L[ℂ] H)) (h₂ : Commute A (T₂ : H →L[ℂ] H)) {φ₀ : H}
    (b : HilbertBasis (ℤ × ℤ) ℂ H) (hb : ∀ m, b m = (magS T₁ T₂ m : H →L[ℂ] H) φ₀)
    (hf : SymbolSummable (exactCoeff T₁ T₂ A φ₀)) :
    ‖A‖ ≤ ∑' p, ‖exactCoeff T₁ T₂ A φ₀ p‖ := by
  have hc : SymbolSummable (weylSymbol γ (exactCoeff T₁ T₂ A φ₀)) := by
    have hn : ∀ p, ‖weylSymbol γ (exactCoeff T₁ T₂ A φ₀) p‖ = ‖exactCoeff T₁ T₂ A φ₀ p‖ := by
      intro p; simp [weylSymbol]
    unfold SymbolSummable; simp_rw [hn]; exact hf
  have hA : A = (b.repr.symm.toContinuousLinearEquiv : L2 (ℤ × ℤ) →L[ℂ] H) ∘L
      op2 (freq γ) (weylSymbol γ (exactCoeff T₁ T₂ A φ₀)) ∘L
      (b.repr.toContinuousLinearEquiv : H →L[ℂ] L2 (ℤ × ℤ)) := by
    rw [← exact_interaction_eq_op2 hT h₁ h₂ b hb hf]
    ext x; simp
  have hn : ∀ p, ‖weylSymbol γ (exactCoeff T₁ T₂ A φ₀) p‖ = ‖exactCoeff T₁ T₂ A φ₀ p‖ := by
    intro p; simp [weylSymbol]
  calc ‖A‖ ≤ ‖(b.repr.symm.toContinuousLinearEquiv : L2 (ℤ × ℤ) →L[ℂ] H)‖ *
        (‖op2 (freq γ) (weylSymbol γ (exactCoeff T₁ T₂ A φ₀))‖ *
          ‖(b.repr.toContinuousLinearEquiv : H →L[ℂ] L2 (ℤ × ℤ))‖) := by
        conv_lhs => rw [hA]
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ((∑' p, ‖weylSymbol γ (exactCoeff T₁ T₂ A φ₀) p‖) * 1) := by
        gcongr
        · exact b.repr.symm.toLinearIsometry.norm_toContinuousLinearMap_le
        · exact norm_op2_le _ hc
        · exact b.repr.toLinearIsometry.norm_toContinuousLinearMap_le
    _ = _ := by simp [hn]

end CMS
