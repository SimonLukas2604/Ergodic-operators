/-
# Symbol calculus for the scaled preparation  (paper §2.2)

Algebraic identities for the twisted product of Weyl symbols:
bilinearity, the unit, the anti-multiplicative involution `(R ⋆ S)^* = S^* ⋆ R^*`;
support rules in the hopping index; the projection `Π_{≥2}`; the hopping shifts
`U = δ_{(1,0)}`, `U^{-1} = δ_{(-1,0)}`, and the inverse `S^{-1}` of `K ↦ U ⋆ K` on positive
tails together with the exact weight gains `e^{-s}` used in Lemma 2.1.
Everything here is proved.
-/
import AnalyticPerturbationsAMO.Neumann

noncomputable section

open scoped ComplexConjugate

namespace AMO

variable {α s ℓ : ℝ}

/-! ### Bilinearity -/

lemma summable_tmul_term' {R S : Symbol} (hR : SymbolSummable R) (hS : SymbolSummable S)
    (p : ℤ × ℤ) : Summable fun p₁ => R p₁ * S (p - p₁) * wphase α p₁ (p - p₁) :=
  (summable_tmul_term le_rfl le_rfl (symbolSummable_iff_wsum_zero.1 hR)
    (symbolSummable_iff_wsum_zero.1 hS) p).of_norm

lemma tmul_add_left {R R' S : Symbol} (hR : SymbolSummable R) (hR' : SymbolSummable R')
    (hS : SymbolSummable S) : tmul α (R + R') S = tmul α R S + tmul α R' S := by
  funext p
  simp only [tmul, Pi.add_apply]
  rw [← (summable_tmul_term' hR hS p).tsum_add (summable_tmul_term' hR' hS p)]
  congr 1
  funext p₁
  ring

lemma tmul_add_right {R S S' : Symbol} (hR : SymbolSummable R) (hS : SymbolSummable S)
    (hS' : SymbolSummable S') : tmul α R (S + S') = tmul α R S + tmul α R S' := by
  funext p
  simp only [tmul, Pi.add_apply]
  rw [← (summable_tmul_term' hR hS p).tsum_add (summable_tmul_term' hR hS' p)]
  congr 1
  funext p₁
  ring

lemma tmul_smul_left (c : ℂ) (R S : Symbol) : tmul α (c • R) S = c • tmul α R S := by
  funext p
  simp only [tmul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1
  funext p₁
  ring

lemma tmul_smul_right (c : ℂ) (R S : Symbol) : tmul α R (c • S) = c • tmul α R S := by
  funext p
  simp only [tmul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1
  funext p₁
  ring

lemma tmul_neg_left (R S : Symbol) : tmul α (-R) S = -tmul α R S := by
  have := tmul_smul_left (α := α) (-1) R S
  simpa using this

lemma tmul_neg_right (R S : Symbol) : tmul α R (-S) = -tmul α R S := by
  have := tmul_smul_right (α := α) (-1) R S
  simpa using this

lemma tmul_sub_left {R R' S : Symbol} (hR : SymbolSummable R) (hR' : SymbolSummable R')
    (hS : SymbolSummable S) : tmul α (R - R') S = tmul α R S - tmul α R' S := by
  have hR'n : SymbolSummable (-R') := by simpa [SymbolSummable] using hR'
  rw [sub_eq_add_neg, tmul_add_left hR hR'n hS, tmul_neg_left, ← sub_eq_add_neg]

lemma tmul_sub_right {R S S' : Symbol} (hR : SymbolSummable R) (hS : SymbolSummable S)
    (hS' : SymbolSummable S') : tmul α R (S - S') = tmul α R S - tmul α R S' := by
  have hS'n : SymbolSummable (-S') := by simpa [SymbolSummable] using hS'
  rw [sub_eq_add_neg, tmul_add_right hR hS hS'n, tmul_neg_right, ← sub_eq_add_neg]

/-! ### The unit -/

@[simp] lemma wphase_zero_left (α : ℝ) (p : ℤ × ℤ) : wphase α 0 p = 1 := by simp [wphase]
@[simp] lemma wphase_zero_right (α : ℝ) (p : ℤ × ℤ) : wphase α p 0 = 1 := by simp [wphase]

lemma one_tmul (R : Symbol) : tmul α one R = R := by
  funext p
  rw [tmul, tsum_eq_single 0]
  · simp [one]
  · intro p₁ hp₁
    simp [one, Pi.single_apply, hp₁]

lemma tmul_one (R : Symbol) : tmul α R one = R := by
  funext p
  rw [tmul, tsum_eq_single p]
  · simp [one]
  · intro p₁ hp₁
    have : p - p₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hp₁)
    simp [one, Pi.single_apply, this]

/-! ### The involution -/

lemma sstar_add (R R' : Symbol) : sstar (R + R') = sstar R + sstar R' := by
  funext p; simp [sstar]

lemma sstar_sub (R R' : Symbol) : sstar (R - R') = sstar R - sstar R' := by
  funext p; simp [sstar]

lemma sstar_smul (c : ℂ) (R : Symbol) : sstar (c • R) = conj c • sstar R := by
  funext p; simp [sstar]

lemma sstar_sstar (R : Symbol) : sstar (sstar R) = R := by
  funext p; simp [sstar]

lemma sstar_one : sstar one = one := by
  funext p
  simp only [sstar, one, Pi.single_apply, neg_eq_zero]
  split_ifs <;> simp

lemma sstar_eq_iff (R : Symbol) : sstar R = R ↔ SymbolSelfAdjoint R := by
  constructor
  · intro h p
    have := congrFun h (-p)
    simp only [sstar, neg_neg] at this
    exact this.symm
  · intro h
    funext p
    simp only [sstar]
    have := h (-p)
    rw [neg_neg] at this
    exact this.symm

/-- `(R ⋆ S)^* = S^* ⋆ R^*`. -/
theorem sstar_tmul (R S : Symbol) : sstar (tmul α R S) = tmul α (sstar S) (sstar R) := by
  funext p
  simp only [sstar, tmul]
  rw [Complex.conj_tsum]
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p₁ => p + p₁, invFun := fun p₂ => p₂ - p,
      left_inv := fun x => by simp, right_inv := fun x => by simp }
  conv_rhs => rw [← e.tsum_eq]
  congr 1
  funext p₁
  simp only [e, Equiv.coe_fn_mk, map_mul]
  have h1 : -(p + p₁) = -p - p₁ := by abel
  have h2 : -(p - (p + p₁)) = p₁ := by abel
  have h3 : p - (p + p₁) = -p₁ := by abel
  rw [h1, h2, h3]
  have hph : conj (wphase α p₁ (-p - p₁)) = wphase α (p + p₁) (-p₁) := by
    unfold wphase
    rw [conj_e]
    congr 1
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
      Prod.snd_neg, Int.cast_sub, Int.cast_add, Int.cast_neg]
    ring
  rw [hph]
  ring

/-! ### Hopping supports -/

/-- `R` is supported on hopping indices `≥ n`. -/
def HopGE (R : Symbol) (n : ℤ) : Prop := ∀ p : ℤ × ℤ, p.1 < n → R p = 0

/-- `R` is supported on hopping indices `≤ n`. -/
def HopLE (R : Symbol) (n : ℤ) : Prop := ∀ p : ℤ × ℤ, n < p.1 → R p = 0

lemma tmul_eq_zero_of {R S : Symbol} {p : ℤ × ℤ}
    (h : ∀ p₁, R p₁ = 0 ∨ S (p - p₁) = 0) : tmul α R S p = 0 := by
  rw [tmul]
  convert tsum_zero with p₁
  rcases h p₁ with h | h <;> simp [h]

lemma HopGE.tmul {R S : Symbol} {m n : ℤ} (hR : HopGE R m) (hS : HopGE S n) :
    HopGE (tmul α R S) (m + n) := by
  intro p hp
  refine tmul_eq_zero_of fun p₁ => ?_
  by_cases h : p₁.1 < m
  · exact Or.inl (hR p₁ h)
  · right; apply hS; simp only [Prod.fst_sub]; omega

lemma HopLE.tmul {R S : Symbol} {m n : ℤ} (hR : HopLE R m) (hS : HopLE S n) :
    HopLE (tmul α R S) (m + n) := by
  intro p hp
  refine tmul_eq_zero_of fun p₁ => ?_
  by_cases h : m < p₁.1
  · exact Or.inl (hR p₁ h)
  · right; apply hS; simp only [Prod.fst_sub]; omega

lemma HopGE.sstar {R : Symbol} {n : ℤ} (h : HopGE R n) : HopLE (sstar R) (-n) := by
  intro p hp
  simp only [AMO.sstar, map_eq_zero]
  exact h _ (by simp only [Prod.fst_neg]; omega)

lemma HopLE.sstar {R : Symbol} {n : ℤ} (h : HopLE R n) : HopGE (sstar R) (-n) := by
  intro p hp
  simp only [AMO.sstar, map_eq_zero]
  exact h _ (by simp only [Prod.fst_neg]; omega)

lemma HopGE.add {R S : Symbol} {n : ℤ} (hR : HopGE R n) (hS : HopGE S n) : HopGE (R + S) n :=
  fun p hp => by simp [hR p hp, hS p hp]

lemma HopGE.sub {R S : Symbol} {n : ℤ} (hR : HopGE R n) (hS : HopGE S n) : HopGE (R - S) n :=
  fun p hp => by simp [hR p hp, hS p hp]

lemma HopGE.smul {R : Symbol} {n : ℤ} (c : ℂ) (hR : HopGE R n) : HopGE (c • R) n :=
  fun p hp => by simp [hR p hp]

lemma HopLE.add {R S : Symbol} {n : ℤ} (hR : HopLE R n) (hS : HopLE S n) : HopLE (R + S) n :=
  fun p hp => by simp [hR p hp, hS p hp]

lemma HopLE.smul {R : Symbol} {n : ℤ} (c : ℂ) (hR : HopLE R n) : HopLE (c • R) n :=
  fun p hp => by simp [hR p hp]

lemma HopGE.mono {R : Symbol} {m n : ℤ} (h : HopGE R n) (hmn : m ≤ n) : HopGE R m :=
  fun p hp => h p (by omega)

lemma HopLE.mono {R : Symbol} {m n : ℤ} (h : HopLE R m) (hmn : m ≤ n) : HopLE R n :=
  fun p hp => h p (by omega)

/-! ### The projection `Π_{≥2}` -/

/-- `Π_{≥2}`: keep hopping indices `≥ 2`. -/
def P2 (R : Symbol) : Symbol := fun p => if 2 ≤ p.1 then R p else 0

lemma P2_add (R S : Symbol) : P2 (R + S) = P2 R + P2 S := by
  funext p; simp only [P2, Pi.add_apply]; split_ifs <;> simp

lemma P2_sub (R S : Symbol) : P2 (R - S) = P2 R - P2 S := by
  funext p; simp only [P2, Pi.sub_apply]; split_ifs <;> simp

lemma P2_smul (c : ℂ) (R : Symbol) : P2 (c • R) = c • P2 R := by
  funext p; simp only [P2, Pi.smul_apply]; split_ifs <;> simp

lemma P2_of_HopGE {R : Symbol} (h : HopGE R 2) : P2 R = R := by
  funext p; simp only [P2]; split_ifs with hp
  · rfl
  · exact (h p (by omega)).symm

lemma P2_of_HopLE {R : Symbol} (h : HopLE R 1) : P2 R = 0 := by
  funext p; simp only [P2, Pi.zero_apply]; split_ifs with hp
  · exact h p (by omega)
  · rfl

lemma P2_P2 (R : Symbol) : P2 (P2 R) = P2 R := by
  funext p; simp only [P2]; split_ifs <;> rfl

lemma HopGE_P2 (R : Symbol) : HopGE (P2 R) 2 := fun p hp => by
  simp only [P2]; rw [if_neg (by omega)]

lemma HopLE_of_P2 {R : Symbol} (h : P2 R = 0) : HopLE R 1 := fun p hp => by
  have := congrFun h p
  simp only [P2, Pi.zero_apply] at this
  rwa [if_pos (by omega)] at this

lemma norm_P2_le (R : Symbol) (p : ℤ × ℤ) : ‖P2 R p‖ ≤ ‖R p‖ := by
  simp only [P2]; split_ifs <;> simp

lemma WSum.P2 {R : Symbol} (h : WSum s ℓ R) : WSum s ℓ (P2 R) :=
  h.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
    (fun p => mul_le_mul_of_nonneg_right (norm_P2_le R p) (wt_pos p).le)

lemma wnorm_P2_le {R : Symbol} (h : WSum s ℓ R) : wnorm s ℓ (P2 R) ≤ wnorm s ℓ R :=
  h.P2.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_right (norm_P2_le R p) (wt_pos p).le) h

/-! ### Hopping shifts -/

/-- The symbol of `U`. -/
def u1 : Symbol := Pi.single (1, 0) 1

/-- The symbol of `U^{-1}`. -/
def um1 : Symbol := Pi.single (-1, 0) 1

lemma u1_tmul (K : Symbol) (p : ℤ × ℤ) :
    tmul α u1 K p = K (p - (1, 0)) * wphase α (1, 0) (p - (1, 0)) := by
  rw [tmul, tsum_eq_single (1, 0)]
  · simp [u1]
  · intro p₁ hp₁
    simp [u1, Pi.single_apply, hp₁]

lemma um1_tmul (K : Symbol) (p : ℤ × ℤ) :
    tmul α um1 K p = K (p + (1, 0)) * wphase α (-1, 0) (p + (1, 0)) := by
  rw [tmul, tsum_eq_single (-1, 0)]
  · simp only [um1, Pi.single_eq_same, one_mul]
    rw [show p - (-1, 0) = p + (1, 0) by ext <;> simp]
  · intro p₁ hp₁
    simp [um1, Pi.single_apply, hp₁]

lemma HopGE.u1_tmul {K : Symbol} {n : ℤ} (h : HopGE K n) :
    HopGE (AMO.tmul α u1 K) (n + 1) := by
  intro p hp
  rw [AMO.u1_tmul, h _ (by simp only [Prod.fst_sub]; omega), zero_mul]

lemma wt_shift (hs : 0 ≤ s) {p : ℤ × ℤ} (hp : 0 ≤ p.1) :
    wt s ℓ (p + (1, 0)) = Real.exp s * wt s ℓ p := by
  unfold wt
  rw [← Real.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, add_zero, Int.cast_add, Int.cast_one, Int.cast_zero]
  have h0 : (0 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hp
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (p.1 : ℝ) + 1 by linarith), abs_of_nonneg h0]
  ring

/-- The inverse of `K ↦ U ⋆ K` on positive tails:
`(S^{-1} D)_p = D_{p + (1,0)} \overline{φ((1,0), p)}` for `p₁ ≥ 1`. -/
def Sinv (α : ℝ) (D : Symbol) : Symbol :=
  fun p => if 1 ≤ p.1 then D (p + (1, 0)) * conj (wphase α (1, 0) p) else 0

lemma HopGE_Sinv (D : Symbol) : HopGE (Sinv α D) 1 := fun p hp => by
  simp only [Sinv]; rw [if_neg (by omega)]

lemma wphase_mul_conj (α : ℝ) (p p' : ℤ × ℤ) : wphase α p p' * conj (wphase α p p') = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_wphase]; simp

lemma conj_mul_wphase (α : ℝ) (p p' : ℤ × ℤ) : conj (wphase α p p') * wphase α p p' = 1 := by
  rw [mul_comm, wphase_mul_conj]

/-- `U ⋆ S^{-1} D = Π_{≥2} D`. -/
lemma u1_tmul_Sinv (D : Symbol) : tmul α u1 (Sinv α D) = P2 D := by
  funext p
  rw [u1_tmul]
  simp only [Sinv, P2, Prod.fst_sub]
  by_cases hp : 2 ≤ p.1
  · rw [if_pos (by omega), if_pos hp, sub_add_cancel, mul_assoc, conj_mul_wphase, mul_one]
  · rw [if_neg (by omega), if_neg hp, zero_mul]

/-- `S^{-1}(U ⋆ K) = K` for `K` supported on hopping indices `≥ 1`. -/
lemma Sinv_u1_tmul {K : Symbol} (hK : HopGE K 1) : Sinv α (tmul α u1 K) = K := by
  funext p
  simp only [Sinv]
  split_ifs with hp
  · rw [u1_tmul, add_sub_cancel_right, mul_assoc, wphase_mul_conj, mul_one]
  · exact (hK p (by omega)).symm

lemma Sinv_add (D D' : Symbol) : Sinv α (D + D') = Sinv α D + Sinv α D' := by
  funext p; simp only [Sinv, Pi.add_apply]; split_ifs <;> ring

lemma Sinv_sub (D D' : Symbol) : Sinv α (D - D') = Sinv α D - Sinv α D' := by
  funext p; simp only [Sinv, Pi.sub_apply]; split_ifs <;> ring

lemma Sinv_smul (c : ℂ) (D : Symbol) : Sinv α (c • D) = c • Sinv α D := by
  funext p; simp only [Sinv, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `‖S^{-1} D‖_{s,ℓ} ≤ e^{-s} ‖D‖_{s,ℓ}`. -/
lemma Sinv_wsum (hs : 0 ≤ s) {D : Symbol} (hD : WSum s ℓ D) :
    WSum s ℓ (Sinv α D) ∧ wnorm s ℓ (Sinv α D) ≤ Real.exp (-s) * wnorm s ℓ D := by
  let e : ℤ × ℤ ≃ ℤ × ℤ := Equiv.addRight (1, 0)
  have hshift : Summable fun p => ‖D (p + (1, 0))‖ * wt s ℓ (p + (1, 0)) :=
    (e.summable_iff (f := fun p => ‖D p‖ * wt s ℓ p)).2 hD
  have hb : ∀ p, ‖Sinv α D p‖ * wt s ℓ p ≤
      Real.exp (-s) * (‖D (p + (1, 0))‖ * wt s ℓ (p + (1, 0))) := by
    intro p
    simp only [Sinv]
    split_ifs with hp
    · rw [norm_mul, Complex.norm_conj, norm_wphase, mul_one, wt_shift hs (by omega)]
      have hexp : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
      exact le_of_eq (by linear_combination (-(‖D (p + (1, 0))‖ * wt s ℓ p)) * hexp)
    · simp only [norm_zero, zero_mul]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) (wt_pos _).le)
  have hsum : WSum s ℓ (Sinv α D) :=
    (hshift.mul_left _).of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le) hb
  refine ⟨hsum, ?_⟩
  rw [wnorm_eq, wnorm_eq]
  calc ∑' p, ‖Sinv α D p‖ * wt s ℓ p
      ≤ ∑' p, Real.exp (-s) * (‖D (p + (1, 0))‖ * wt s ℓ (p + (1, 0))) :=
        hsum.tsum_le_tsum hb (hshift.mul_left _)
    _ = Real.exp (-s) * ∑' p, ‖D p‖ * wt s ℓ p := by
        rw [tsum_mul_left]
        congr 1
        exact e.tsum_eq (fun p => ‖D p‖ * wt s ℓ p)

/-- `‖Π_{≥2}(U^{-1} ⋆ K)‖_{s,ℓ} ≤ e^{-s} ‖K‖_{s,ℓ}`. -/
lemma P2_um1_wsum (hs : 0 ≤ s) {K : Symbol} (hK : WSum s ℓ K) :
    WSum s ℓ (P2 (tmul α um1 K)) ∧
      wnorm s ℓ (P2 (tmul α um1 K)) ≤ Real.exp (-s) * wnorm s ℓ K := by
  let e : ℤ × ℤ ≃ ℤ × ℤ := Equiv.addRight (1, 0)
  have hshift : Summable fun p => ‖K (p + (1, 0))‖ * wt s ℓ (p + (1, 0)) :=
    (e.summable_iff (f := fun p => ‖K p‖ * wt s ℓ p)).2 hK
  have hb : ∀ p, ‖P2 (tmul α um1 K) p‖ * wt s ℓ p ≤
      Real.exp (-s) * (‖K (p + (1, 0))‖ * wt s ℓ (p + (1, 0))) := by
    intro p
    simp only [P2]
    split_ifs with hp
    · rw [um1_tmul, norm_mul, norm_wphase, mul_one, wt_shift hs (by omega)]
      have hexp : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
      exact le_of_eq (by linear_combination (-(‖K (p + (1, 0))‖ * wt s ℓ p)) * hexp)
    · simp only [norm_zero, zero_mul]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) (wt_pos _).le)
  have hsum : WSum s ℓ (P2 (tmul α um1 K)) :=
    (hshift.mul_left _).of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le) hb
  refine ⟨hsum, ?_⟩
  rw [wnorm_eq, wnorm_eq]
  calc ∑' p, ‖P2 (tmul α um1 K) p‖ * wt s ℓ p
      ≤ ∑' p, Real.exp (-s) * (‖K (p + (1, 0))‖ * wt s ℓ (p + (1, 0))) :=
        hsum.tsum_le_tsum hb (hshift.mul_left _)
    _ = Real.exp (-s) * ∑' p, ‖K p‖ * wt s ℓ p := by
        rw [tsum_mul_left]
        congr 1
        exact e.tsum_eq (fun p => ‖K p‖ * wt s ℓ p)

lemma single_wsum (p₀ : ℤ × ℤ) (c : ℂ) : WSum s ℓ (Pi.single p₀ c) := by
  unfold WSum
  apply summable_of_ne_finset_zero (s := {p₀})
  intro p hp
  simp only [Finset.mem_singleton] at hp
  simp [Pi.single_apply, hp]

lemma wnorm_single (p₀ : ℤ × ℤ) (c : ℂ) : wnorm s ℓ (Pi.single p₀ c) = ‖c‖ * wt s ℓ p₀ := by
  rw [wnorm_eq, tsum_eq_single p₀]
  · simp
  · intro p hp
    simp [Pi.single_apply, hp]

lemma wnorm_u1 : wnorm s ℓ u1 = Real.exp s := by
  rw [u1, wnorm_single]; simp [wt]

lemma wnorm_um1 : wnorm s ℓ um1 = Real.exp s := by
  rw [um1, wnorm_single]; simp [wt]

lemma HopGE_u1 : HopGE u1 1 := fun p hp => by
  simp only [u1, Pi.single_apply]
  rw [if_neg (by rintro rfl; simp at hp)]

lemma HopLE_u1 : HopLE u1 1 := fun p hp => by
  simp only [u1, Pi.single_apply]
  rw [if_neg (by rintro rfl; simp at hp)]

lemma HopGE_um1 : HopGE um1 (-1) := fun p hp => by
  simp only [um1, Pi.single_apply]
  rw [if_neg (by rintro rfl; simp at hp)]

lemma HopLE_um1 : HopLE um1 (-1) := fun p hp => by
  simp only [um1, Pi.single_apply]
  rw [if_neg (by rintro rfl; simp at hp)]

lemma sstar_u1 : sstar u1 = um1 := by
  funext p
  simp only [sstar, u1, um1, Pi.single_apply]
  by_cases h : p = (-1, 0)
  · subst h; simp
  · rw [if_neg h, if_neg (by intro h'; apply h; rw [← neg_neg p, h']; rfl)]; simp

lemma sstar_um1 : sstar um1 = u1 := by
  rw [← sstar_u1, sstar_sstar]

/-! ### Associativity -/

/-- The phase cocycle identity `φ(b,c) φ(b+c,d) = φ(c,d) φ(b,c+d)`. -/
lemma wphase_cocycle (α : ℝ) (b c d : ℤ × ℤ) :
    wphase α b c * wphase α (b + c) d = wphase α c d * wphase α b (c + d) := by
  unfold wphase
  rw [← e_add, ← e_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

lemma bdd_of_summable {T : Symbol} (hT : SymbolSummable T) (p : ℤ × ℤ) :
    ‖T p‖ ≤ ∑' q, ‖T q‖ :=
  hT.le_tsum p (fun _ _ => norm_nonneg _)

/-- **Associativity of the twisted product.** -/
theorem tmul_assoc {R S T : Symbol} (hR : SymbolSummable R) (hS : SymbolSummable S)
    (hT : SymbolSummable T) : tmul α (tmul α R S) T = tmul α R (tmul α S T) := by
  funext p
  -- the triple sum indexed by `(b, c)`
  set G : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun z =>
    R z.1 * S z.2 * T (p - z.1 - z.2) * (wphase α z.1 z.2 * wphase α (z.1 + z.2) (p - z.1 - z.2))
    with hG
  have hGs : Summable fun z => ‖G z‖ := by
    have hRS : Summable fun z : (ℤ × ℤ) × (ℤ × ℤ) => ‖R z.1‖ * ‖S z.2‖ :=
      hR.mul_of_nonneg hS (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    refine (hRS.mul_right (∑' q, ‖T q‖)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    simp only [hG, norm_mul, norm_wphase, mul_one]
    exact mul_le_mul_of_nonneg_left (bdd_of_summable hT _) (by positivity)
  have hG' : Summable G := hGs.of_norm
  -- left-hand side
  have hL : tmul α (tmul α R S) T p = ∑' b, ∑' c, G (b, c) := by
    let e : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) :=
      { toFun := fun z => (z.2, z.1 - z.2), invFun := fun z => (z.1 + z.2, z.1),
        left_inv := fun z => by simp, right_inv := fun z => by simp }
    have hGe : Summable (G ∘ e) := (e.summable_iff).2 hG'
    rw [← hG'.tsum_prod, ← e.tsum_eq]
    show _ = ∑' c, (G ∘ e) c
    rw [hGe.tsum_prod]
    unfold tmul
    congr 1
    funext a
    rw [← tsum_mul_right, ← tsum_mul_right]
    congr 1
    funext b
    simp only [Function.comp_apply, e, Equiv.coe_fn_mk, hG]
    rw [show p - b - (a - b) = p - a by abel, add_sub_cancel]
    ring
  -- right-hand side
  have hRhs : tmul α R (tmul α S T) p = ∑' b, ∑' c, G (b, c) := by
    unfold tmul
    congr 1
    funext b
    rw [← tsum_mul_left, ← tsum_mul_right]
    congr 1
    funext c
    simp only [hG]
    rw [show p - b - c = p - b - c from rfl]
    have hcoc := wphase_cocycle α b c (p - b - c)
    rw [show c + (p - b - c) = p - b by abel] at hcoc
    rw [hcoc]
    ring
  rw [hL, hRhs]

end AMO
