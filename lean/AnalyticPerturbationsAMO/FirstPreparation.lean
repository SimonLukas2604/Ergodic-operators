/-
# Exact Jacobi preparation of `H - E`  (paper §2.2, eq. `d-eq:firstprep`)

For `H = U + U^{-1} + η(V + V^{-1}) + R` with `R` self-adjoint and small in `𝒲_{s,ℓ}`, and an
energy `E` with `e^{-s}(2|η|e^ℓ + |E|) + e^{-2s} ≤ 1/4`, Lemma 2.1 produces an **exact,
analytic, exponentially local Jacobi preparation**
  `H_x - E = Q_x^* J_x Q_x`,  `J = a U + a^♯(· - α) U^{-1} + b`,
packaged as a `JacobiPrep` (the structure used in the main theorems), with `a, b` analytic and
`1`-periodic on the strip `|Im z| < ℓ/2π`, `|a - 1| ≤ 1/4`, `b` real, and the analytic square
root `c = (a a^♯)^{1/2}` with `c = |a|` on the real axis.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.FourierSeries
import AnalyticPerturbationsAMO.ScaledPreparation

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open Complex L2

namespace AMO

/-! ### Linearity of coefficient functions -/

lemma coefFn_add {s ℓ : ℝ} (hs : 0 ≤ s) {R S : Symbol} (hR : WSum s ℓ R) (hS : WSum s ℓ S)
    (α : ℝ) (r : ℤ) {z : ℂ} (hz : |z.im| ≤ ℓ / (2 * Real.pi)) :
    coefFn α (R + S) r z = coefFn α R r z + coefFn α S r z := by
  unfold coefFn fser
  have h1 := (summable_fiber hs hR r).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => norm_fser_term_le (d := fun q => R (r, q)) (β := fun q => α * r * q / 2)
      (by norm_num : |(1 : ℤ)| ≤ 1) q hz)
  have h2 := (summable_fiber hs hS r).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => norm_fser_term_le (d := fun q => S (r, q)) (β := fun q => α * r * q / 2)
      (by norm_num : |(1 : ℤ)| ≤ 1) q hz)
  rw [← h1.of_norm.tsum_add h2.of_norm]
  congr 1; funext q
  simp only [Pi.add_apply]; ring

lemma coefFn_of_zero_fiber {α : ℝ} {R : Symbol} {r : ℤ} (h : ∀ q, R (r, q) = 0) (z : ℂ) :
    coefFn α R r z = 0 := by
  unfold coefFn fser
  simp [h]

lemma coefFn_single (α : ℝ) (r : ℤ) (c : ℂ) (z : ℂ) : coefFn α (Pi.single (r, 0) c) r z = c := by
  unfold coefFn fser
  rw [tsum_eq_single 0]
  · simp [ec]
  · intro q hq
    simp [Pi.single_apply, hq]

/-! ### The phase coefficient `w = v - E` -/

/-- The symbol of `η(V + V^{-1}) - E`. -/
def wsym (η E : ℝ) : Symbol :=
  Pi.single (0, 1) (η : ℂ) + Pi.single (0, -1) (η : ℂ) - Pi.single ((0 : ℤ), (0 : ℤ)) (E : ℂ)

lemma wsym_wsum (s ℓ η E : ℝ) : WSum s ℓ (wsym η E) := by
  unfold WSum
  apply summable_of_ne_finset_zero (s := {(0, 1), (0, -1), (0, 0)})
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  simp [wsym, Pi.single_apply, hp.1, hp.2.1, hp.2.2]

lemma wsym_hop (η E : ℝ) : HopGE (wsym η E) 0 ∧ HopLE (wsym η E) 0 := by
  constructor
  · intro p hp
    obtain ⟨a, b⟩ := p
    simp only at hp
    simp only [wsym, Pi.add_apply, Pi.sub_apply, Pi.single_apply, Prod.mk.injEq]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · intro p hp
    obtain ⟨a, b⟩ := p
    simp only at hp
    simp only [wsym, Pi.add_apply, Pi.sub_apply, Pi.single_apply, Prod.mk.injEq]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp

lemma sstar_single (p : ℤ × ℤ) (c : ℂ) : sstar (Pi.single p c) = Pi.single (-p) (conj c) := by
  funext q
  simp only [sstar, Pi.single_apply, neg_eq_iff_eq_neg]
  split_ifs <;> simp

lemma wsym_sa (η E : ℝ) : SymbolSelfAdjoint (wsym η E) := by
  rw [← sstar_eq_iff]
  unfold wsym
  rw [sstar_sub, sstar_add, sstar_single, sstar_single, sstar_single]
  simp only [Complex.conj_ofReal, Prod.neg_mk, neg_zero]
  rw [show ((0 : ℤ), -(-1 : ℤ)) = (0, 1) by simp]
  abel

lemma wnorm_wsym_le (s ℓ η E : ℝ) : wnorm s ℓ (wsym η E) ≤ 2 * |η| * Real.exp ℓ + |E| := by
  set A : Symbol := Pi.single (0, 1) (η : ℂ)
  set B : Symbol := Pi.single (0, -1) (η : ℂ)
  set C : Symbol := Pi.single ((0 : ℤ), (0 : ℤ)) (E : ℂ)
  have hw : wsym η E = A + B - C := rfl
  have hA : WSum s ℓ A := single_wsum _ _
  have hB : WSum s ℓ B := single_wsum _ _
  have hC : WSum s ℓ C := single_wsum _ _
  have hle : ∀ p, ‖wsym η E p‖ * wt s ℓ p ≤
      (‖A p‖ * wt s ℓ p + ‖B p‖ * wt s ℓ p) + ‖C p‖ * wt s ℓ p := by
    intro p
    rw [← add_mul, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (wt_pos p).le
    rw [hw, Pi.sub_apply, Pi.add_apply]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  calc wnorm s ℓ (wsym η E)
      ≤ ∑' p, ((‖A p‖ * wt s ℓ p + ‖B p‖ * wt s ℓ p) + ‖C p‖ * wt s ℓ p) :=
        (wsym_wsum s ℓ η E).tsum_le_tsum hle ((hA.add hB).add hC)
    _ = wnorm s ℓ A + wnorm s ℓ B + wnorm s ℓ C := by
        rw [(hA.add hB).tsum_add hC, hA.tsum_add hB]; rfl
    _ = 2 * |η| * Real.exp ℓ + |E| := by
        rw [wnorm_single, wnorm_single, wnorm_single]
        simp [wt]
        ring

/-! ### The data of Lemma 2.1 for `J₀ = U + U^{-1} + η(V + V^{-1}) - E` -/

section Construction

variable (ω : Weights) (α η E : ℝ)

/-- Lemma 2.1 data with `a₀ = 1`, `c₀ = 1/4`, `w = η(V + V^{-1}) - E`. -/
def prepData (hc : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + |E|) +
    Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4) : ScaledPrep.Data ω where
  a0 := 1
  ha0 := one_pos
  c0 := 1 / 4
  hc0 := by norm_num
  hc1 := by norm_num
  w := ω.ofS (wsym η E) (wsym_wsum _ _ η E)
  w_ge := by rw [Weights.toS_ofS]; exact (wsym_hop η E).1
  w_le := by rw [Weights.toS_ofS]; exact (wsym_hop η E).2
  w_sa := by
    apply ω.toS_injective
    rw [Weights.toS_star, Weights.toS_ofS]
    exact (sstar_eq_iff _).2 (wsym_sa η E)
  hsmall := by
    rw [Weights.norm_ofS, div_one]
    have := wnorm_wsym_le ω.s ω.ℓ η E
    have h := mul_le_mul_of_nonneg_left this (Real.exp_pos (-ω.s)).le
    linarith

/-- The smallness threshold for `e^{-s}‖R‖_{s,ℓ}`. -/
def sig1 : ℝ := min (ScaledPrep.sig0 (1 / 4)) (1 / (4 * ScaledPrep.Cst (1 / 4)))

lemma Cst_quarter_pos : 0 < ScaledPrep.Cst (1 / 4) := by
  unfold ScaledPrep.Cst; norm_num

end Construction

/-! ### The analytic square root -/

lemma mem_slitPlane_of_close {p : ℂ} (h : ‖p - 1‖ < 1) : p ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : |(p - 1).re| ≤ ‖p - 1‖ := Complex.abs_re_le_norm _
  have : (p - 1).re = p.re - 1 := by simp
  rw [this] at h1
  linarith [(abs_le.1 h1).1]

lemma sqrt_normSq_cpow (z : ℂ) :
    (((z * conj z) : ℂ) ^ ((2 : ℂ)⁻¹)) = (‖z‖ : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : ((2 : ℂ)⁻¹) = ((2⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, ← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [← Real.rpow_natCast (‖z‖) 2, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- `f^♯(z) = \overline{f(\bar z)}` is analytic on a conjugation-invariant strip. -/
lemma analyticOnNhd_sharp {f : ℂ → ℂ} {w : ℝ} (hf : AnalyticOnNhd ℂ f (strip w)) :
    AnalyticOnNhd ℂ (fun z => conj (f (conj z))) (strip w) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_strip w)
  intro z hz
  have hz' : conj z ∈ strip w := by simpa [strip] using hz
  have h := ((hf _ hz').differentiableAt).conj_conj
  rw [Complex.conj_conj] at h
  exact h.differentiableWithinAt

/-- The analytic square root `c = (a a^♯)^{1/2}`. -/
def sqrtFn (a : ℂ → ℂ) (z : ℂ) : ℂ := (a z * conj (a (conj z))) ^ ((2 : ℂ)⁻¹)

section SqrtFn

variable {a : ℂ → ℂ} {w : ℝ}

lemma sqrtFn_ofReal (t : ℝ) : sqrtFn a t = ‖a t‖ := by
  unfold sqrtFn
  rw [Complex.conj_ofReal, sqrt_normSq_cpow]

lemma sqrtFn_base_close (hclose : ∀ z ∈ strip w, ‖a z - 1‖ ≤ 1 / 4) {z : ℂ} (hz : z ∈ strip w) :
    ‖a z * conj (a (conj z)) - 1‖ < 1 := by
  have hz' : conj z ∈ strip w := by simpa [strip] using hz
  have h1 := hclose z hz
  have h2 : ‖conj (a (conj z)) - 1‖ ≤ 1 / 4 := by
    rw [← map_one (starRingEnd ℂ), ← map_sub, Complex.norm_conj]; exact hclose _ hz'
  have ha : ‖a z‖ ≤ 5 / 4 := by
    have := norm_le_norm_add_norm_sub' (a z) 1
    rw [norm_one] at this; linarith
  have hsplit : a z * conj (a (conj z)) - 1 = a z * (conj (a (conj z)) - 1) + (a z - 1) := by ring
  rw [hsplit]
  calc ‖a z * (conj (a (conj z)) - 1) + (a z - 1)‖
      ≤ ‖a z‖ * ‖conj (a (conj z)) - 1‖ + ‖a z - 1‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ 5 / 4 * (1 / 4) + 1 / 4 := by gcongr
    _ < 1 := by norm_num

lemma sqrtFn_analytic (ha : AnalyticOnNhd ℂ a (strip w))
    (hclose : ∀ z ∈ strip w, ‖a z - 1‖ ≤ 1 / 4) : AnalyticOnNhd ℂ (sqrtFn a) (strip w) :=
  (ha.mul (analyticOnNhd_sharp ha)).cpow analyticOnNhd_const
    (fun z hz => mem_slitPlane_of_close (sqrtFn_base_close hclose hz))

lemma sqrtFn_periodic (hper : ∀ z, a (z + 1) = a z) (z : ℂ) : sqrtFn a (z + 1) = sqrtFn a z := by
  unfold sqrtFn
  rw [map_add, map_one, hper, hper]

lemma sqrtFn_sq (z : ℂ) : sqrtFn a z ^ 2 = a z * conj (a (conj z)) := by
  unfold sqrtFn
  exact Complex.cpow_ofNat_inv_pow _ 2

lemma sqrtFn_ne (hclose : ∀ z ∈ strip w, ‖a z - 1‖ ≤ 1 / 4) {z : ℂ} (hz : z ∈ strip w) :
    sqrtFn a z ≠ 0 := by
  intro h0
  have hp := Complex.slitPlane_ne_zero (mem_slitPlane_of_close (sqrtFn_base_close hclose hz))
  apply hp
  rw [← sqrtFn_sq, h0]
  ring

end SqrtFn

/-! ### Assembly -/

lemma WSum.add' {s ℓ : ℝ} {R S : Symbol} (hR : WSum s ℓ R) (hS : WSum s ℓ S) :
    WSum s ℓ (R + S) :=
  (Summable.add hR hS).of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
    (fun p => by
      rw [Pi.add_apply, ← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (wt_pos p).le)

lemma op_sub_symbol (α : ℝ) {X Y : Symbol} (hX : SymbolSummable X) (hY : SymbolSummable Y)
    (x : ℝ) : op α (X - Y) x = op α X x - op α Y x := by
  have hY' : SymbolSummable (-Y) := by simpa [SymbolSummable] using hY
  rw [sub_eq_add_neg, op_add hX hY', ScaledPrep.op_neg', ← sub_eq_add_neg]

lemma amo_eq_wsym (η E : ℝ) :
    u1 + um1 + wsym η E = amo η - Pi.single ((0 : ℤ), (0 : ℤ)) (E : ℂ) := by
  unfold u1 um1 wsym amo
  abel

/-- **Exact Jacobi preparation** (`d-eq:firstprep`).  For weights `s, ℓ > 0`, an energy with
`e^{-s}(2|η|e^ℓ + |E|) + e^{-2s} ≤ 1/4`, and a self-adjoint `R` with
`e^{-s}‖R‖_{s,ℓ} ≤ σ₁`, the operator `H_x - E` admits an exact, analytic, exponentially local
Jacobi preparation on the strip `|Im z| < ℓ/2π`. -/
theorem exists_jacobiPrep (ω : Weights) (hs : 0 < ω.s) (hℓ : 0 < ω.ℓ) (α η E : ℝ)
    {R : Symbol} (hR : WSum ω.s ω.ℓ R) (hRsa : SymbolSelfAdjoint R)
    (hc : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + |E|) +
      Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4)
    (hσ : Real.exp (-ω.s) * wnorm ω.s ω.ℓ R ≤ sig1) :
    Nonempty (JacobiPrep α (H α η R) E) := by
  set D := prepData ω η E hc
  have ha0 : D.a0 = 1 := rfl
  have hlam : D.lam = Real.exp (-ω.s) := by
    unfold ScaledPrep.Data.lam; rw [ha0, div_one]
  set RW := ω.ofS R hR
  have hRW : ω.toS RW = R := Weights.toS_ofS _ _ _
  have hRstar : ω.star RW = RW := by
    apply ω.toS_injective
    rw [Weights.toS_star, hRW]
    exact (sstar_eq_iff _).2 hRsa
  have hnormR : ‖RW‖ = wnorm ω.s ω.ℓ R := Weights.norm_ofS _ _ _
  have hsm : D.lam * ‖RW‖ ≤ ScaledPrep.sig0 D.c0 := by
    rw [hlam, hnormR]
    exact hσ.trans (min_le_left _ _)
  obtain ⟨K, j, hKge, hjle, hjge, hjsa, hid, hbound⟩ :=
    ScaledPrep.scaled_preparation (α := α) D RW hRstar hsm
  -- smallness of `K` and `j`
  have hCpos := Cst_quarter_pos
  have hKj : ‖K‖ + Real.exp (-ω.s) * ‖j‖ ≤ 1 / 4 := by
    have h1 : ScaledPrep.Cst D.c0 * (D.lam * ‖RW‖) ≤ 1 / 4 := by
      have h2 : D.lam * ‖RW‖ ≤ 1 / (4 * ScaledPrep.Cst (1 / 4)) := by
        rw [hlam, hnormR]; exact hσ.trans (min_le_right _ _)
      have : D.c0 = 1 / 4 := rfl
      rw [this]
      calc ScaledPrep.Cst (1 / 4) * (D.lam * ‖RW‖)
          ≤ ScaledPrep.Cst (1 / 4) * (1 / (4 * ScaledPrep.Cst (1 / 4))) := by gcongr
        _ = 1 / 4 := by field_simp
    rw [← hlam]
    linarith
  have hK1 : ‖K‖ < 1 := by
    have : 0 ≤ Real.exp (-ω.s) * ‖j‖ := by positivity
    linarith
  -- the prepared Jacobi symbol
  set S2 := ω.toS (D.J0 + j)
  have hS2eq : S2 = u1 + um1 + wsym η E + ω.toS j := by
    simp only [S2, Weights.toS_add, ScaledPrep.Data.toS_J0, D, prepData, Weights.toS_ofS,
      Complex.ofReal_one, one_smul]
  have hS2w : WSum ω.s ω.ℓ S2 := ω.toS_wsum _
  have hS2sa : SymbolSelfAdjoint S2 := by
    apply (sstar_eq_iff _).1
    rw [← Weights.toS_star, ω.star_add, D.star_J0, hjsa]
  have hS2ge : HopGE S2 (-1) := by
    rw [hS2eq]
    exact (((HopGE_u1.mono (by norm_num)).add HopGE_um1).add
      ((wsym_hop η E).1.mono (by norm_num))).add hjge
  have hS2le : HopLE S2 1 := by
    rw [hS2eq]
    exact ((HopLE_u1.add (HopLE_um1.mono (by norm_num))).add
      ((wsym_hop η E).2.mono (by norm_num))).add hjle
  set w := ω.ℓ / (2 * Real.pi)
  set a := coefFn α S2 1
  set b := coefFn α S2 0
  -- `a = 1 + a_j` is close to `1`
  have hclose : ∀ z ∈ strip w, ‖a z - 1‖ ≤ 1 / 4 := by
    intro z hz
    have hz' : |z.im| ≤ ω.ℓ / (2 * Real.pi) := le_of_lt hz
    have hu1 : WSum ω.s ω.ℓ u1 := ScaledPrep.u1_wsum
    have hum1 : WSum ω.s ω.ℓ um1 := ScaledPrep.um1_wsum
    have hws := wsym_wsum ω.s ω.ℓ η E
    have hj := ω.toS_wsum j
    have hsum : a z = coefFn α u1 1 z + coefFn α um1 1 z + coefFn α (wsym η E) 1 z +
        coefFn α (ω.toS j) 1 z := by
      simp only [a]
      rw [hS2eq, coefFn_add hs.le (((hu1.add' hum1)).add' hws) hj α 1 hz',
        coefFn_add hs.le (hu1.add' hum1) hws α 1 hz', coefFn_add hs.le hu1 hum1 α 1 hz']
    have e1 : coefFn α u1 1 z = 1 := coefFn_single α 1 1 z
    have e2 : coefFn α um1 1 z = 0 :=
      coefFn_of_zero_fiber (fun q => by simp [um1, Pi.single_apply]) z
    have e3 : coefFn α (wsym η E) 1 z = 0 :=
      coefFn_of_zero_fiber (fun q => (wsym_hop η E).2 (1, q) (by norm_num)) z
    rw [hsum, e1, e2, e3, add_zero, add_zero, add_sub_cancel_left]
    calc ‖coefFn α (ω.toS j) 1 z‖ ≤ ∑' q : ℤ, ‖ω.toS j (1, q)‖ * Real.exp (ω.ℓ * |(q : ℝ)|) :=
          norm_coefFn_le hs.le hj α 1 hz'
      _ ≤ Real.exp (-(ω.s * |((1 : ℤ) : ℝ)|)) * wnorm ω.s ω.ℓ (ω.toS j) :=
          fiber_le_wnorm hs.le hj 1
      _ = Real.exp (-ω.s) * ‖j‖ := by rw [ω.wnorm_toS]; simp
      _ ≤ 1 / 4 := by have := norm_nonneg K; linarith
  -- the change of unknown `Q_x = (I + K)_x`
  have hQ := fun x => ScaledPrep.Q_exp_local (ω := ω) α K hK1 x
  let Q : ℝ → (Op ℤ)ˣ := fun x =>
    ⟨op α (ω.toS (ω.one' + K)) x, Classical.choose (hQ x), (Classical.choose_spec (hQ x)).1,
      (Classical.choose_spec (hQ x)).2.1⟩
  have hwpos : 0 < w := by positivity
  -- the factorization
  have hfac : ∀ x : ℝ, H α η R x - algebraMap ℂ (Op ℤ) E =
      star (Q x : Op ℤ) * jacobi α a b x * Q x := by
    intro x
    have hF := ScaledPrep.operator_factorization (α := α) D RW K j hid x
    have hlhs : op α (ω.toS (D.J0 + RW)) x = H α η R x - algebraMap ℂ (Op ℤ) E := by
      have e : ω.toS (D.J0 + RW) = (amo η + R) - Pi.single ((0 : ℤ), (0 : ℤ)) (E : ℂ) := by
        simp only [Weights.toS_add, ScaledPrep.Data.toS_J0, D, prepData, Weights.toS_ofS,
          Complex.ofReal_one, one_smul, hRW]
        rw [show u1 + um1 + wsym η E + R = (u1 + um1 + wsym η E) + R from rfl, amo_eq_wsym]
        abel
      rw [e, op_sub_symbol α ((amo_summable _).add (hR.symbolSummable hs.le hℓ.le)) (symbolSummable_single _ _),
        op_single, W_zero, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [← hlhs, hF, op_eq_jacobi hs.le hℓ.le hS2w hS2sa hS2ge hS2le x]
  have hap : AnalyticOnNhd ℂ a (strip w) := coefFn_analytic hs.le hS2w α 1
  have hbp : AnalyticOnNhd ℂ b (strip w) := coefFn_analytic hs.le hS2w α 0
  have hreal : ∀ t : ℝ, (t : ℂ) ∈ strip w := fun t => by simp [strip, hwpos]
  have hexp : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (x : ℝ) (m n : ℤ),
      ‖⟪delta m, (Q x : Op ℤ) (delta n)⟫_ℂ‖ ≤ C * Real.exp (-κ * |((n - m : ℤ) : ℝ)|) ∧
      ‖⟪delta m, ((Q x)⁻¹ : (Op ℤ)ˣ).1 (delta n)⟫_ℂ‖ ≤ C * Real.exp (-κ * |((n - m : ℤ) : ℝ)|) := by
    refine ⟨max ((1 - ‖K‖)⁻¹) ‖ω.one' + K‖ + 1, ω.s, by positivity, hs, fun x m n => ⟨?_, ?_⟩⟩
    · have h := (Classical.choose_spec (hQ x)).2.2.2 m n
      have habs : |((m - n : ℤ) : ℝ)| = |((n - m : ℤ) : ℝ)| := by
        push_cast; exact abs_sub_comm _ _
      rw [habs] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      linarith [le_max_right ((1 - ‖K‖)⁻¹) ‖ω.one' + K‖]
    · have h := (Classical.choose_spec (hQ x)).2.2.1 m n
      have habs : |((m - n : ℤ) : ℝ)| = |((n - m : ℤ) : ℝ)| := by
        push_cast; exact abs_sub_comm _ _
      rw [habs] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      linarith [le_max_left ((1 - ‖K‖)⁻¹) ‖ω.one' + K‖]
  have hane : ∀ t : ℝ, a t ≠ 0 := fun t h => by
    have := hclose t (hreal t)
    rw [h, zero_sub, norm_neg, norm_one] at this
    norm_num at this
  exact ⟨{
    Q := Q
    a := a
    b := b
    c := sqrtFn a
    w := w
    w_pos := hwpos
    a_analytic := hap
    b_analytic := hbp
    c_analytic := sqrtFn_analytic hap hclose
    a_periodic := coefFn_add_one α S2 1
    b_periodic := coefFn_add_one α S2 0
    c_periodic := sqrtFn_periodic (coefFn_add_one α S2 1)
    b_real := coefFn_zero_real hS2sa
    a_ne := hane
    c_sq := fun z _ => sqrtFn_sq z
    c_eq_norm := sqrtFn_ofReal
    c_ne := fun z hz => sqrtFn_ne hclose hz
    factor := hfac
    exp_local := hexp }⟩

end AMO
