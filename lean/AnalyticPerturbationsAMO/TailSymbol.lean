/-
# Lemma 2.4 for symbols: inverting `K ↦ Π_{≥2}(J₀ K)` on positive tails

For `J₀ = a(U + U^{-1}) + w` (`a > 0`, `w` a phase coefficient) the hopping-`r` row of
`Π_{≥2}(J₀ ⋆ K)` is, in the gauge `l_r(q) = K_{r,q} e(-αrq/2)`,
  `a l_{r-1} + (τ_{-rα} w) ∗ l_r + a l_{r+1} = δ_r`,
which is the tail recurrence of `TailInverse.lean` in the Banach algebra `𝒲_{s,ℓ}`.
The Green series therefore inverts `K ↦ Π_{≥2}(J₀ ⋆ K)` on positive tails, with the paper's bound
  `‖K‖_{s,ℓ} ≤ C e^{-s} / (a (1 - e^{γ - s})) · ‖D‖_{s,ℓ}`.
Everything here is proved.
-/
import AnalyticPerturbationsAMO.WeightedRing
import AnalyticPerturbationsAMO.TailInverse
import AnalyticPerturbationsAMO.FourierSeries

noncomputable section

open scoped ComplexConjugate Matrix.Norms.Operator

namespace AMO

variable {α : ℝ}

/-! ### Coefficients of products with a phase coefficient -/

/-- A symbol of hopping index `0` (a phase coefficient). -/
def Hop0 (R : Symbol) : Prop := HopGE R 0 ∧ HopLE R 0

lemma Hop0.eq_zero {R : Symbol} (h : Hop0 R) {p : ℤ × ℤ} (hp : p.1 ≠ 0) : R p = 0 := by
  rcases lt_or_gt_of_ne hp with h1 | h1
  · exact h.1 p h1
  · exact h.2 p h1

/-- `(w ⋆ K)_{r,q} = ∑_{q'} w_{0,q'} K_{r,q-q'} e(-αrq'/2)` for a phase coefficient `w`. -/
lemma tmul_hop0_apply {w : Symbol} (hw : Hop0 w) (K : Symbol) (r q : ℤ) :
    tmul α w K (r, q) = ∑' q' : ℤ, w (0, q') * K (r, q - q') * e (-(α * r * q') / 2) := by
  unfold tmul
  have hinj : Function.Injective fun q' : ℤ => ((0 : ℤ), q') := fun a b h => by
    simpa using h
  rw [← hinj.tsum_eq (f := fun p₁ : ℤ × ℤ => w p₁ * K ((r, q) - p₁) * wphase α p₁ ((r, q) - p₁))
    (fun p hp => by
      by_cases h0 : p.1 = 0
      · exact ⟨p.2, by ext <;> simp [h0]⟩
      · exact absurd (by simp [hw.eq_zero h0]) hp)]
  congr 1
  funext q'
  simp only [Prod.mk_sub_mk, sub_zero]
  congr 1
  unfold wphase
  congr 1
  push_cast
  ring

/-- `(U ⋆ K)_{r,q} = K_{r-1,q} e(αq/2)`. -/
lemma u1_tmul_apply' (K : Symbol) (r q : ℤ) :
    tmul α u1 K (r, q) = K (r - 1, q) * e (α * q / 2) := by
  rw [u1_tmul]
  simp only [Prod.mk_sub_mk, sub_zero]
  congr 1
  unfold wphase
  congr 1
  push_cast
  ring

/-- `(U^{-1} ⋆ K)_{r,q} = K_{r+1,q} e(-αq/2)`. -/
lemma um1_tmul_apply' (K : Symbol) (r q : ℤ) :
    tmul α um1 K (r, q) = K (r + 1, q) * e (-(α * q) / 2) := by
  rw [um1_tmul]
  simp only [Prod.mk_add_mk, add_zero]
  congr 1
  unfold wphase
  congr 1
  push_cast
  ring

/-! ### Gauge rows -/

/-- The gauge row `l_r(q) = K_{r,q} e(-αrq/2)`, as a phase coefficient. -/
def lrow (α : ℝ) (K : Symbol) (r : ℤ) : Symbol :=
  fun p => if p.1 = 0 then K (r, p.2) * e (-(α * r * p.2) / 2) else 0

lemma lrow_hop0 (K : Symbol) (r : ℤ) : Hop0 (lrow α K r) := by
  constructor <;> intro p hp <;> simp only [lrow] <;> rw [if_neg (by omega)]

lemma lrow_apply (K : Symbol) (r q : ℤ) : lrow α K r (0, q) = K (r, q) * e (-(α * r * q) / 2) := by
  simp [lrow]

lemma K_eq_lrow (K : Symbol) (r q : ℤ) : K (r, q) = lrow α K r (0, q) * e (α * r * q / 2) := by
  rw [lrow_apply, mul_assoc, ← e_add]
  rw [show -(α * r * q) / 2 + α * r * q / 2 = (0 : ℝ) by ring, e_zero, mul_one]

lemma norm_lrow_term (K : Symbol) (r : ℤ) (p : ℤ × ℤ) :
    ‖lrow α K r p‖ = if p.1 = 0 then ‖K (r, p.2)‖ else 0 := by
  simp only [lrow]; split_ifs <;> simp

/-- `‖l_r‖_{s,ℓ} = ∑_q |K_{r,q}| e^{ℓ|q|}`. -/
lemma lrow_wsum {s ℓ : ℝ} (hs : 0 ≤ s) {K : Symbol} (hK : WSum s ℓ K) (r : ℤ) :
    WSum s ℓ (lrow α K r) ∧
      wnorm s ℓ (lrow α K r) = ∑' q : ℤ, ‖K (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) := by
  have hinj : Function.Injective fun q : ℤ => ((0 : ℤ), q) := fun a b h => by simpa using h
  have hsupp : Function.support (fun p : ℤ × ℤ => ‖lrow α K r p‖ * wt s ℓ p) ⊆
      Set.range fun q : ℤ => ((0 : ℤ), q) := fun p hp => by
    by_cases h0 : p.1 = 0
    · exact ⟨p.2, by ext <;> simp [h0]⟩
    · exact absurd (by simp [norm_lrow_term, h0]) hp
  have hcomp : ∀ q : ℤ, ‖lrow α K r ((0 : ℤ), q)‖ * wt s ℓ ((0 : ℤ), q) =
      ‖K (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|) := fun q => by
    rw [norm_lrow_term]; simp [wt]
  have hfib := summable_fiber hs hK r
  constructor
  · unfold WSum
    rw [← hinj.summable_iff (fun p hp => Function.notMem_support.1 (fun h => hp (hsupp h)))]
    exact hfib.congr fun q => (hcomp q).symm
  · rw [wnorm_eq, ← hinj.tsum_eq hsupp]
    exact tsum_congr hcomp

/-! ### The row identity -/

/-- The translated phase coefficient `(τ_{-rα} w)(q) = w_{0,q} e(-αrq)`. -/
def wtr (α : ℝ) (w : Symbol) (r : ℤ) : Symbol :=
  fun p => if p.1 = 0 then w (0, p.2) * e (-(α * r * p.2)) else 0

lemma wtr_hop0 (w : Symbol) (r : ℤ) : Hop0 (wtr α w r) := by
  constructor <;> intro p hp <;> simp only [wtr] <;> rw [if_neg (by omega)]

lemma norm_wtr_le (w : Symbol) (r : ℤ) (p : ℤ × ℤ) : ‖wtr α w r p‖ ≤ ‖w (0, p.2)‖ := by
  simp only [wtr]; split_ifs <;> simp

lemma wtr_wsum {s ℓ : ℝ} {w : Symbol} (hw : Hop0 w) (hW : WSum s ℓ w) (r : ℤ) :
    WSum s ℓ (wtr α w r) := by
  refine hW.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le) (fun p => ?_)
  by_cases h0 : p.1 = 0
  · obtain ⟨a, b⟩ := p
    simp only at h0
    subst h0
    exact mul_le_mul_of_nonneg_right (norm_wtr_le w r _) (wt_pos _).le
  · simp only [wtr, if_neg h0, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (wt_pos p).le

/-- The symbol of `J₀ = a(U + U^{-1}) + w`. -/
def J0sym (a : ℝ) (w : Symbol) : Symbol := (a : ℂ) • u1 + (a : ℂ) • um1 + w

lemma u1_summable : SymbolSummable u1 := by
  have := (single_wsum (s := 0) (ℓ := 0) ((1 : ℤ), (0 : ℤ)) (1 : ℂ))
  exact symbolSummable_iff_wsum_zero.2 (by unfold u1; exact this)

lemma um1_summable : SymbolSummable um1 := by
  have := (single_wsum (s := 0) (ℓ := 0) ((-1 : ℤ), (0 : ℤ)) (1 : ℂ))
  exact symbolSummable_iff_wsum_zero.2 (by unfold um1; exact this)

lemma SymbolSummable.smul' {R : Symbol} (h : SymbolSummable R) (c : ℂ) : SymbolSummable (c • R) :=
  (h.mul_left ‖c‖).congr fun p => by simp [norm_smul]

/-- **Row identity.**  For `r ≥ 2`, in the gauge `l_r`,
`e(-αrq/2) Π_{≥2}(J₀ ⋆ K)_{r,q} = a l_{r-1}(q) + (τ_{-rα}w ⋆ l_r)(q) + a l_{r+1}(q)`. -/
lemma row_identity {a : ℝ} {w K : Symbol} (hw : Hop0 w) (hwS : SymbolSummable w)
    (hK : SymbolSummable K) {r : ℤ} (hr : 2 ≤ r) (q : ℤ) :
    P2 (tmul α (J0sym a w) K) (r, q) * e (-(α * r * q) / 2) =
      a * lrow α K (r - 1) (0, q) + tmul α (wtr α w r) (lrow α K r) (0, q) +
        a * lrow α K (r + 1) (0, q) := by
  have h1 := (u1_summable.smul' (a : ℂ))
  have h2 := (um1_summable.smul' (a : ℂ))
  simp only [P2, if_pos hr, J0sym]
  rw [tmul_add_left (h1.add h2) hwS hK, tmul_add_left h1 h2 hK, tmul_smul_left, tmul_smul_left]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [u1_tmul_apply', um1_tmul_apply', tmul_hop0_apply hw, tmul_hop0_apply (wtr_hop0 w r)]
  rw [lrow_apply, lrow_apply]
  -- the convolution term
  have hconv : (∑' q' : ℤ, w (0, q') * K (r, q - q') * e (-(α * r * q') / 2)) *
      e (-(α * r * q) / 2) =
      ∑' q' : ℤ, wtr α w r (0, q') * lrow α K r (0, q - q') *
        e (-(α * ((0 : ℤ) : ℝ) * q') / 2) := by
    rw [← tsum_mul_right]
    congr 1
    funext q'
    simp only [wtr, lrow, ↓reduceIte, Int.cast_zero, zero_mul, mul_zero, neg_zero, zero_div,
      e_zero, mul_one]
    calc _ = w (0, q') * K (r, q - q') * (e (-(α * r * q') / 2) * e (-(α * r * q) / 2)) := by
            ring
      _ = w (0, q') * K (r, q - q') *
            (e (-(α * r * q')) * e (-(α * r * ((q - q' : ℤ) : ℝ)) / 2)) := by
            rw [← e_add, ← e_add]; congr 2; push_cast; ring
      _ = _ := by ring
  rw [add_mul, add_mul, hconv]
  have he1 : e (α * q / 2) * e (-(α * r * q) / 2) = e (-(α * ((r - 1 : ℤ) : ℝ) * q) / 2) := by
    rw [← e_add]; congr 1; push_cast; ring
  have he2 : e (-(α * q) / 2) * e (-(α * r * q) / 2) = e (-(α * ((r + 1 : ℤ) : ℝ) * q) / 2) := by
    rw [← e_add]; congr 1; push_cast; ring
  rw [show (a : ℂ) * (K (r - 1, q) * e (α * q / 2)) * e (-(α * r * q) / 2) =
      a * (K (r - 1, q) * (e (α * q / 2) * e (-(α * r * q) / 2))) by ring, he1,
    show (a : ℂ) * (K (r + 1, q) * e (-(α * q) / 2)) * e (-(α * r * q) / 2) =
      a * (K (r + 1, q) * (e (-(α * q) / 2) * e (-(α * r * q) / 2))) by ring, he2]
  ring

/-! ### Row sums -/

/-- The weighted `q`-sum of row `r`: `ρ_r(R) = ∑_q |R_{r,q}| e^{ℓ|q|}`. -/
def rowSum (ℓ : ℝ) (R : Symbol) (r : ℤ) : ℝ := ∑' q : ℤ, ‖R (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|)

lemma rowSum_nonneg (ℓ : ℝ) (R : Symbol) (r : ℤ) : 0 ≤ rowSum ℓ R r :=
  tsum_nonneg fun _ => by positivity

lemma wt_split (s ℓ : ℝ) (r q : ℤ) :
    wt s ℓ (r, q) = Real.exp (s * |(r : ℝ)|) * Real.exp (ℓ * |(q : ℝ)|) := by
  simp only [wt, Real.exp_add]

lemma fiber_eq (s ℓ : ℝ) (R : Symbol) (r : ℤ) :
    (∑' q : ℤ, ‖R (r, q)‖ * wt s ℓ (r, q)) = Real.exp (s * |(r : ℝ)|) * rowSum ℓ R r := by
  rw [rowSum, ← tsum_mul_left]; congr 1; funext q; rw [wt_split]; ring

lemma wsum_nonneg (s ℓ : ℝ) (R : Symbol) : 0 ≤ fun p : ℤ × ℤ => ‖R p‖ * wt s ℓ p :=
  fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le

/-- `‖R‖_{s,ℓ} = ∑_r e^{s|r|} ρ_r(R)`. -/
lemma WSum.rows {s ℓ : ℝ} {R : Symbol} (hR : WSum s ℓ R) :
    Summable (fun r : ℤ => Real.exp (s * |(r : ℝ)|) * rowSum ℓ R r) ∧
      wnorm s ℓ R = ∑' r : ℤ, Real.exp (s * |(r : ℝ)|) * rowSum ℓ R r := by
  have hf := (summable_prod_of_nonneg (wsum_nonneg s ℓ R)).1 hR
  refine ⟨hf.2.congr fun r => fiber_eq s ℓ R r, ?_⟩
  rw [wnorm_eq, hR.tsum_prod]
  exact tsum_congr fun r => fiber_eq s ℓ R r

lemma wsum_of_rows {s ℓ : ℝ} {R : Symbol}
    (hfib : ∀ r, Summable fun q : ℤ => ‖R (r, q)‖ * Real.exp (ℓ * |(q : ℝ)|))
    (hrows : Summable fun r : ℤ => Real.exp (s * |(r : ℝ)|) * rowSum ℓ R r) : WSum s ℓ R :=
  (summable_prod_of_nonneg (wsum_nonneg s ℓ R)).2
    ⟨fun r => ((hfib r).mul_left (Real.exp (s * |(r : ℝ)|))).congr fun q => by rw [wt_split]; ring,
      hrows.congr fun r => (fiber_eq s ℓ R r).symm⟩

lemma rowSum_zero_le {s ℓ : ℝ} {R : Symbol} (hR : WSum s ℓ R) : rowSum ℓ R 0 ≤ wnorm s ℓ R := by
  have h := hR.rows
  calc rowSum ℓ R 0 = Real.exp (s * |((0 : ℤ) : ℝ)|) * rowSum ℓ R 0 := by simp
    _ ≤ _ := by
      rw [h.2]
      exact h.1.le_tsum 0 fun r _ => mul_nonneg (Real.exp_pos _).le (rowSum_nonneg _ _ _)

lemma WSum.csmul {s ℓ : ℝ} {R : Symbol} (h : WSum s ℓ R) (c : ℂ) : WSum s ℓ (c • R) :=
  (h.mul_left ‖c‖).congr fun p => by simp [norm_smul, mul_assoc]

lemma wnorm_csmul {s ℓ : ℝ} (R : Symbol) (c : ℂ) : wnorm s ℓ (c • R) = ‖c‖ * wnorm s ℓ R := by
  rw [wnorm_eq, wnorm_eq, ← tsum_mul_left]
  exact tsum_congr fun p => by simp [norm_smul, mul_assoc]

/-! ### The tail recurrence in `𝒲_{s,ℓ}` -/

namespace TailSym

variable (ω : Weights) (α : ℝ)

open Classical in
/-- An algebra element from a symbol (zero if the symbol is not weighted-summable). -/
def mk (R : Symbol) : WAlg ω α := if h : WSum ω.s ω.ℓ R then WAlg.ofWA ω α (ω.ofS R h) else 0

lemma sym_mk {R : Symbol} (h : WSum ω.s ω.ℓ R) : WAlg.sym ω α (mk ω α R) = R := by
  rw [mk, dif_pos h]; exact ω.toS_ofS R h

lemma norm_mk {R : Symbol} (h : WSum ω.s ω.ℓ R) : ‖mk ω α R‖ = wnorm ω.s ω.ℓ R := by
  rw [WAlg.norm_eq_wnorm, sym_mk ω α h]

variable (a : ℝ) (w D : Symbol)

/-- `β_j = -a^{-1} τ_{-(j+2)α} w`. -/
def beta (j : ℕ) : WAlg ω α := mk ω α ((-(a : ℂ)⁻¹) • wtr α w ((j : ℤ) + 2))

/-- `d_j = a^{-1} l_{j+2}(D)`. -/
def dsrc (j : ℕ) : WAlg ω α := mk ω α (((a : ℂ)⁻¹) • lrow α D ((j : ℤ) + 2))

/-- The Green-series solution `L_j = l_{j+1}`. -/
def L (j : ℕ) : WAlg ω α := Tail.green (beta ω α a w) (dsrc ω α a D) j 0

/-- The solution symbol: `K_{r,q} = L_{r-1}(q) e(αrq/2)` for `r ≥ 1`. -/
def Ksol : Symbol := fun p =>
  if 1 ≤ p.1 then WAlg.sym ω α (L ω α a w D (p.1 - 1).toNat) (0, p.2) * e (α * p.1 * p.2 / 2)
  else 0

variable {ω α a w D}

lemma sym_beta (hw : Hop0 w) (hwS : WSum ω.s ω.ℓ w) (j : ℕ) :
    WAlg.sym ω α (beta ω α a w j) = (-(a : ℂ)⁻¹) • wtr α w ((j : ℤ) + 2) :=
  sym_mk ω α ((wtr_wsum hw hwS _).csmul _)

lemma sym_dsrc (hD : WSum ω.s ω.ℓ D) (j : ℕ) :
    WAlg.sym ω α (dsrc ω α a D j) = ((a : ℂ)⁻¹) • lrow α D ((j : ℤ) + 2) :=
  sym_mk ω α ((lrow_wsum ω.hs hD _).1.csmul _)

lemma norm_dsrc (hD : WSum ω.s ω.ℓ D) (j : ℕ) :
    ‖dsrc ω α a D j‖ = |a|⁻¹ * rowSum ω.ℓ D ((j : ℤ) + 2) := by
  rw [dsrc, norm_mk ω α ((lrow_wsum ω.hs hD _).1.csmul _), wnorm_csmul,
    (lrow_wsum ω.hs hD _).2, rowSum]
  simp

/-- `∑_j e^{sj} ‖d_j‖ ≤ |a|^{-1} e^{-2s} ‖D‖_{s,ℓ}`. -/
lemma dsrc_bound (hD : WSum ω.s ω.ℓ D) :
    Summable (fun j : ℕ => Real.exp (ω.s * j) * ‖dsrc ω α a D j‖) ∧
      ∑' j : ℕ, Real.exp (ω.s * j) * ‖dsrc ω α a D j‖ ≤
        |a|⁻¹ * Real.exp (-(2 * ω.s)) * wnorm ω.s ω.ℓ D := by
  have hr := hD.rows
  have hinj : Function.Injective fun j : ℕ => (j : ℤ) + 2 := fun x y h => by simpa using h
  have hc := hr.1.comp_injective hinj
  have hterm : ∀ j : ℕ, Real.exp (ω.s * j) * ‖dsrc ω α a D j‖ =
      |a|⁻¹ * Real.exp (-(2 * ω.s)) *
        (fun r : ℤ => Real.exp (ω.s * |(r : ℝ)|) * rowSum ω.ℓ D r) ((j : ℤ) + 2) := fun j => by
    rw [norm_dsrc hD]
    simp only
    rw [show |(((j : ℤ) + 2 : ℤ) : ℝ)| = (j : ℝ) + 2 by push_cast; exact abs_of_nonneg (by positivity)]
    rw [show ω.s * (j : ℝ) = -(2 * ω.s) + ω.s * ((j : ℝ) + 2) by ring, Real.exp_add]
    ring
  refine ⟨(hc.mul_left (|a|⁻¹ * Real.exp (-(2 * ω.s)))).congr fun j => (hterm j).symm, ?_⟩
  rw [tsum_congr hterm, tsum_mul_left, hr.2]
  exact mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hr.1
    (fun r => mul_nonneg (Real.exp_pos _).le (rowSum_nonneg _ _ _)) hinj) (by positivity)

section Green

variable {C γ : ℝ}

/-- The Green series solves `L_j = β_j L_{j+1} - L_{j+2} + d_j`. -/
lemma L_rec (hD : WSum ω.s ω.ℓ D) (hC : 0 ≤ C)
    (hP : ∀ j m, ‖Tail.P (beta ω α a w) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < ω.s) (j : ℕ) :
    L ω α a w D j = beta ω α a w j * L ω α a w D (j + 1) - L ω α a w D (j + 2) +
      dsrc ω α a D j :=
  Tail.green_scalar hC hP hγs (dsrc_bound hD).1 j

lemma L_bound (hD : WSum ω.s ω.ℓ D) (hC : 0 ≤ C)
    (hP : ∀ j m, ‖Tail.P (beta ω α a w) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < ω.s) :
    Summable (fun j : ℕ => Real.exp (ω.s * j) * ‖L ω α a w D j‖) ∧
      ∑' j : ℕ, Real.exp (ω.s * j) * ‖L ω α a w D j‖ ≤
        C / (1 - Real.exp (γ - ω.s)) * (|a|⁻¹ * Real.exp (-(2 * ω.s)) * wnorm ω.s ω.ℓ D) := by
  have hd := dsrc_bound (α := α) (a := a) hD
  have hg := Tail.green_weighted_bound hC hP hγs hd.1
  have hle : ∀ j : ℕ, Real.exp (ω.s * j) * ‖L ω α a w D j‖ ≤
      Real.exp (ω.s * j) * ‖Tail.green (beta ω α a w) (dsrc ω α a D) j‖ := fun j =>
    mul_le_mul_of_nonneg_left (norm_le_pi_norm (Tail.green (beta ω α a w) (dsrc ω α a D) j) 0)
      (Real.exp_pos _).le
  have hs1 := hg.1.of_nonneg_of_le (fun j => by positivity) hle
  refine ⟨hs1, ?_⟩
  have hq : 0 ≤ C / (1 - Real.exp (γ - ω.s)) :=
    div_nonneg hC (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
  calc _ ≤ _ := Summable.tsum_le_tsum hle hs1 hg.1
    _ ≤ _ := hg.2
    _ ≤ _ := mul_le_mul_of_nonneg_left hd.2 hq

end Green

lemma Ksol_succ (j : ℕ) (q : ℤ) :
    Ksol ω α a w D ((j : ℤ) + 1, q) =
      WAlg.sym ω α (L ω α a w D j) (0, q) * e (α * (((j : ℤ) + 1 : ℤ) : ℝ) * q / 2) := by
  simp only [Ksol]
  rw [if_pos (by omega), show ((j : ℤ) + 1 - 1).toNat = j by omega]

lemma Ksol_lt {r : ℤ} (hr : r < 1) (q : ℤ) : Ksol ω α a w D (r, q) = 0 := by
  simp only [Ksol]; rw [if_neg (by omega)]

lemma Ksol_hopGE : HopGE (Ksol ω α a w D) 1 := fun p hp => by
  obtain ⟨r, q⟩ := p; exact Ksol_lt hp q

lemma lrow_Ksol {r : ℤ} {j : ℕ} (h : r = (j : ℤ) + 1) (q : ℤ) :
    lrow α (Ksol ω α a w D) r (0, q) = WAlg.sym ω α (L ω α a w D j) (0, q) := by
  subst h
  rw [lrow_apply, Ksol_succ, mul_assoc, ← e_add]
  rw [show α * (((j : ℤ) + 1 : ℤ) : ℝ) * q / 2 + -(α * (((j : ℤ) + 1 : ℤ) : ℝ) * q) / 2 = 0 by
    ring, e_zero, mul_one]

lemma rowSum_Ksol (j : ℕ) :
    rowSum ω.ℓ (Ksol ω α a w D) ((j : ℤ) + 1) = rowSum ω.ℓ (WAlg.sym ω α (L ω α a w D j)) 0 := by
  unfold rowSum
  exact tsum_congr fun q => by rw [Ksol_succ, norm_mul, norm_e, mul_one]

lemma rowSum_Ksol_lt {r : ℤ} (hr : r < 1) : rowSum ω.ℓ (Ksol ω α a w D) r = 0 := by
  unfold rowSum
  simp [Ksol_lt hr]

lemma rowSum_Ksol_le (j : ℕ) :
    rowSum ω.ℓ (Ksol ω α a w D) ((j : ℤ) + 1) ≤ ‖L ω α a w D j‖ := by
  have hW : WSum ω.s ω.ℓ (WAlg.sym ω α (L ω α a w D j)) := ω.toS_wsum _
  rw [rowSum_Ksol, WAlg.norm_eq_wnorm]
  exact rowSum_zero_le hW

lemma Ksol_fiber (r : ℤ) :
    Summable fun q : ℤ => ‖Ksol ω α a w D (r, q)‖ * Real.exp (ω.ℓ * |(q : ℝ)|) := by
  by_cases hr : 1 ≤ r
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, r = (j : ℤ) + 1 := ⟨(r - 1).toNat, by omega⟩
    have hW : WSum ω.s ω.ℓ (WAlg.sym ω α (L ω α a w D j)) := ω.toS_wsum _
    exact (summable_fiber ω.hs hW 0).congr fun q => by rw [Ksol_succ, norm_mul, norm_e, mul_one]
  · exact summable_zero.congr fun q => by rw [Ksol_lt (by omega), norm_zero, zero_mul]

/-- **Existence with the weighted bound.** -/
lemma Ksol_wsum_bound (hD : WSum ω.s ω.ℓ D) {C γ : ℝ} (hC : 0 ≤ C)
    (hP : ∀ j m, ‖Tail.P (beta ω α a w) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < ω.s) :
    WSum ω.s ω.ℓ (Ksol ω α a w D) ∧
      wnorm ω.s ω.ℓ (Ksol ω α a w D) ≤
        C * Real.exp (-ω.s) / (|a| * (1 - Real.exp (γ - ω.s))) * wnorm ω.s ω.ℓ D := by
  have hL := L_bound hD hC hP hγs
  set f : ℤ → ℝ := fun r => Real.exp (ω.s * |(r : ℝ)|) * rowSum ω.ℓ (Ksol ω α a w D) r with hf
  have hinj : Function.Injective fun j : ℕ => (j : ℤ) + 1 := fun x y h => by simpa using h
  have hzero : ∀ r ∉ Set.range (fun j : ℕ => (j : ℤ) + 1), f r = 0 := fun r hr => by
    have : r < 1 := by
      by_contra h
      exact hr ⟨(r - 1).toNat, by simp only; omega⟩
    simp only [hf, rowSum_Ksol_lt this, mul_zero]
  have hcomp : ∀ j : ℕ, f ((j : ℤ) + 1) ≤
      Real.exp ω.s * (Real.exp (ω.s * j) * ‖L ω α a w D j‖) := fun j => by
    simp only [hf]
    rw [show |(((j : ℤ) + 1 : ℤ) : ℝ)| = (j : ℝ) + 1 by push_cast; exact abs_of_nonneg (by positivity)]
    rw [show ω.s * ((j : ℝ) + 1) = ω.s + ω.s * j by ring, Real.exp_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rowSum_Ksol_le j)
      (Real.exp_pos _).le) (Real.exp_pos _).le
  have hf0 : ∀ r, 0 ≤ f r := fun r => mul_nonneg (Real.exp_pos _).le (rowSum_nonneg _ _ _)
  have hsc : Summable (f ∘ fun j : ℕ => (j : ℤ) + 1) :=
    (hL.1.mul_left (Real.exp ω.s)).of_nonneg_of_le (fun j => hf0 _) hcomp
  have hsf : Summable f := (hinj.summable_iff hzero).1 hsc
  have hW : WSum ω.s ω.ℓ (Ksol ω α a w D) := wsum_of_rows Ksol_fiber hsf
  refine ⟨hW, ?_⟩
  have hsupp : Function.support f ⊆ Set.range fun j : ℕ => (j : ℤ) + 1 := fun r hr => by
    by_contra h; exact hr (hzero r h)
  have hq : 0 < 1 - Real.exp (γ - ω.s) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
  have h2 : Real.exp (-(2 * ω.s)) = Real.exp (-ω.s) * Real.exp (-ω.s) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : Real.exp ω.s * Real.exp (-ω.s) = 1 := by rw [← Real.exp_add]; simp
  rw [hW.rows.2, ← hinj.tsum_eq hsupp]
  calc ∑' j : ℕ, f ((j : ℤ) + 1)
      ≤ ∑' j : ℕ, Real.exp ω.s * (Real.exp (ω.s * j) * ‖L ω α a w D j‖) :=
        Summable.tsum_le_tsum hcomp hsc (hL.1.mul_left _)
    _ = Real.exp ω.s * ∑' j : ℕ, Real.exp (ω.s * j) * ‖L ω α a w D j‖ := tsum_mul_left
    _ ≤ Real.exp ω.s * (C / (1 - Real.exp (γ - ω.s)) *
          (|a|⁻¹ * Real.exp (-(2 * ω.s)) * wnorm ω.s ω.ℓ D)) :=
        mul_le_mul_of_nonneg_left hL.2 (Real.exp_pos _).le
    _ = (Real.exp ω.s * Real.exp (-ω.s)) *
          (C * Real.exp (-ω.s) / (|a| * (1 - Real.exp (γ - ω.s))) * wnorm ω.s ω.ℓ D) := by
        rw [h2, mul_comm |a|, ← div_div]; ring
    _ = _ := by rw [h1, one_mul]

lemma e_ne_zero' (t : ℝ) : e t ≠ 0 := fun h => by simpa [h] using norm_e t

/-- **The equation** `Π_{≥2}(J₀ ⋆ K) = D`. -/
lemma Ksol_eq (ha : a ≠ 0) (hw : Hop0 w) (hwS : WSum ω.s ω.ℓ w) (hD2 : HopGE D 2)
    (hD : WSum ω.s ω.ℓ D) {C γ : ℝ} (hC : 0 ≤ C)
    (hP : ∀ j m, ‖Tail.P (beta ω α a w) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < ω.s) :
    P2 (tmul α (J0sym a w) (Ksol ω α a w D)) = D := by
  funext p
  obtain ⟨r, q⟩ := p
  by_cases hr : 2 ≤ r
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, r = (j : ℤ) + 2 := ⟨(r - 2).toNat, by omega⟩
    have hK : SymbolSummable (Ksol ω α a w D) :=
      (Ksol_wsum_bound hD hC hP hγs).1.symbolSummable ω.hs ω.hℓ
    have hrow := row_identity (α := α) (a := a) hw (hwS.symbolSummable ω.hs ω.hℓ) hK hr q
    rw [lrow_Ksol (j := j) (by ring), lrow_Ksol (j := j + 2) (by push_cast; ring)] at hrow
    have hmid : tmul α (wtr α w ((j : ℤ) + 2)) (lrow α (Ksol ω α a w D) ((j : ℤ) + 2)) (0, q) =
        tmul α (wtr α w ((j : ℤ) + 2)) (WAlg.sym ω α (L ω α a w D (j + 1))) (0, q) := by
      rw [tmul_hop0_apply (wtr_hop0 w _), tmul_hop0_apply (wtr_hop0 w _)]
      refine tsum_congr fun q' => ?_
      rw [lrow_Ksol (j := j + 1) (by push_cast; ring)]
    have hg := congrArg (fun f => WAlg.sym ω α f (0, q)) (L_rec hD hC hP hγs j)
    simp only [WAlg.sym_add, WAlg.sym_sub, WAlg.sym_mul, sym_beta hw hwS, sym_dsrc hD,
      tmul_smul_left, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hg
    have h1 : (a : ℂ) * (a : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast ha)
    apply mul_right_cancel₀ (e_ne_zero' (-(α * (((j : ℤ) + 2 : ℤ) : ℝ) * q) / 2))
    rw [hrow, hmid, ← lrow_apply]
    linear_combination (a : ℂ) * hg +
      (lrow α D ((j : ℤ) + 2) (0, q) -
        tmul α (wtr α w ((j : ℤ) + 2)) (WAlg.sym ω α (L ω α a w D (j + 1))) (0, q)) * h1
  · simp only [P2, if_neg hr]
    exact (hD2 _ (by simp only; omega)).symm

/-- **Uniqueness**: any weighted positive-tail solution is `Ksol`. -/
lemma Ksol_unique (ha : a ≠ 0) (hw : Hop0 w) (hwS : WSum ω.s ω.ℓ w) (hD : WSum ω.s ω.ℓ D)
    {C γ : ℝ} (hC : 0 ≤ C) (hP : ∀ j m, ‖Tail.P (beta ω α a w) j m‖ ≤ C * Real.exp (γ * m))
    (hγs : γ < ω.s) {K : Symbol} (hK1 : HopGE K 1) (hK : WSum ω.s ω.ℓ K)
    (hKeq : P2 (tmul α (J0sym a w) K) = D) : K = Ksol ω α a w D := by
  have hlW : ∀ j : ℕ, WSum ω.s ω.ℓ (lrow α K ((j : ℤ) + 1)) := fun j => (lrow_wsum ω.hs hK _).1
  obtain ⟨l, hl⟩ : ∃ l : ℕ → WAlg ω α, l = fun j : ℕ => mk ω α (lrow α K ((j : ℤ) + 1)) := ⟨_, rfl⟩
  have hsl : ∀ j, WAlg.sym ω α (l j) = lrow α K ((j : ℤ) + 1) := fun j => by
    rw [hl]; exact sym_mk ω α (hlW j)
  have h1 : (a : ℂ)⁻¹ * (a : ℂ) = 1 := inv_mul_cancel₀ (by exact_mod_cast ha)
  have hrec : ∀ j, l j = beta ω α a w j * l (j + 1) - l (j + 2) + dsrc ω α a D j := by
    intro j
    apply WAlg.sym_injective ω α
    rw [WAlg.sym_add, WAlg.sym_sub, WAlg.sym_mul, sym_beta hw hwS, sym_dsrc hD, hsl, hsl, hsl,
      tmul_smul_left]
    funext p
    obtain ⟨r, q⟩ := p
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (((j + 1 : ℕ) : ℤ) + 1) = (j : ℤ) + 2 by push_cast; ring,
      show (((j + 2 : ℕ) : ℤ) + 1) = (j : ℤ) + 2 + 1 by push_cast; ring]
    by_cases hr : r = 0
    · subst hr
      have hrow := row_identity (α := α) (a := a) hw (hwS.symbolSummable ω.hs ω.hℓ)
        (hK.symbolSummable ω.hs ω.hℓ) (r := (j : ℤ) + 2) (by omega) q
      rw [hKeq, ← lrow_apply, show (j : ℤ) + 2 - 1 = (j : ℤ) + 1 by ring] at hrow
      linear_combination (-(a : ℂ)⁻¹) * hrow -
        (lrow α K ((j : ℤ) + 1) (0, q) + lrow α K ((j : ℤ) + 2 + 1) (0, q)) * h1
    · have hz : ∀ (R : Symbol) (t q' : ℤ), lrow α R t (r, q') = 0 := fun R t q' =>
        (lrow_hop0 R t).eq_zero hr
      rw [tmul_hop0_apply (wtr_hop0 w _)]
      simp [hz]
  have hlsum : Summable fun j : ℕ => Real.exp (ω.s * j) * ‖l j‖ := by
    have hinj : Function.Injective fun j : ℕ => (j : ℤ) + 1 := fun x y h => by simpa using h
    refine (hK.rows.1.comp_injective hinj).of_nonneg_of_le (fun j => by positivity) fun j => ?_
    simp only [Function.comp]
    rw [hl, norm_mk ω α (hlW j), (lrow_wsum ω.hs hK _).2]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) le_rfl (tsum_nonneg fun _ => by positivity)
      (Real.exp_pos _).le
    rw [show |(((j : ℤ) + 1 : ℤ) : ℝ)| = (j : ℝ) + 1 by push_cast; exact abs_of_nonneg (by positivity)]
    nlinarith [ω.hs]
  have hu : ∀ j, l j = L ω α a w D j := fun j =>
    Tail.green_unique hC hP hγs ω.hs (dsrc_bound hD).1 hrec hlsum j
  funext p
  obtain ⟨r, q⟩ := p
  by_cases hr : 1 ≤ r
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, r = (j : ℤ) + 1 := ⟨(r - 1).toNat, by omega⟩
    rw [K_eq_lrow (α := α) K, Ksol_succ, ← hu j, hsl]
  · rw [hK1 _ (by simp only; omega), Ksol_lt (by omega)]

/-- **Lemma 2.4 (tail inverse), symbol form.**  Let `J₀ = a(U + U^{-1}) + w` with `a ≠ 0` and
`w` a phase coefficient in `𝒲_{s,ℓ}`, and suppose the transfer products of the tail recurrence
satisfy `‖P_{j,m}‖ ≤ C e^{γ m}` with `γ < s`.  Then for every `D ∈ 𝒲_{s,ℓ}` supported in hopping
`≥ 2` there is a unique `K ∈ 𝒲_{s,ℓ}` supported in hopping `≥ 1` with `Π_{≥2}(J₀ K) = D`, and
`‖K‖_{s,ℓ} ≤ C e^{-s} / (|a| (1 - e^{γ - s})) ‖D‖_{s,ℓ}`. -/
theorem tail_inverse_symbol (ha : a ≠ 0) (hw : Hop0 w) (hwS : WSum ω.s ω.ℓ w)
    (hD2 : HopGE D 2) (hD : WSum ω.s ω.ℓ D) {C γ : ℝ} (hC : 0 ≤ C)
    (hP : ∀ j m, ‖Tail.P (beta ω α a w) j m‖ ≤ C * Real.exp (γ * m)) (hγs : γ < ω.s) :
    ∃! K : Symbol, HopGE K 1 ∧ WSum ω.s ω.ℓ K ∧ P2 (tmul α (J0sym a w) K) = D ∧
      wnorm ω.s ω.ℓ K ≤ C * Real.exp (-ω.s) / (|a| * (1 - Real.exp (γ - ω.s))) *
        wnorm ω.s ω.ℓ D :=
  ⟨Ksol ω α a w D,
    ⟨Ksol_hopGE, (Ksol_wsum_bound hD hC hP hγs).1, Ksol_eq ha hw hwS hD2 hD hC hP hγs,
      (Ksol_wsum_bound hD hC hP hγs).2⟩,
    fun K hK => Ksol_unique ha hw hwS hD hC hP hγs hK.1 hK.2.1 hK.2.2.1⟩

end TailSym

end AMO
