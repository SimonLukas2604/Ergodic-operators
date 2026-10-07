/-
# The weighted Weyl algebra `𝒲_{s,ℓ}`  (paper §2.2, "Preparation in a scaled Banach algebra")

Symbols with `‖R‖_{s,ℓ} = ∑ |R_{r,q}| e^{s|r| + ℓ|q|} < ∞` form a Banach `*`-algebra under the
twisted convolution
  `(R ⋆ S)_p = ∑_{p₁} R_{p₁} S_{p - p₁} e^{πiα(r₁q₂ - r₂q₁)}`,
which is the symbol of the operator product.  We prove (no `sorry`):
* `‖R ⋆ S‖_{s,ℓ} ≤ ‖R‖_{s,ℓ} ‖S‖_{s,ℓ}` and `‖R^*‖_{s,ℓ} = ‖R‖_{s,ℓ}` for `s, ℓ ≥ 0`;
* `op(R ⋆ S) = op(R) op(S)` and `op(R^*) = op(R)^*` on every fibre;
* Fourier duality is multiplicative: `𝓕(R ⋆ S) = 𝓕R ⋆ 𝓕S`;
* **exponential locality**: `|⟨δ_n, R_x δ_m⟩| ≤ ‖R‖_{s,ℓ} e^{-s|n-m|}`.
-/
import AnalyticPerturbationsAMO.Spectral

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open L2

namespace AMO

/-- The weight `w_{s,ℓ}(r,q) = e^{s|r| + ℓ|q|}`. -/
def wt (s ℓ : ℝ) (p : ℤ × ℤ) : ℝ := Real.exp (s * |(p.1 : ℝ)| + ℓ * |(p.2 : ℝ)|)

variable {s ℓ : ℝ}

lemma wt_pos (p : ℤ × ℤ) : 0 < wt s ℓ p := Real.exp_pos _

lemma one_le_wt (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (p : ℤ × ℤ) : 1 ≤ wt s ℓ p :=
  Real.one_le_exp (by positivity)

lemma wt_add_le (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (p p' : ℤ × ℤ) :
    wt s ℓ (p + p') ≤ wt s ℓ p * wt s ℓ p' := by
  unfold wt
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  have h1 := mul_le_mul_of_nonneg_left (abs_add_le (p.1 : ℝ) p'.1) hs
  have h2 := mul_le_mul_of_nonneg_left (abs_add_le (p.2 : ℝ) p'.2) hℓ
  nlinarith

lemma wt_neg (p : ℤ × ℤ) : wt s ℓ (-p) = wt s ℓ p := by simp [wt]

/-- `R ∈ 𝒲_{s,ℓ}`. -/
def WSum (s ℓ : ℝ) (R : Symbol) : Prop := Summable fun p => ‖R p‖ * wt s ℓ p

lemma wnorm_eq (R : Symbol) : wnorm s ℓ R = ∑' p, ‖R p‖ * wt s ℓ p := rfl

lemma WSmall.wsum {ε : ℝ} {R : Symbol} (h : WSmall s ℓ R ε) : WSum s ℓ R := h.1

lemma WSum.symbolSummable {R : Symbol} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (h : WSum s ℓ R) :
    SymbolSummable R :=
  h.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => le_mul_of_one_le_right (norm_nonneg _) (one_le_wt hs hℓ p))

lemma symbolSummable_iff_wsum_zero {R : Symbol} : SymbolSummable R ↔ WSum 0 0 R := by
  simp [WSum, SymbolSummable, wt]

/-! ### Twisted convolution -/

/-- The Weyl phase `e^{πiα(rq' - r'q)}`. -/
def wphase (α : ℝ) (p p' : ℤ × ℤ) : ℂ := e (α * (p.1 * p'.2 - p'.1 * p.2) / 2)

@[simp] lemma norm_wphase (α : ℝ) (p p' : ℤ × ℤ) : ‖wphase α p p'‖ = 1 := norm_e _

/-- Twisted convolution of symbols: the symbol of the product of the operators. -/
def tmul (α : ℝ) (R S : Symbol) : Symbol :=
  fun p => ∑' p₁ : ℤ × ℤ, R p₁ * S (p - p₁) * wphase α p₁ (p - p₁)

/-- `(p, p₁) ↦ (p₁, p - p₁)`. -/
def shearEquiv : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun z := (z.2, z.1 - z.2)
  invFun z := (z.1 + z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

section Product

variable {α : ℝ} {R S : Symbol}

/-- The product majorant `F(p₁, p₂) = |R_{p₁}| w(p₁) |S_{p₂}| w(p₂)`. -/
def majorant (s ℓ : ℝ) (R S : Symbol) (z : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  (‖R z.1‖ * wt s ℓ z.1) * (‖S z.2‖ * wt s ℓ z.2)

lemma summable_majorant (hR : WSum s ℓ R) (hS : WSum s ℓ S) :
    Summable (majorant s ℓ R S) :=
  hR.mul_of_nonneg hS (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
    (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)

lemma tsum_majorant (hR : WSum s ℓ R) (hS : WSum s ℓ S) :
    ∑' z, majorant s ℓ R S z = wnorm s ℓ R * wnorm s ℓ S :=
  (hR.tsum_mul_tsum hS (summable_majorant hR hS)).symm

lemma summable_majorant_shear (hR : WSum s ℓ R) (hS : WSum s ℓ S) :
    Summable (majorant s ℓ R S ∘ shearEquiv) :=
  (shearEquiv.summable_iff).2 (summable_majorant hR hS)

lemma norm_term_mul_wt_le (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (p p₁ : ℤ × ℤ) :
    ‖R p₁ * S (p - p₁) * wphase α p₁ (p - p₁)‖ * wt s ℓ p ≤
      (majorant s ℓ R S ∘ shearEquiv) (p, p₁) := by
  simp only [Function.comp_apply, shearEquiv, Equiv.coe_fn_mk, majorant, norm_mul,
    norm_wphase, mul_one]
  have h := wt_add_le hs hℓ p₁ (p - p₁)
  rw [add_sub_cancel] at h
  calc ‖R p₁‖ * ‖S (p - p₁)‖ * wt s ℓ p
      ≤ ‖R p₁‖ * ‖S (p - p₁)‖ * (wt s ℓ p₁ * wt s ℓ (p - p₁)) := by gcongr
    _ = _ := by ring

lemma summable_tmul_term (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hR : WSum s ℓ R) (hS : WSum s ℓ S)
    (p : ℤ × ℤ) : Summable fun p₁ => ‖R p₁ * S (p - p₁) * wphase α p₁ (p - p₁)‖ := by
  refine ((summable_majorant_shear hR hS).prod_factor p).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p₁ => ?_)
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_wt hs hℓ p) |>.trans
    (norm_term_mul_wt_le hs hℓ p p₁)

lemma norm_tmul_mul_wt_le (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hR : WSum s ℓ R) (hS : WSum s ℓ S)
    (p : ℤ × ℤ) :
    ‖tmul α R S p‖ * wt s ℓ p ≤ ∑' p₁, (majorant s ℓ R S ∘ shearEquiv) (p, p₁) := by
  calc ‖tmul α R S p‖ * wt s ℓ p
      ≤ (∑' p₁, ‖R p₁ * S (p - p₁) * wphase α p₁ (p - p₁)‖) * wt s ℓ p :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (summable_tmul_term hs hℓ hR hS p))
          (wt_pos p).le
    _ = ∑' p₁, ‖R p₁ * S (p - p₁) * wphase α p₁ (p - p₁)‖ * wt s ℓ p := by
        rw [tsum_mul_right]
    _ ≤ _ := (((summable_tmul_term hs hℓ hR hS p).mul_right _)).tsum_le_tsum
        (fun p₁ => norm_term_mul_wt_le hs hℓ p p₁)
        ((summable_majorant_shear hR hS).prod_factor p)

/-- `𝒲_{s,ℓ}` is closed under the twisted product. -/
theorem WSum.tmul (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hR : WSum s ℓ R) (hS : WSum s ℓ S) :
    WSum s ℓ (tmul α R S) :=
  (summable_majorant_shear hR hS).prod.of_nonneg_of_le
    (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
    (norm_tmul_mul_wt_le hs hℓ hR hS)

/-- **Submultiplicativity** `‖R ⋆ S‖_{s,ℓ} ≤ ‖R‖_{s,ℓ} ‖S‖_{s,ℓ}`. -/
theorem wnorm_tmul_le (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hR : WSum s ℓ R) (hS : WSum s ℓ S) :
    wnorm s ℓ (tmul α R S) ≤ wnorm s ℓ R * wnorm s ℓ S := by
  rw [← tsum_majorant hR hS, ← shearEquiv.tsum_eq]
  show _ ≤ ∑' c, (majorant s ℓ R S ∘ shearEquiv) c
  rw [(summable_majorant_shear hR hS).tsum_prod]
  exact (WSum.tmul hs hℓ hR hS).tsum_le_tsum (norm_tmul_mul_wt_le hs hℓ hR hS)
    (summable_majorant_shear hR hS).prod

/-- **The symbol calculus is multiplicative**: `op(R ⋆ S) = op(R) op(S)` on every fibre. -/
theorem op_tmul (hR : SymbolSummable R) (hS : SymbolSummable S) (x : ℝ) :
    op α (tmul α R S) x = op α R x * op α S x := by
  have hR0 := symbolSummable_iff_wsum_zero.1 hR
  have hS0 := symbolSummable_iff_wsum_zero.1 hS
  have hnR : Summable fun p => ‖R p • W α x p.1 p.2‖ :=
    hR.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
      rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_W_le _ _ _ _))
  have hnS : Summable fun p => ‖S p • W α x p.1 p.2‖ :=
    hS.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
      rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_W_le _ _ _ _))
  -- the product of the two series
  let T : (ℤ × ℤ) × (ℤ × ℤ) → L2 ℤ →L[ℂ] L2 ℤ := fun z =>
    (R z.1 * S z.2 * wphase α z.1 z.2) • W α x (z.1 + z.2).1 (z.1 + z.2).2
  have hT : ∀ z, (R z.1 • W α x z.1.1 z.1.2) * (S z.2 • W α x z.2.1 z.2.2) = T z := by
    intro z
    rw [smul_mul_smul_comm, ContinuousLinearMap.mul_def, W_mul, smul_smul]
    rfl
  have hTn : Summable fun z => ‖(T ∘ shearEquiv) z‖ := by
    refine (summable_majorant_shear hR0 hS0).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun z => ?_)
    simp only [Function.comp_apply, T, shearEquiv, Equiv.coe_fn_mk, majorant, wt,
      zero_mul, add_zero, Real.exp_zero, mul_one]
    rw [norm_smul, norm_mul, norm_mul, norm_wphase, mul_one]
    exact mul_le_of_le_one_right (by positivity) (norm_W_le _ _ _ _)
  have hTs : Summable (T ∘ shearEquiv) := hTn.of_norm
  unfold op
  rw [tsum_mul_tsum_of_summable_norm hnR hnS]
  simp only [hT]
  rw [← shearEquiv.tsum_eq]
  show _ = ∑' c, (T ∘ shearEquiv) c
  rw [hTs.tsum_prod]
  congr 1
  funext p
  have hc : Summable fun p₁ => R p₁ * S (p - p₁) * wphase α p₁ (p - p₁) :=
    (summable_tmul_term le_rfl le_rfl hR0 hS0 p).of_norm
  rw [tmul]
  refine (hc.tsum_smul_const (W α x p.1 p.2)).symm.trans ?_
  congr 1
  funext p₁
  simp [T, shearEquiv]

end Product

/-! ### Involution -/

/-- The symbol of the adjoint: `(R^*)_p = conj R_{-p}`. -/
def sstar (R : Symbol) : Symbol := fun p => conj (R (-p))

lemma wnorm_sstar (R : Symbol) : wnorm s ℓ (sstar R) = wnorm s ℓ R := by
  rw [wnorm_eq, wnorm_eq, ← (Equiv.neg (ℤ × ℤ)).tsum_eq]
  congr 1
  funext p
  simp [sstar, wt]

lemma SymbolSummable.sstar {R : Symbol} (h : SymbolSummable R) : SymbolSummable (sstar R) := by
  unfold SymbolSummable AMO.sstar
  simp only [Complex.norm_conj]
  exact ((Equiv.neg (ℤ × ℤ)).summable_iff (f := fun p => ‖R p‖)).2 h

/-- `op(R^*) = op(R)^*`. -/
theorem op_sstar {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    op α (sstar R) x = star (op α R x) := by
  have h1 := (summable_op (α := α) hR x).hasSum.star
  have h2 := ((Equiv.neg (ℤ × ℤ)).hasSum_iff).2 (summable_op (α := α) hR.sstar x).hasSum
  unfold op at *
  refine (h1.unique ?_).symm
  convert h2 using 1
  funext p
  simp [star_W, sstar]

/-! ### Fourier duality is an algebra automorphism -/

/-- The rotation `(r, q) ↦ (-q, r)` of `ℤ²`. -/
def rotEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (-p.2, p.1)
  invFun p := (p.2, -p.1)
  left_inv p := by simp
  right_inv p := by simp

lemma wphase_rot (α : ℝ) (p p' : ℤ × ℤ) :
    wphase α (rotEquiv p) (rotEquiv p') = wphase α p p' := by
  unfold wphase
  congr 1
  simp only [rotEquiv, Equiv.coe_fn_mk, Int.cast_neg]
  ring

/-- `𝓕(R ⋆ S) = 𝓕R ⋆ 𝓕S`. -/
theorem fourier_tmul (α : ℝ) (R S : Symbol) :
    fourier (tmul α R S) = tmul α (fourier R) (fourier S) := by
  funext p
  simp only [fourier, tmul]
  rw [← rotEquiv.tsum_eq]
  congr 1
  funext p₁
  have hsub : ((-p.2, p.1) : ℤ × ℤ) - rotEquiv p₁ = rotEquiv (p - p₁) := by
    simp [rotEquiv]
    abel
  rw [hsub, wphase_rot]
  simp [rotEquiv]

/-! ### Exponential locality -/

lemma inner_delta_left (n : ℤ) (u : L2 ℤ) : ⟪delta n, u⟫_ℂ = u n := by
  rw [delta, lp.inner_single_left]
  simp

lemma W_delta_apply (α x : ℝ) (r q n m : ℤ) :
    W α x r q (delta m) n = if n + r = m then e (α * r * q / 2 + q * (x + n * α)) else 0 := by
  rw [W_apply, delta]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs <;> simp

/-- **Exponential locality of `𝒲_{s,ℓ}`**: `|⟨δ_n, R_x δ_m⟩| ≤ ‖R‖_{s,ℓ} e^{-s|n-m|}`. -/
theorem norm_entry_le (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) {α : ℝ} {R : Symbol} (hR : WSum s ℓ R)
    (x : ℝ) (n m : ℤ) :
    ‖⟪delta n, op α R x (delta m)⟫_ℂ‖ ≤ wnorm s ℓ R * Real.exp (-s * |((n - m : ℤ) : ℝ)|) := by
  have hR1 := hR.symbolSummable hs hℓ
  have hsum := summable_op_apply (α := α) hR1 x (delta m)
  rw [op_apply hR1]
  have heval : ⟪delta n, ∑' p : ℤ × ℤ, R p • W α x p.1 p.2 (delta m)⟫_ℂ =
      ∑' p : ℤ × ℤ, ⟪delta n, R p • W α x p.1 p.2 (delta m)⟫_ℂ :=
    (hsum.hasSum.mapL (innerSL ℂ (delta n))).tsum_eq.symm
  rw [heval, wnorm_eq, ← tsum_mul_right]
  simp only [inner_smul_right, inner_delta_left]
  have hterm : ∀ p : ℤ × ℤ, ‖R p * W α x p.1 p.2 (delta m) n‖ ≤
      ‖R p‖ * wt s ℓ p * Real.exp (-s * |((n - m : ℤ) : ℝ)|) := by
    intro p
    rw [W_delta_apply, norm_mul]
    split_ifs with h
    · rw [norm_e, mul_one, mul_assoc]
      refine le_mul_of_one_le_right (norm_nonneg _) ?_
      have hp : (p.1 : ℝ) = -((n - m : ℤ) : ℝ) := by push_cast; linarith [(by exact_mod_cast h : (n : ℝ) + p.1 = m)]
      rw [wt, ← Real.exp_add, hp, abs_neg]
      exact Real.one_le_exp (by nlinarith [abs_nonneg ((p.2 : ℤ) : ℝ)])
    · simp only [norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (wt_pos p).le) (Real.exp_pos _).le
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (hR.mul_right _).of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  · exact ((hR.mul_right _).of_nonneg_of_le (fun _ => norm_nonneg _) hterm).tsum_le_tsum hterm
      (hR.mul_right _)

end AMO
