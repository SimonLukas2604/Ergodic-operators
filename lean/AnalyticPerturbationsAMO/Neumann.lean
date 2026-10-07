/-
# The Neumann series in `𝒲_{s,ℓ}`  (paper §2.2)

If `‖L‖_{s,ℓ} < 1` then `I - L` is invertible *inside the weighted algebra*:
`(I - L)^{-1} = ∑_{m ≥ 0} L^{⋆m}` with `‖(I - L)^{-1}‖_{s,ℓ} ≤ (1 - ‖L‖_{s,ℓ})^{-1}`, on every
fibre.  Consequently the inverse is exponentially local:
`|⟨δ_n, (I - L)_x^{-1} δ_m⟩| ≤ (1 - ‖L‖_{s,ℓ})^{-1} e^{-s|n-m|}`.
Everything here is proved.
-/
import AnalyticPerturbationsAMO.WeylAlgebra

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open L2

namespace AMO

variable {α s ℓ : ℝ}

/-! ### The unit symbol -/

/-- The symbol of the identity, `δ_{(0,0)}`. -/
def one : Symbol := Pi.single 0 1

lemma W_zero (α x : ℝ) : W α x 0 0 = 1 := by
  ext u n
  simp [W_apply]

lemma op_one (α x : ℝ) : op α one x = 1 := by
  rw [one, op_single]
  exact (one_smul ℂ _).trans (W_zero α x)

lemma one_wsum : WSum s ℓ one := by
  unfold WSum
  apply summable_of_ne_finset_zero (s := {0})
  intro p hp
  simp only [Finset.mem_singleton] at hp
  simp [one, Pi.single_apply, hp]

lemma wnorm_one : wnorm s ℓ one = 1 := by
  rw [wnorm_eq, tsum_eq_single 0]
  · simp [one, wt]
  · intro p hp
    simp [one, Pi.single_apply, hp]

/-! ### Powers -/

/-- Twisted powers `L^{⋆m}`. -/
def tpow (α : ℝ) (L : Symbol) : ℕ → Symbol
  | 0 => one
  | m + 1 => tmul α L (tpow α L m)

variable {L : Symbol}

lemma WSum.tpow (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hL : WSum s ℓ L) (m : ℕ) :
    WSum s ℓ (tpow α L m) := by
  induction m with
  | zero => exact one_wsum
  | succ m ih => exact WSum.tmul hs hℓ hL ih

lemma wnorm_tpow_le (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hL : WSum s ℓ L) (m : ℕ) :
    wnorm s ℓ (tpow α L m) ≤ wnorm s ℓ L ^ m := by
  induction m with
  | zero => simp [tpow, wnorm_one]
  | succ m ih =>
    calc wnorm s ℓ (tpow α L (m + 1)) ≤ wnorm s ℓ L * wnorm s ℓ (tpow α L m) :=
          wnorm_tmul_le hs hℓ hL (hL.tpow hs hℓ m)
      _ ≤ wnorm s ℓ L * wnorm s ℓ L ^ m := by
          exact mul_le_mul_of_nonneg_left ih
            (tsum_nonneg fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
      _ = wnorm s ℓ L ^ (m + 1) := by ring

lemma op_tpow (hL : SymbolSummable L) (x : ℝ) (m : ℕ) :
    op α (tpow α L m) x = op α L x ^ m := by
  have hs0 : ∀ m, SymbolSummable (tpow α L m) := fun m =>
    ((symbolSummable_iff_wsum_zero.1 hL).tpow le_rfl le_rfl m).symbolSummable le_rfl le_rfl
  induction m with
  | zero => simp [tpow, op_one]
  | succ m ih => rw [tpow, op_tmul hL (hs0 m), ih, pow_succ']

/-! ### The Neumann series -/

/-- `N = ∑_m L^{⋆m}`, the symbol of `(I - L)^{-1}`. -/
def neumann (α : ℝ) (L : Symbol) : Symbol := fun p => ∑' m : ℕ, tpow α L m p

lemma wnorm_nonneg' (L : Symbol) : 0 ≤ wnorm s ℓ L :=
  tsum_nonneg fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le

section

variable (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (hL : WSum s ℓ L) (hq : wnorm s ℓ L < 1)
include hs hℓ hL hq

/-- The double majorant `H(m, p) = |L^{⋆m}_p| w(p)` is summable on `ℕ × ℤ²`. -/
lemma summable_H :
    Summable fun z : ℕ × (ℤ × ℤ) => ‖tpow α L z.1 z.2‖ * wt s ℓ z.2 := by
  refine (summable_prod_of_nonneg (fun z => mul_nonneg (norm_nonneg _) (wt_pos _).le)).2
    ⟨fun m => hL.tpow hs hℓ m, ?_⟩
  refine (summable_geometric_of_lt_one (wnorm_nonneg' L) hq).of_nonneg_of_le
    (fun m => tsum_nonneg fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
    (fun m => wnorm_tpow_le hs hℓ hL m)

lemma summable_tpow_apply (p : ℤ × ℤ) : Summable fun m : ℕ => ‖tpow α L m p‖ := by
  refine ((summable_H (α := α) hs hℓ hL hq).prod_symm.prod_factor p).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun m => ?_)
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_wt hs hℓ p)

/-- `N ∈ 𝒲_{s,ℓ}` and `‖N‖_{s,ℓ} ≤ (1 - ‖L‖_{s,ℓ})^{-1}`. -/
theorem neumann_wsum :
    WSum s ℓ (neumann α L) ∧ wnorm s ℓ (neumann α L) ≤ (1 - wnorm s ℓ L)⁻¹ := by
  have hH := summable_H (α := α) hs hℓ hL hq
  have hpt : ∀ p, ‖neumann α L p‖ * wt s ℓ p ≤ ∑' m : ℕ, ‖tpow α L m p‖ * wt s ℓ p := by
    intro p
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right
      (norm_tsum_le_tsum_norm (summable_tpow_apply hs hℓ hL hq p)) (wt_pos p).le
  have hsw : WSum s ℓ (neumann α L) :=
    hH.prod_symm.prod.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le) hpt
  refine ⟨hsw, ?_⟩
  have hq0 := wnorm_nonneg' (s := s) (ℓ := ℓ) L
  calc wnorm s ℓ (neumann α L) ≤ ∑' p : ℤ × ℤ, ∑' m : ℕ, ‖tpow α L m p‖ * wt s ℓ p :=
        hsw.tsum_le_tsum hpt hH.prod_symm.prod
    _ = ∑' m : ℕ, ∑' p : ℤ × ℤ, ‖tpow α L m p‖ * wt s ℓ p :=
        hH.tsum_comm (f := fun m p => ‖tpow α L m p‖ * wt s ℓ p)
    _ ≤ ∑' m : ℕ, wnorm s ℓ L ^ m :=
        hH.prod.tsum_le_tsum (fun m => wnorm_tpow_le hs hℓ hL m)
          (summable_geometric_of_lt_one hq0 hq)
    _ = (1 - wnorm s ℓ L)⁻¹ := tsum_geometric_of_lt_one hq0 hq

/-- On every fibre, `op(N) = ∑_m op(L)^m`. -/
lemma op_neumann (x : ℝ) : op α (neumann α L) x = ∑' m : ℕ, op α L x ^ m := by
  have hH := summable_H (α := α) hs hℓ hL hq
  have hL1 := hL.symbolSummable hs hℓ
  -- the operator-valued double series
  set F : ℕ → ℤ × ℤ → L2 ℤ →L[ℂ] L2 ℤ := fun m p => tpow α L m p • W α x p.1 p.2
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_norm (hH.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_))
    simp only [Function.uncurry, F]
    rw [norm_smul]
    exact mul_le_mul (le_refl _) ((norm_W_le _ _ _ _).trans (one_le_wt hs hℓ z.2))
      (norm_nonneg _) (norm_nonneg _)
  have hrow : ∀ p, Summable fun m => tpow α L m p :=
    fun p => (summable_tpow_apply hs hℓ hL hq p).of_norm
  calc op α (neumann α L) x = ∑' p : ℤ × ℤ, ∑' m : ℕ, F m p := by
        unfold op
        congr 1
        funext p
        exact ((hrow p).tsum_smul_const (W α x p.1 p.2)).symm
    _ = ∑' m : ℕ, ∑' p : ℤ × ℤ, F m p := hF.tsum_comm
    _ = ∑' m : ℕ, op α L x ^ m := by
        congr 1
        funext m
        rw [← op_tpow hL1 x m]
        rfl

/-- **Neumann series in `𝒲_{s,ℓ}`.**  `op(N)` is a two-sided inverse of `I - op(L)` on every
fibre. -/
theorem neumann_inverse (x : ℝ) :
    (1 - op α L x) * op α (neumann α L) x = 1 ∧ op α (neumann α L) x * (1 - op α L x) = 1 := by
  have hnorm : ‖op α L x‖ < 1 := by
    refine lt_of_le_of_lt (norm_op_le (hL.symbolSummable hs hℓ) x) (lt_of_le_of_lt ?_ hq)
    exact (hL.symbolSummable hs hℓ).tsum_le_tsum
      (fun p => le_mul_of_one_le_right (norm_nonneg _) (one_le_wt hs hℓ p)) hL
  rw [op_neumann hs hℓ hL hq x]
  exact ⟨mul_neg_geom_series _ hnorm, geom_series_mul_neg _ hnorm⟩

/-- **Exponential locality of the inverse**:
`|⟨δ_n, (I - L)_x^{-1} δ_m⟩| ≤ (1 - ‖L‖_{s,ℓ})^{-1} e^{-s|n-m|}`. -/
theorem norm_entry_inverse_le (x : ℝ) (n m : ℤ) :
    ‖⟪delta n, op α (neumann α L) x (delta m)⟫_ℂ‖ ≤
      (1 - wnorm s ℓ L)⁻¹ * Real.exp (-s * |((n - m : ℤ) : ℝ)|) := by
  obtain ⟨hw, hb⟩ := neumann_wsum (α := α) hs hℓ hL hq
  exact (norm_entry_le hs hℓ hw x n m).trans
    (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le)

end

end AMO
