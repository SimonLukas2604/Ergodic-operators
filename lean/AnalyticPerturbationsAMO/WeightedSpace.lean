/-
# `𝒲_{s,ℓ}` as a Banach space

A symbol `R` with `‖R‖_{s,ℓ} < ∞` is represented by its weighted coefficients
`p ↦ R_p e^{s|r| + ℓ|q|}` in `ℓ¹(ℤ²)`, which is complete.  The twisted product, involution,
projection `Π_{≥2}` and the tail inverse `S^{-1}` are transported to this space with their norm
bounds.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.SymbolCalculus

noncomputable section

open scoped ComplexConjugate ENNReal

namespace AMO

/-- Nonnegative analytic weights `(s, ℓ)`. -/
structure Weights where
  s : ℝ
  ℓ : ℝ
  hs : 0 ≤ s
  hℓ : 0 ≤ ℓ

/-- The Banach space `ℓ¹(ℤ²)` carrying weighted coefficients. -/
abbrev WA := lp (fun _ : ℤ × ℤ => ℂ) 1

namespace Weights

variable (ω : Weights) (α : ℝ)

lemma memℓp_one_iff (f : ℤ × ℤ → ℂ) : Memℓp f 1 ↔ Summable fun p => ‖f p‖ := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

lemma norm_WA (f : WA) : ‖f‖ = ∑' p, ‖f p‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

/-- The symbol represented by `f`. -/
def toS (f : WA) : Symbol := fun p => f p / wt ω.s ω.ℓ p

/-- The representative of a symbol of finite weighted norm. -/
def ofS (R : Symbol) (h : WSum ω.s ω.ℓ R) : WA :=
  ⟨fun p => R p * wt ω.s ω.ℓ p, (memℓp_one_iff _).2 (h.congr fun p => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos p)])⟩

lemma wt_ne (p : ℤ × ℤ) : (wt ω.s ω.ℓ p : ℂ) ≠ 0 := by
  exact_mod_cast (wt_pos p).ne'

@[simp] lemma toS_ofS (R : Symbol) (h : WSum ω.s ω.ℓ R) : ω.toS (ω.ofS R h) = R := by
  funext p
  simp only [toS, ofS]
  change R p * _ / _ = R p
  rw [mul_div_assoc, div_self (ω.wt_ne p), mul_one]

lemma toS_wsum (f : WA) : WSum ω.s ω.ℓ (ω.toS f) := by
  have hf : Summable fun p => ‖f p‖ := (memℓp_one_iff _).1 (lp.memℓp f)
  refine hf.congr (fun p => ?_)
  simp only [toS, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos p)]
  rw [div_mul_cancel₀ _ (wt_pos p).ne']

@[simp] lemma ofS_toS (f : WA) : ω.ofS (ω.toS f) (ω.toS_wsum f) = f := by
  ext p
  simp only [ofS, toS]
  change f p / _ * _ = f p
  rw [div_mul_cancel₀ _ (ω.wt_ne p)]

lemma norm_ofS (R : Symbol) (h : WSum ω.s ω.ℓ R) : ‖ω.ofS R h‖ = wnorm ω.s ω.ℓ R := by
  rw [norm_WA, wnorm_eq]
  congr 1
  funext p
  change ‖R p * (wt ω.s ω.ℓ p : ℂ)‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos p)]

lemma wnorm_toS (f : WA) : wnorm ω.s ω.ℓ (ω.toS f) = ‖f‖ := by
  rw [← ω.norm_ofS _ (ω.toS_wsum f), ofS_toS]

lemma toS_add (f g : WA) : ω.toS (f + g) = ω.toS f + ω.toS g := by
  funext p; simp [toS, add_div]

lemma toS_sub (f g : WA) : ω.toS (f - g) = ω.toS f - ω.toS g := by
  funext p; simp [toS, sub_div]

lemma toS_smul (c : ℂ) (f : WA) : ω.toS (c • f) = c • ω.toS f := by
  funext p; simp [toS, mul_div_assoc]

lemma toS_zero : ω.toS 0 = 0 := by
  funext p; simp [toS]

lemma toS_injective : Function.Injective ω.toS := by
  intro f g h
  rw [← ω.ofS_toS f, ← ω.ofS_toS g]
  congr 1

lemma ofS_eq_iff {R : Symbol} (h : WSum ω.s ω.ℓ R) (f : WA) : ω.ofS R h = f ↔ R = ω.toS f :=
  ⟨fun e => by rw [← e, toS_ofS], fun e => by subst e; exact ω.ofS_toS f⟩

/-! ### Transported operations -/

lemma WSum.sstar' {R : Symbol} (h : WSum ω.s ω.ℓ R) : WSum ω.s ω.ℓ (sstar R) := by
  unfold WSum at *
  have := ((Equiv.neg (ℤ × ℤ)).summable_iff (f := fun p => ‖R p‖ * wt ω.s ω.ℓ p)).2 h
  refine this.congr (fun p => ?_)
  simp [sstar, wt]

/-- The product in `𝒲_{s,ℓ}`. -/
def mul (f g : WA) : WA :=
  ω.ofS (tmul α (ω.toS f) (ω.toS g)) (WSum.tmul ω.hs ω.hℓ (ω.toS_wsum f) (ω.toS_wsum g))

/-- The involution in `𝒲_{s,ℓ}`. -/
def star (f : WA) : WA := ω.ofS (sstar (ω.toS f)) (WSum.sstar' ω (ω.toS_wsum f))

/-- `Π_{≥2}` in `𝒲_{s,ℓ}`. -/
def P2' (f : WA) : WA := ω.ofS (P2 (ω.toS f)) (ω.toS_wsum f).P2

/-- `S^{-1}` in `𝒲_{s,ℓ}`. -/
def Sinv' (f : WA) : WA := ω.ofS (Sinv α (ω.toS f)) (Sinv_wsum ω.hs (ω.toS_wsum f)).1

@[simp] lemma toS_mul (f g : WA) : ω.toS (ω.mul α f g) = tmul α (ω.toS f) (ω.toS g) := by
  simp [mul]

@[simp] lemma toS_star (f : WA) : ω.toS (ω.star f) = sstar (ω.toS f) := by simp [star]

@[simp] lemma toS_P2' (f : WA) : ω.toS (ω.P2' f) = P2 (ω.toS f) := by simp [P2']

@[simp] lemma toS_Sinv' (f : WA) : ω.toS (ω.Sinv' α f) = Sinv α (ω.toS f) := by simp [Sinv']

lemma norm_mul_le (f g : WA) : ‖ω.mul α f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [mul, norm_ofS, ← ω.wnorm_toS f, ← ω.wnorm_toS g]
  exact wnorm_tmul_le ω.hs ω.hℓ (ω.toS_wsum f) (ω.toS_wsum g)

lemma norm_star (f : WA) : ‖ω.star f‖ = ‖f‖ := by
  rw [star, norm_ofS, wnorm_sstar, wnorm_toS]

lemma norm_P2'_le (f : WA) : ‖ω.P2' f‖ ≤ ‖f‖ := by
  rw [P2', norm_ofS, ← ω.wnorm_toS f]
  exact wnorm_P2_le (ω.toS_wsum f)

lemma norm_Sinv'_le (f : WA) : ‖ω.Sinv' α f‖ ≤ Real.exp (-ω.s) * ‖f‖ := by
  rw [Sinv', norm_ofS, ← ω.wnorm_toS f]
  exact (Sinv_wsum ω.hs (ω.toS_wsum f)).2

lemma toS_summable (f : WA) : SymbolSummable (ω.toS f) :=
  (ω.toS_wsum f).symbolSummable ω.hs ω.hℓ

lemma mul_add (f g h : WA) : ω.mul α f (g + h) = ω.mul α f g + ω.mul α f h := by
  apply ω.toS_injective
  simp only [toS_mul, toS_add]
  exact tmul_add_right (ω.toS_summable f) (ω.toS_summable g) (ω.toS_summable h)

lemma add_mul (f g h : WA) : ω.mul α (f + g) h = ω.mul α f h + ω.mul α g h := by
  apply ω.toS_injective
  simp only [toS_mul, toS_add]
  exact tmul_add_left (ω.toS_summable f) (ω.toS_summable g) (ω.toS_summable h)

lemma mul_sub (f g h : WA) : ω.mul α f (g - h) = ω.mul α f g - ω.mul α f h := by
  apply ω.toS_injective
  simp only [toS_mul, toS_sub]
  exact tmul_sub_right (ω.toS_summable f) (ω.toS_summable g) (ω.toS_summable h)

lemma sub_mul (f g h : WA) : ω.mul α (f - g) h = ω.mul α f h - ω.mul α g h := by
  apply ω.toS_injective
  simp only [toS_mul, toS_sub]
  exact tmul_sub_left (ω.toS_summable f) (ω.toS_summable g) (ω.toS_summable h)

lemma mul_smul (c : ℂ) (f g : WA) : ω.mul α f (c • g) = c • ω.mul α f g := by
  apply ω.toS_injective
  simp only [toS_mul, toS_smul, tmul_smul_right]

lemma smul_mul (c : ℂ) (f g : WA) : ω.mul α (c • f) g = c • ω.mul α f g := by
  apply ω.toS_injective
  simp only [toS_mul, toS_smul, tmul_smul_left]

lemma star_sub (f g : WA) : ω.star (f - g) = ω.star f - ω.star g := by
  apply ω.toS_injective
  simp only [toS_star, toS_sub, sstar_sub]

lemma P2'_sub (f g : WA) : ω.P2' (f - g) = ω.P2' f - ω.P2' g := by
  apply ω.toS_injective
  simp only [toS_P2', toS_sub, P2_sub]

lemma P2'_add (f g : WA) : ω.P2' (f + g) = ω.P2' f + ω.P2' g := by
  apply ω.toS_injective
  simp only [toS_P2', toS_add, P2_add]

lemma P2'_smul (c : ℂ) (f : WA) : ω.P2' (c • f) = c • ω.P2' f := by
  apply ω.toS_injective
  simp only [toS_P2', toS_smul, P2_smul]

lemma Sinv'_sub (f g : WA) : ω.Sinv' α (f - g) = ω.Sinv' α f - ω.Sinv' α g := by
  apply ω.toS_injective
  simp only [toS_Sinv', toS_sub, Sinv_sub]

lemma Sinv'_smul (c : ℂ) (f : WA) : ω.Sinv' α (c • f) = c • ω.Sinv' α f := by
  apply ω.toS_injective
  simp only [toS_Sinv', toS_smul, Sinv_smul]

/-- `‖a • b - a' • b'‖` style bilinear difference bound. -/
lemma norm_mul_sub_mul_le (f f' g g' : WA) :
    ‖ω.mul α f g - ω.mul α f' g'‖ ≤ ‖f - f'‖ * ‖g‖ + ‖f'‖ * ‖g - g'‖ := by
  have : ω.mul α f g - ω.mul α f' g' = ω.mul α (f - f') g + ω.mul α f' (g - g') := by
    rw [ω.sub_mul, ω.mul_sub]; abel
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add (ω.norm_mul_le α _ _) (ω.norm_mul_le α _ _))

lemma mul_assoc' (f g h : WA) : ω.mul α (ω.mul α f g) h = ω.mul α f (ω.mul α g h) := by
  apply ω.toS_injective
  simp only [toS_mul]
  exact tmul_assoc (ω.toS_summable f) (ω.toS_summable g) (ω.toS_summable h)

lemma star_mul (f g : WA) : ω.star (ω.mul α f g) = ω.mul α (ω.star g) (ω.star f) := by
  apply ω.toS_injective
  simp only [toS_star, toS_mul, sstar_tmul]

lemma star_star (f : WA) : ω.star (ω.star f) = f := by
  apply ω.toS_injective
  simp only [toS_star, sstar_sstar]

lemma star_add (f g : WA) : ω.star (f + g) = ω.star f + ω.star g := by
  apply ω.toS_injective
  simp only [toS_star, toS_add, sstar_add]

lemma star_real_smul (c : ℝ) (f : WA) : ω.star ((c : ℂ) • f) = (c : ℂ) • ω.star f := by
  apply ω.toS_injective
  simp only [toS_star, toS_smul, sstar_smul, Complex.conj_ofReal]

/-- The unit of `𝒲_{s,ℓ}`. -/
def one' : WA := ω.ofS one one_wsum

@[simp] lemma toS_one' : ω.toS ω.one' = one := by simp [one']

lemma one'_mul (f : WA) : ω.mul α ω.one' f = f := by
  apply ω.toS_injective; simp [one_tmul]

lemma mul_one' (f : WA) : ω.mul α f ω.one' = f := by
  apply ω.toS_injective; simp [tmul_one]

lemma star_one' : ω.star ω.one' = ω.one' := by
  apply ω.toS_injective; simp [sstar_one]

lemma mul_zero' (f : WA) : ω.mul α f 0 = 0 := by
  have := ω.mul_sub α f 0 0
  simpa using this

lemma zero_mul' (f : WA) : ω.mul α 0 f = 0 := by
  have := ω.sub_mul α 0 0 f
  simpa using this

lemma star_zero' : ω.star 0 = 0 := by
  have := ω.star_sub 0 0
  simpa using this

lemma isSelfAdjoint_iff (f : WA) : ω.star f = f ↔ SymbolSelfAdjoint (ω.toS f) := by
  rw [← sstar_eq_iff, ← toS_star]
  exact ⟨fun h => by rw [h], fun h => ω.toS_injective h⟩

lemma continuous_star : Continuous ω.star := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun f g => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← ω.star_sub, ω.norm_star]
  simp

lemma isClosed_selfAdjoint : IsClosed {f : WA | ω.star f = f} :=
  isClosed_eq ω.continuous_star continuous_id

end Weights

/-! ### An abstract contraction principle -/

/-- **Banach fixed point on a closed set.** -/
theorem exists_fixed_of_contract {X : Type*} [MetricSpace X] [CompleteSpace X] {S : Set X}
    (hS : IsClosed S) {x₀ : X} (hx₀ : x₀ ∈ S) {f : X → X} (hmaps : Set.MapsTo f S S)
    {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hlip : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ k * dist x y) : ∃ z ∈ S, f z = z := by
  have hc : ContractingWith ⟨k, hk0⟩ (hmaps.restrict f S S) := by
    refine ⟨by exact_mod_cast hk1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    exact hlip x x.2 y y.2
  obtain ⟨y, hy, hfix, -⟩ :=
    hc.exists_fixedPoint' hS.isComplete hmaps hx₀ (edist_ne_top x₀ (f x₀))
  exact ⟨y, hy, hfix⟩

end AMO
