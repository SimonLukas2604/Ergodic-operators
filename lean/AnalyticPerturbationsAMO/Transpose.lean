/-
# The transpose of symbols

`τ R (r, q) = R(-r, q)` is the symbol of the operator transpose (`W_{r,q}ᵀ = W_{-r,q}`).  It is a
`ℂ`-linear isometric **anti-automorphism** of the twisted product,
  `τ(R ⋆ S) = τ S ⋆ τ R`,
fixes phase coefficients and swaps `U ↔ U^{-1}`; it maps hopping `≥ n` to hopping `≤ -n`.
Composed with the adjoint it gives the conjugate-linear **automorphism**
`θ R (r, q) = conj R(r, -q)`, which preserves hopping indices and commutes with `Π_{≥2}` and
the tail inverse `S^{-1}`.  These are used to complexify Lemma 2.1 (no adjoints in the
fixed-point map).  Everything here is proved.
-/
import AnalyticPerturbationsAMO.WeightedSpace

noncomputable section

open scoped ComplexConjugate

namespace AMO

variable {α s ℓ : ℝ}

/-- The transpose `τ R (r, q) = R(-r, q)`. -/
def tsym (R : Symbol) : Symbol := fun p => R (-p.1, p.2)

@[simp] lemma tsym_apply (R : Symbol) (p : ℤ × ℤ) : tsym R p = R (-p.1, p.2) := rfl

lemma tsym_tsym (R : Symbol) : tsym (tsym R) = R := by funext p; simp

lemma tsym_add (R S : Symbol) : tsym (R + S) = tsym R + tsym S := rfl
lemma tsym_sub (R S : Symbol) : tsym (R - S) = tsym R - tsym S := rfl
lemma tsym_smul (c : ℂ) (R : Symbol) : tsym (c • R) = c • tsym R := rfl
lemma tsym_zero : tsym (0 : Symbol) = 0 := rfl

/-- The reflection `(r, q) ↦ (-r, q)`. -/
def reflEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

lemma wt_refl (p : ℤ × ℤ) : wt s ℓ (-p.1, p.2) = wt s ℓ p := by simp [wt]

lemma WSum.tsym {R : Symbol} (h : WSum s ℓ R) : WSum s ℓ (tsym R) := by
  unfold WSum at *
  rw [← reflEquiv.summable_iff] at h
  refine h.congr fun p => ?_
  simp [reflEquiv, wt_refl]

lemma wnorm_tsym (R : Symbol) : wnorm s ℓ (tsym R) = wnorm s ℓ R := by
  rw [wnorm_eq, wnorm_eq, ← reflEquiv.tsum_eq]
  congr 1; funext p
  simp [reflEquiv, wt_refl]

/-- **`τ` reverses twisted products.** -/
theorem tsym_tmul (R S : Symbol) : tsym (tmul α R S) = tmul α (tsym S) (tsym R) := by
  funext p
  simp only [tsym_apply, tmul]
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p₁ => (p₁.1 - p.1, p.2 - p₁.2)
      invFun := fun p₂ => (p₂.1 + p.1, p.2 - p₂.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  rw [← e.tsum_eq]
  congr 1
  funext p₁
  simp only [e, Equiv.coe_fn_mk, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
  have h1 : (-p.1 - (p₁.1 - p.1), p.2 - (p.2 - p₁.2)) = (-p₁.1, p₁.2) := by ext <;> simp <;> ring
  have h2 : (p₁.1 - p.1, p.2 - p₁.2) = (-(p.1 - p₁.1), p.2 - p₁.2) := by ext <;> simp
  rw [h1, h2]
  have hph : wphase α (-(p.1 - p₁.1), p.2 - p₁.2) (-p₁.1, p₁.2) =
      wphase α p₁ (p.1 - p₁.1, p.2 - p₁.2) := by
    unfold wphase; congr 1; push_cast; ring
  rw [hph, show p - p₁ = (p.1 - p₁.1, p.2 - p₁.2) from rfl]
  ring

lemma HopGE.tsym {R : Symbol} {n : ℤ} (h : HopGE R n) : HopLE (tsym R) (-n) := fun p hp =>
  h _ (by simp only; omega)

lemma HopLE.tsym {R : Symbol} {n : ℤ} (h : HopLE R n) : HopGE (tsym R) (-n) := fun p hp =>
  h _ (by simp only; omega)

lemma tsym_u1 : tsym u1 = um1 := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [tsym_apply, u1, um1, Pi.single_apply, Prod.mk.injEq]
  by_cases ha : a = -1 <;> by_cases hb : b = 0 <;> simp [ha, hb] <;> omega

lemma tsym_um1 : tsym um1 = u1 := by rw [← tsym_u1, tsym_tsym]

lemma tsym_hop0 {w : Symbol} (hge : HopGE w 0) (hle : HopLE w 0) : tsym w = w := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [tsym_apply]
  rcases lt_trichotomy a 0 with h | h | h
  · rw [hge (a, b) h, hle (-a, b) (by simp only; omega)]
  · subst h; simp
  · rw [hle (a, b) h, hge (-a, b) (by simp only; omega)]

/-! ### The conjugate-linear automorphism `θ = (·)^* ∘ τ` -/

/-- `θ R (r, q) = conj R(r, -q)`. -/
def tconj (R : Symbol) : Symbol := fun p => conj (R (p.1, -p.2))

lemma tconj_eq (R : Symbol) : tconj R = sstar (tsym R) := by
  funext p; simp [tconj, sstar]

lemma tconj_tmul (R S : Symbol) : tconj (tmul α R S) = tmul α (tconj R) (tconj S) := by
  rw [tconj_eq, tsym_tmul, sstar_tmul, ← tconj_eq, ← tconj_eq]

lemma tconj_P2 (R : Symbol) : tconj (P2 R) = P2 (tconj R) := by
  funext p; simp only [tconj, P2]; split_ifs <;> simp

lemma tconj_Sinv (D : Symbol) : tconj (Sinv α D) = Sinv α (tconj D) := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [tconj, Sinv]
  split_ifs
  · rw [map_mul, Complex.conj_conj]
    congr 1
    · simp
    · unfold wphase
      rw [show (-(b : ℤ) : ℤ) = -b from rfl]
      simp only [e, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      congr 1
      push_cast
      ring
  · simp

lemma tconj_add (R S : Symbol) : tconj (R + S) = tconj R + tconj S := by
  funext p; simp [tconj]

lemma tconj_sub (R S : Symbol) : tconj (R - S) = tconj R - tconj S := by
  funext p; simp [tconj]

lemma tconj_real_smul (c : ℝ) (R : Symbol) : tconj ((c : ℂ) • R) = (c : ℂ) • tconj R := by
  funext p; simp [tconj]

lemma tconj_u1 : tconj u1 = u1 := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [tconj, u1, Pi.single_apply, Prod.mk.injEq]
  by_cases ha : a = 1 <;> by_cases hb : b = 0 <;> simp [ha, hb]

lemma tconj_um1 : tconj um1 = um1 := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [tconj, um1, Pi.single_apply, Prod.mk.injEq]
  by_cases ha : a = -1 <;> by_cases hb : b = 0 <;> simp [ha, hb]

lemma tconj_tconj (R : Symbol) : tconj (tconj R) = R := by funext p; simp [tconj]

lemma WSum.tconj {R : Symbol} (h : WSum s ℓ R) : WSum s ℓ (tconj R) := by
  unfold WSum at *
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1, -p.2), invFun := fun p => (p.1, -p.2),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  rw [← e.summable_iff] at h
  refine h.congr fun p => ?_
  simp [e, AMO.tconj, wt]

/-! ### On `𝒲_{s,ℓ}` -/

namespace Weights

variable (ω : Weights) (α : ℝ)

/-- The transpose on `𝒲_{s,ℓ}`. -/
def tr' (f : WA) : WA := ω.ofS (tsym (ω.toS f)) (ω.toS_wsum f).tsym

@[simp] lemma toS_tr' (f : WA) : ω.toS (ω.tr' f) = tsym (ω.toS f) := ω.toS_ofS _ _

lemma norm_tr' (f : WA) : ‖ω.tr' f‖ = ‖f‖ := by
  rw [← ω.wnorm_toS, toS_tr', wnorm_tsym, ω.wnorm_toS]

lemma tr'_tr' (f : WA) : ω.tr' (ω.tr' f) = f := by
  apply ω.toS_injective; simp [tsym_tsym]

lemma tr'_add (f g : WA) : ω.tr' (f + g) = ω.tr' f + ω.tr' g := by
  apply ω.toS_injective; simp [ω.toS_add, tsym_add]

lemma tr'_sub (f g : WA) : ω.tr' (f - g) = ω.tr' f - ω.tr' g := by
  apply ω.toS_injective; simp [ω.toS_sub, tsym_sub]

lemma tr'_smul (c : ℂ) (f : WA) : ω.tr' (c • f) = c • ω.tr' f := by
  apply ω.toS_injective; simp [ω.toS_smul, tsym_smul]

lemma tr'_zero : ω.tr' 0 = 0 := by
  have := ω.tr'_smul 0 0; simpa using this

lemma tr'_mul (f g : WA) : ω.tr' (ω.mul α f g) = ω.mul α (ω.tr' g) (ω.tr' f) := by
  apply ω.toS_injective; simp [ω.toS_mul, tsym_tmul]

/-- `θ` on `𝒲_{s,ℓ}`. -/
def tc' (f : WA) : WA := ω.ofS (tconj (ω.toS f)) (ω.toS_wsum f).tconj

@[simp] lemma toS_tc' (f : WA) : ω.toS (ω.tc' f) = tconj (ω.toS f) := ω.toS_ofS _ _

lemma tc'_eq (f : WA) : ω.tc' f = ω.star (ω.tr' f) := by
  apply ω.toS_injective; simp [toS_star, tconj_eq]

lemma tc'_mul (f g : WA) : ω.tc' (ω.mul α f g) = ω.mul α (ω.tc' f) (ω.tc' g) := by
  apply ω.toS_injective; simp [ω.toS_mul, tconj_tmul]

lemma tc'_P2' (f : WA) : ω.tc' (ω.P2' f) = ω.P2' (ω.tc' f) := by
  apply ω.toS_injective; simp [toS_P2', tconj_P2]

lemma tc'_Sinv' (f : WA) : ω.tc' (ω.Sinv' α f) = ω.Sinv' α (ω.tc' f) := by
  apply ω.toS_injective; simp [toS_Sinv', tconj_Sinv]

lemma tc'_add (f g : WA) : ω.tc' (f + g) = ω.tc' f + ω.tc' g := by
  apply ω.toS_injective; simp [ω.toS_add, tconj_add]

lemma tc'_sub (f g : WA) : ω.tc' (f - g) = ω.tc' f - ω.tc' g := by
  apply ω.toS_injective; simp [ω.toS_sub, tconj_sub]

lemma tc'_real_smul (c : ℝ) (f : WA) : ω.tc' ((c : ℂ) • f) = (c : ℂ) • ω.tc' f := by
  apply ω.toS_injective
  rw [toS_tc', ω.toS_smul, ω.toS_smul, toS_tc', tconj_real_smul]

end Weights

lemma tsym_sstar (R : Symbol) : tsym (sstar R) = sstar (tsym R) := by
  funext p; simp [sstar]

namespace Weights

variable (ω : Weights)

lemma tr'_star (f : WA) : ω.tr' (ω.star f) = ω.star (ω.tr' f) := by
  apply ω.toS_injective; simp [toS_star, tsym_sstar]

lemma tc'_tr' (f : WA) : ω.tc' (ω.tr' f) = ω.star f := by
  rw [tc'_eq, tr'_tr']

lemma tr'_tc' (f : WA) : ω.tr' (ω.tc' f) = ω.star f := by
  rw [tc'_eq, tr'_star, tr'_tr']

end Weights

end AMO
