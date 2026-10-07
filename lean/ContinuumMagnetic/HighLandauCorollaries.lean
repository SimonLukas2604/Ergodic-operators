/-
# High Landau levels: the remaining statements  (paper §1.4, Corollaries `cor:high-energy-fibres`,
`cor:high-critical-dimension`, and the `W = 0` case of Theorem `thm:high-energy-spectrum`)

This file proves, from the analytic input `PaperInputs` and the exact Landau-band reduction
`LandauReductionClaim`:

* `high_landau_fibres` — **Corollary `cor:high-energy-fibres`** (off-critical part): for every good
  index the spectrum of almost every physical Bloch fibre `H(k)|_{Ran Π_n(k)}` is the cluster `𝒞_n`;
  for `a_y > a_x` the fibres are purely absolutely continuous; for `a_x > a_y` there is a complete
  eigenbasis on `{𝓛_n > β(α_B)}`, no a.c. component, pure singular continuity on `{𝓛_n < β(α_B)}`,
  the explicit sufficient conditions `β < log(a_x/a_y) - C‖R_n‖` and `β > log(a_x/a_y) + C‖R_n‖`,
  and localization of the whole cluster when `β(α_B) = 0`;
* `high_landau_fibres_critical` — **Corollary `cor:high-energy-fibres`** (iv): in the
  rotation-symmetric critical case, `β(α_B) > 0` gives purely singular continuous fibres;
* `high_landau_critical_dimension` — **Corollary `cor:high-critical-dimension`**: every internal
  allowed gap of `𝒞_n` is open and `𝓗^{1/2}(𝒞_n) < ∞`; at ordinary Liouville reciprocal flux
  `dim_H 𝒞_n = 0`;
* `high_landau_W0`, `high_landau_critical_dimension_W0` — the statements for `W = 0` on the
  density-one set `𝒢₀` of indices with `|cos(2√(n s_B) - π/4)| ≥ n^{-1/8}`.

The proofs are organized around two per-cluster lemmas (`cluster_offcritical`, `cluster_critical`)
and two selection lemmas producing clusters with a small normalized remainder
(`exists_small_cluster`, `exists_small_cluster_G0`).

Deviation: the fibre reductions are assumed for almost every Bloch momentum `k`, so the fibre
statements hold for almost every `k` (the paper states the spectral identity and (iv) for every `k`).
-/
import ContinuumMagnetic.MainTheorems

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Set Filter Topology AMO

namespace CMS

/-! ### Selection of clusters with a small remainder -/

section Selection

variable {h B Vbar ax ay σ ρ C : ℝ} {w : Symbol} {δ : ℕ → ℝ}

/-- For good indices (`Kε ≤ |cos(2√(n s_B) - π/4)|` with `K = 4C/ε'`) the normalized remainder is
`ε'`-small in the analytic norm. -/
lemma exists_small_cluster (hC : 0 < C) (hδ : Tendsto δ atTop (𝓝 0))
    (hred : ∀ᶠ n in atTop, goodCos h B n ≠ 0 → ∃ D : LandauCluster h B Vbar ax ay w n,
      (Summable fun p : ℤ × ℤ => ‖D.R p‖ * Real.exp (σ * |(p.1 : ℝ)| + σ * |(p.2 : ℝ)|)) ∧
      wnorm σ σ D.R * goodCos h B n ≤ C * (wnorm ρ ρ w / aStar ax ay) + δ n ∧
      (ax = ay → AMO.fourier w = w → AMO.fourier D.R = D.R))
    (hastar : 0 < aStar ax ay) {ε' : ℝ} (hε' : 0 < ε') {ε : ℝ} (hε : 0 < ε)
    (hW : wnorm ρ ρ w ≤ ε * aStar ax ay) :
    ∀ᶠ n in atTop, 4 * C / ε' * ε ≤ goodCos h B n → ∃ D : LandauCluster h B Vbar ax ay w n,
      WSmall σ σ D.R ε' ∧ (ax = ay → AMO.fourier w = w → AMO.fourier D.R = D.R) := by
  filter_upwards [hred, hδ.eventually (Iio_mem_nhds (mul_pos hC hε))] with n hn hδn hgood
  have hK : 0 < 4 * C / ε' := by positivity
  have hcos : goodCos h B n ≠ 0 := ((mul_pos hK hε).trans_le hgood).ne'
  obtain ⟨D, hsum, hbound, hsymm⟩ := hn hcos
  have hw0 : 0 ≤ wnorm σ σ D.R := tsum_nonneg fun p => by positivity
  have hr := landau_remainder_small hC hK hε hastar hW hδn.le hgood hw0 hbound
  have : 2 * C / (4 * C / ε') = ε' / 2 := by field_simp; ring
  rw [this] at hr
  exact ⟨D, ⟨hsum, by linarith⟩, hsymm⟩

/-- For `W = 0` and indices in `𝒢₀` (`|cos(2√(n s_B) - π/4)| ≥ n^{-1/8}`) the normalized
remainder is eventually `ε'`-small. -/
lemma exists_small_cluster_G0 (hδ8 : Tendsto (fun n : ℕ => δ n * (n : ℝ) ^ (1 / 8 : ℝ)) atTop (𝓝 0))
    (hred : ∀ᶠ n in atTop, goodCos h B n ≠ 0 → ∃ D : LandauCluster h B Vbar ax ay 0 n,
      (Summable fun p : ℤ × ℤ => ‖D.R p‖ * Real.exp (σ * |(p.1 : ℝ)| + σ * |(p.2 : ℝ)|)) ∧
      wnorm σ σ D.R * goodCos h B n ≤ C * (wnorm ρ ρ (0 : Symbol) / aStar ax ay) + δ n ∧
      (ax = ay → AMO.fourier (0 : Symbol) = 0 → AMO.fourier D.R = D.R))
    {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ n in atTop, n ∈ G0 (sB h B) → ∃ D : LandauCluster h B Vbar ax ay 0 n,
      WSmall σ σ D.R ε' ∧ (ax = ay → AMO.fourier D.R = D.R) := by
  filter_upwards [hred, hδ8.eventually (Iio_mem_nhds hε')] with n hn hδn hG
  obtain ⟨hn1, hcosG⟩ := hG
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : 0 < (n : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hnpos _
  have hcos' : (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ goodCos h B n := hcosG
  have hcos : goodCos h B n ≠ 0 := (hpow.trans_le hcos').ne'
  obtain ⟨D, hsum, hbound, hsymm⟩ := hn hcos
  have hw0 : 0 ≤ wnorm σ σ D.R := tsum_nonneg fun p => by positivity
  have hwz : wnorm ρ ρ (0 : Symbol) = 0 := by simp [wnorm]
  rw [hwz, zero_div, mul_zero, zero_add] at hbound
  have h1 : wnorm σ σ D.R * (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ δ n :=
    (mul_le_mul_of_nonneg_left hcos' hw0).trans hbound
  have h2 : (n : ℝ) ^ (-(1 / 8 : ℝ)) * (n : ℝ) ^ (1 / 8 : ℝ) = 1 := by
    rw [← Real.rpow_add hnpos]; simp
  have h3 : wnorm σ σ D.R ≤ δ n * (n : ℝ) ^ (1 / 8 : ℝ) := by
    have := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hnpos.le (1 / 8 : ℝ))
    rwa [mul_assoc, h2, mul_one] at this
  exact ⟨D, ⟨hsum, h3.trans_lt hδn⟩, fun hxy => hsymm hxy (by funext p; rfl)⟩

end Selection

/-! ### Per-cluster conclusions -/

section Cluster

variable {h B Vbar ax ay : ℝ} {w : Symbol} {n : ℕ}

/-- The cluster energy `E_n`, scale `a_* f_n` and coupling `η = min(a_x,a_y)/a_*`. -/
abbrev clE (_D : LandauCluster h B Vbar ax ay w n) : ℝ := landauLevel h B Vbar n
abbrev clA (_D : LandauCluster h B Vbar ax ay w n) : ℝ := aStar ax ay * landauFormFactor n (sB h B)
abbrev clEta (_D : LandauCluster h B Vbar ax ay w n) : ℝ := min ax ay / aStar ax ay

lemma LandauCluster.scale_ne (D : LandauCluster h B Vbar ax ay w n) (hax : 0 < ax) :
    clA D ≠ 0 :=
  mul_ne_zero (lt_max_of_lt_left hax).ne' D.formFactor_ne

/-- **The off-critical cluster** (Theorem `thm:high-energy-spectrum` (i) and Corollary
`cor:high-energy-fibres` (i)–(iii)), given the Paper I conclusions for the normalized
interaction. -/
theorem cluster_offcritical (D : LandauCluster h B Vbar ax ay w n)
    (hα : Irrational (alphaB h B)) (hax : 0 < ax) (hR : SymbolSummable D.R) {Cst ε : ℝ}
    (hD : DryTenMartini (alphaB h B) (clEta D) D.R)
    (hT : SpectralTransition (alphaB h B) (clEta D) D.R Cst ε) :
    D.cluster = affine (clE D) (clA D) '' Sigma (alphaB h B) (clEta D) D.R ∧
    IsCantor D.cluster ∧
    (∃ ν, IsDOSMeasure (op (alphaB h B) (islandSym (clE D) (clA D) true (clEta D) D.R)) ν ∧
      AllGapsOpen D.cluster ν (alphaB h B)) ∧
    0 < volume D.cluster ∧ dimH D.cluster = 1 ∧ PurelyACH D.A ∧
    (∀ᵐ k ∂volume, spectrum ℝ (D.fibre k) = D.cluster) ∧
    (ax < ay → ∀ᵐ k ∂volume, PurelyACH (D.fibre k)) ∧
    (ay ≤ ax → ∃ Lsup : ℝ → ℝ,
      (∀ E ∈ Sigma (alphaB h B) (clEta D) D.R,
        0 < Lsup E ∧ |Lsup E - Real.log (1 / clEta D)| ≤ Cst * ε) ∧
      (∀ᵐ k ∂volume, HasCompleteEigenbasisOn (D.fibre k)
        (affine (clE D) (clA D) '' locRegion (Sigma (alphaB h B) (clEta D) D.R) Lsup (alphaB h B))) ∧
      (∀ᵐ k ∂volume, NoACComponentH (D.fibre k)) ∧
      (∀ᵐ k ∂volume, PurelySCOnH (D.fibre k)
        (affine (clE D) (clA D) '' scRegion (Sigma (alphaB h B) (clEta D) D.R) Lsup (alphaB h B)))) := by
  set α := alphaB h B
  set E := clE D
  set a := clA D
  set η := clEta D
  have ha : a ≠ 0 := D.scale_ne hax
  have hsa := D.R_sa
  have hspec : ∀ (sub : Bool) (x : ℝ), spectrum ℝ (op α (islandSym E a sub η D.R) x) =
      affine E a '' Sigma α η D.R := fun sub x =>
    islandSpec_eq α E a sub η hα hR hsa hD.dual_spectrum x
  have hcl : D.cluster = affine E a '' Sigma α η D.R := D.realization.spec.trans (hspec true 0)
  obtain ⟨ν, hνH, -, hgaps⟩ := hD.gaps
  obtain ⟨ν', hν'H, hac⟩ := hT.ids_ac
  have hνν' : ν = ν' := hνH.unique hν'H
  subst hνν'
  have := hνH.1
  have hat : ∀ t, ν {t} = 0 := fun t => hac Real.volume_singleton
  have hsaH := isSelfAdjoint_H α η hR hsa
  have hνc : IsDOSMeasure (op α (islandSym E a true η D.R)) (ν.map (affine E a)) := by
    rw [show op α (islandSym E a true η D.R) = fun x => affineOp E a (H α η D.R x) from
      funext (op_islandSym α E a true η hR)]
    exact hνH.map_affine hsaH E a
  have hpos := hT.volume_Sigma_pos hα hR hsa
  have hv : 0 < volume (affine E a '' Sigma α η D.R) := by
    refine pos_iff_ne_zero.2 fun h0 => hpos.1.ne' ?_
    have := volume_preimage_affine (E₀ := E) ha h0
    rwa [preimage_image_eq _ (affine_injective ha)] at this
  refine ⟨hcl, ?_, ⟨_, hνc, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcl]; exact hD.cantor.image_affine E ha
  · rw [hcl]; exact hgaps.map_affine_ne hat hα E ha
  · rw [hcl]; exact hv
  · rw [hcl]; exact dimH_eq_one_of_volume_pos hv
  · exact purelyACH_of_dominated (D.realization.dom _ hνc) (AbsolutelyContinuous.map_affine hac ha)
  · filter_upwards [D.fibre_reduction] with k hk
    exact hk.spectrum_real_eq.trans ((hspec _ _).trans hcl.symm)
  · intro hlt
    have hdec : decide (ax < ay) = true := decide_eq_true hlt
    have hred := D.fibre_reduction
    rw [hdec] at hred
    filter_upwards [ae_phase hT.ac D.θ, hred] with k h1 h2
    have h3 := h1.affineOp (isSelfAdjoint_H α η hR hsa _) E ha
    rw [← op_physSym_true, ← op_islandSym α E a true η hR] at h3
    exact purelyACH_of_purelyAC h3 h2
  · intro hle
    have hdec : decide (ax < ay) = false := decide_eq_false (not_lt.2 hle)
    have hred := D.fibre_reduction
    rw [hdec] at hred
    obtain ⟨Lsup, -, hb, hloc, hnoac, -, hsc⟩ := hT.exponent
    have hsaD := isSelfAdjoint_Hdual α η hR hsa
    have hop : ∀ x, affineOp E a (Hdual α η D.R x) = op α (islandSym E a false η D.R) x :=
      fun x => by rw [← op_physSym_false, ← op_islandSym α E a false η hR]
    refine ⟨Lsup, hb, ?_, ?_, ?_⟩
    · filter_upwards [ae_phase hloc D.θ, hred] with k h1 h2
      have h3 := h1.affineOp (hsaD _) E ha
      rw [hop] at h3
      exact hasCompleteEigenbasisOn_of_andersonLocalizedOn h3 h2
    · filter_upwards [ae_phase hnoac D.θ, hred] with k h1 h2
      have h3 := h1.affineOp (hsaD _) E ha
      rw [hop] at h3
      exact noACComponentH_of_noACComponent h3 h2
    · filter_upwards [ae_phase hsc D.θ, hred] with k h1 h2
      have h3 := h1.affineOp (hsaD _) E ha
      rw [hop] at h3
      exact purelySCOnH_of_purelySCOn h3 h2

/-- In the rotation-symmetric case the realization and fibre symbols are the critical symbol
`E_n δ₀ + a_* f_n (U + U⁻¹ + V + V⁻¹ + R_n)`. -/
lemma LandauCluster.critical_symbols (D : LandauCluster h B Vbar ax ax w n) (hax : 0 < ax)
    (hF : AMO.fourier D.R = D.R) :
    DominatedRealization (alphaB h B) (critSym (clE D) (clA D) D.R) D.A ∧
    ∀ᵐ k ∂volume, Intertwines (D.Uk k)
      (op (alphaB h B) (critSym (clE D) (clA D) D.R) ((k + D.θ) / (2 * Real.pi))) (D.fibre k) := by
  have hη1 : (min ax ax / aStar ax ax : ℝ) = 1 := by
    rw [min_self, aStar, max_self, div_self hax.ne']
  have hreal := D.realization
  rw [hη1, Complex.ofReal_one] at hreal
  have hred := D.fibre_reduction
  have hdec : decide (ax < ax) = false := decide_eq_false (lt_irrefl ax)
  rw [hdec, hη1] at hred
  have hsym : islandSym (clE D) (clA D) false 1 D.R = critSym (clE D) (clA D) D.R := by
    show affineSym _ _ (AMO.fourier (amo ((1 : ℝ) : ℂ) + D.R)) = affineSym _ _ (amo 1 + D.R)
    rw [AMO.fourier_add, Complex.ofReal_one, fourier_amo_one, hF]
  rw [hsym] at hred
  exact ⟨hreal, hred⟩

/-- **The critical cluster** (Theorem `thm:high-energy-spectrum` (ii) and Corollary
`cor:high-energy-fibres` (iv)), given the Paper I critical conclusions. -/
theorem cluster_critical (D : LandauCluster h B Vbar ax ax w n) (hα : Irrational (alphaB h B))
    (hax : 0 < ax) (hR : SymbolSummable D.R) (hF : AMO.fourier D.R = D.R)
    (hcantor : IsCantor (Sigma (alphaB h B) 1 D.R)) (hnull : volume (Sigma (alphaB h B) 1 D.R) = 0)
    (hfib : 0 < beta (alphaB h B) → ∀ x, PurelySC (H (alphaB h B) 1 D.R x))
    {ν : Measure ℝ} (hν : IsDOSMeasure (H (alphaB h B) 1 D.R) ν) (hat : ∀ t, ν {t} = 0) :
    D.cluster = islandSpec (alphaB h B) (critSym (clE D) (clA D) D.R) ∧
    IsCantor D.cluster ∧ volume D.cluster = 0 ∧ PurelySCH D.A ∧
    (0 < beta (alphaB h B) → ∀ᵐ k ∂volume, PurelySCH (D.fibre k)) := by
  set α := alphaB h B
  set E := clE D
  set a := clA D
  have ha : a ≠ 0 := D.scale_ne hax
  have hsa := D.R_sa
  obtain ⟨hreal, hred⟩ := D.critical_symbols hax hF
  have hspecx : ∀ x, spectrum ℝ (op α (critSym E a D.R) x) = affine E a '' Sigma α 1 D.R :=
    islandSpec_critSym hα hR hsa
  have hcl0 : D.cluster = islandSpec α (critSym E a D.R) := hreal.spec
  have hcl : D.cluster = affine E a '' Sigma α 1 D.R := hcl0.trans (hspecx 0)
  have hsaH := isSelfAdjoint_H α 1 hR hsa
  have hνc : IsDOSMeasure (op α (critSym E a D.R)) (ν.map (affine E a)) := by
    rw [show op α (critSym E a D.R) = fun x => affineOp E a (H α 1 D.R x) from
      funext (op_critSym _ E a hR)]
    exact hν.map_affine hsaH E a
  have hvol : volume (affine E a '' Sigma α 1 D.R) = 0 := volume_image_affine ha hnull
  have hclosed : IsClosed (affine E a '' Sigma α 1 D.R) := by
    rw [← hspecx 0]; exact AMO.spectrum_real_isClosed _
  have hcarried : ν.map (affine E a) (affine E a '' Sigma α 1 D.R)ᶜ = 0 := by
    refine dos_compl_eq_zero hνc hclosed (hcantor.image_affine E ha).1 ?_ (fun x => (hspecx x).le)
    intro x
    rw [op_critSym _ E a hR x]
    exact IsSelfAdjoint.affineOp E a (hsaH x)
  refine ⟨hcl0, hcl ▸ hcantor.image_affine E ha, hcl ▸ hvol,
    purelySCH_of_dominated (hreal.dom _ hνc) (atomless_map_affine hat E ha)
      hclosed.measurableSet hcarried hvol, fun hβ => ?_⟩
  filter_upwards [hred] with k h2
  have h3 := (hfib hβ ((k + D.θ) / (2 * Real.pi))).affineOp (hsaH _) E ha
  rw [← op_critSym α E a hR] at h3
  exact purelySCH_of_purelySC h3 h2

end Cluster

/-! ### The theorems -/

section Theorems

lemma symbolSelfAdjoint_zero : SymbolSelfAdjoint (0 : Symbol) := fun p => by simp

lemma summable_zero_weighted (ρ : ℝ) :
    Summable fun p : ℤ × ℤ => ‖(0 : Symbol) p‖ * Real.exp (ρ * |(p.1 : ℝ)| + ρ * |(p.2 : ℝ)|) := by
  simpa using (summable_zero : Summable fun _ : ℤ × ℤ => (0 : ℝ))

/-- **Theorem `thm:high-energy-spectrum` for `W = 0`.**  Both conclusions of the theorem hold for
all sufficiently large `n` in the density-one set
`𝒢₀ = {n ≥ 1 : |cos(2√(n s_B) - π/4)| ≥ n^{-1/8}}`. -/
theorem high_landau_W0 (P : PaperInputs) (hred : LandauReductionClaim) :
    ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∃ S > (0 : ℝ),
      ∀ {h B Vbar ax ay : ℝ}, 0 < h → 0 < B → 0 < ax → 0 < ay → Irrational (alphaB h B) →
      ∀ {σ ρ : ℝ}, (ax ≠ ay → max s₀ (Real.log (A / (min ax ay / aStar ax ay))) < σ) →
        (ax = ay → S < σ) → σ < ρ →
        HasNatDensity (G0 (sB h B)) 1 ∧
        ∀ᶠ n in atTop, n ∈ G0 (sB h B) → ∃ D : LandauCluster h B Vbar ax ay 0 n,
          (ax ≠ ay → IsCantor D.cluster ∧
            (∃ ν, IsDOSMeasure (op (alphaB h B) (islandSym (clE D) (clA D) true (clEta D) D.R)) ν ∧
              AllGapsOpen D.cluster ν (alphaB h B)) ∧
            0 < volume D.cluster ∧ dimH D.cluster = 1 ∧ PurelyACH D.A) ∧
          (ax = ay → IsCantor D.cluster ∧ volume D.cluster = 0 ∧ PurelySCH D.A) := by
  obtain ⟨A, hA, s₀, hs₀, hin⟩ := analytic_input P.dryTenMartini P.spectralTransition
  obtain ⟨S₁, hS₁, ε₁, hε₁, hcrit⟩ := analytic_input_iv P.critical
  obtain ⟨S₂, hS₂, ε₂, hε₂, hids⟩ := P.criticalIDS
  refine ⟨A, hA, s₀, hs₀, max S₁ S₂, lt_max_of_lt_left hS₁, ?_⟩
  intro h B Vbar ax ay hh hB hax hay hα σ ρ hσsub hσcrit hσρ
  have hastar : 0 < aStar ax ay := lt_max_of_lt_left hax
  have hσ : 0 < σ := by
    by_cases hxy : ax = ay
    · exact (lt_max_of_lt_left hS₁).trans (hσcrit hxy)
    · exact (hs₀.trans_le (le_max_left _ _)).trans (hσsub hxy)
  obtain ⟨C, hC, δ, hδ, hδ8, hredn⟩ := hred (Vbar := Vbar) (w := 0) hh hB hax hay hα
    symbolSelfAdjoint_zero (by simp) hσ hσρ (summable_zero_weighted ρ)
  refine ⟨G0_density hh hB, ?_⟩
  by_cases hxy : ax = ay
  · subst hxy
    have hσS : max S₁ S₂ ≤ σ := (hσcrit rfl).le
    filter_upwards [exists_small_cluster_G0 hδ8 hredn (lt_min hε₁ hε₂)] with n hn hG
    obtain ⟨D, hW, hsymm⟩ := hn hG
    have hF := hsymm rfl
    have h₁ : WSmall S₁ S₁ D.R ε₁ := WSmall.of_le
      (hW.mono_weights ((le_max_left _ _).trans hσS) ((le_max_left _ _).trans hσS))
      (min_le_left _ _)
    have h₂ : WSmall S₂ S₂ D.R ε₂ := WSmall.of_le
      (hW.mono_weights ((le_max_right _ _).trans hσS) ((le_max_right _ _).trans hσS))
      (min_le_right _ _)
    have hR : SymbolSummable D.R := h₁.summable hS₁.le hS₁.le
    obtain ⟨hcantor, hnull, -, hfib⟩ := hcrit _ D.R hα D.R_sa hF h₁
    obtain ⟨ν, hν, hat⟩ := hids _ D.R hα D.R_sa hF h₂
    obtain ⟨-, hc, hv, hsc, -⟩ := cluster_critical D hα hax hR hF hcantor hnull hfib hν hat
    exact ⟨D, fun h' => absurd rfl h', fun _ => ⟨hc, hv, hsc⟩⟩
  · have hη0 : 0 < min ax ay / aStar ax ay := div_pos (lt_min hax hay) hastar
    have hη1 : min ax ay / aStar ax ay < 1 := by
      rw [div_lt_one hastar]
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · rw [min_eq_left hlt.le, aStar, max_eq_right hlt.le]; exact hlt
      · rw [min_eq_right hgt.le, aStar, max_eq_left hgt.le]; exact hgt
    obtain ⟨εs, hεs, Cst, -, hthm⟩ := hin (1 - min ax ay / aStar ax ay) ⟨by linarith, by linarith⟩
    have hσs := hσsub hxy
    filter_upwards [exists_small_cluster_G0 hδ8 hredn hεs] with n hn hG
    obtain ⟨D, hW, -⟩ := hn hG
    have hsmall : WSmall s₀ (Real.log (A / (min ax ay / aStar ax ay))) D.R εs :=
      hW.mono_weights ((le_max_left _ _).trans hσs.le) ((le_max_right _ _).trans hσs.le)
    have hlog : 0 ≤ Real.log (A / (min ax ay / aStar ax ay)) := Real.log_nonneg (by
      rw [le_div_iff₀ hη0]; linarith)
    have hR : SymbolSummable D.R := hsmall.summable hs₀.le hlog
    obtain ⟨hD, hT⟩ := hthm _ _ D.R hα hη0 (by linarith) D.R_sa hsmall
    obtain ⟨-, hc, hg, hv, hd, hac, -⟩ := cluster_offcritical D hα hax hR hD hT
    exact ⟨D, fun _ => ⟨hc, hg, hv, hd, hac⟩, fun h' => absurd h' hxy⟩

/-- **Corollary `cor:high-energy-fibres`** (i)–(iii).  For every good index, almost every
physical Bloch fibre restricted to the cluster has spectrum `𝒞_n`; for `a_y > a_x` it is purely
absolutely continuous; for `a_x > a_y` the prepared exponent `𝓛_n` satisfies
`|𝓛_n - log(a_x/a_y)| ≤ C‖R_n‖`, the fibre has a complete eigenbasis on `{𝓛_n > β(α_B)}`,
no absolutely continuous component, and is purely singular continuous on `{𝓛_n < β(α_B)}`;
the whole cluster is localized if `β(α_B) < log(a_x/a_y) - C‖R_n‖` (in particular if
`β(α_B) = 0`) and purely singular continuous if `β(α_B) > log(a_x/a_y) + C‖R_n‖`. -/
theorem high_landau_fibres (P : PaperInputs) (hred : LandauReductionClaim) :
    ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ),
      ∀ {h B Vbar ax ay : ℝ}, 0 < h → 0 < B → 0 < ax → 0 < ay → ax ≠ ay →
      Irrational (alphaB h B) → ∀ {w : Symbol}, SymbolSelfAdjoint w →
      (w 0 = 0 ∧ w (1, 0) = 0 ∧ w (-1, 0) = 0 ∧ w (0, 1) = 0 ∧ w (0, -1) = 0) →
      ∀ {σ ρ : ℝ}, max s₀ (Real.log (A / (min ax ay / aStar ax ay))) < σ → σ < ρ →
        (Summable fun p : ℤ × ℤ => ‖w p‖ * Real.exp (ρ * |(p.1 : ℝ)| + ρ * |(p.2 : ℝ)|)) →
      ∃ K > (0 : ℝ), ∃ Cst > (0 : ℝ), ∀ ε, 0 < ε → wnorm ρ ρ w ≤ ε * aStar ax ay →
        ∀ᶠ n in atTop, K * ε ≤ goodCos h B n → ∃ D : LandauCluster h B Vbar ax ay w n,
          (∀ᵐ k ∂volume, spectrum ℝ (D.fibre k) = D.cluster) ∧
          (ax < ay → ∀ᵐ k ∂volume, PurelyACH (D.fibre k)) ∧
          (ay < ax →
            (∃ Lsup : ℝ → ℝ,
              (∀ E ∈ Sigma (alphaB h B) (clEta D) D.R, 0 < Lsup E ∧
                |Lsup E - Real.log (1 / clEta D)| ≤
                  Cst * wnorm s₀ (Real.log (A / clEta D)) D.R) ∧
              (∀ᵐ k ∂volume, HasCompleteEigenbasisOn (D.fibre k) (affine (clE D) (clA D) ''
                locRegion (Sigma (alphaB h B) (clEta D) D.R) Lsup (alphaB h B))) ∧
              (∀ᵐ k ∂volume, NoACComponentH (D.fibre k)) ∧
              (∀ᵐ k ∂volume, PurelySCOnH (D.fibre k) (affine (clE D) (clA D) ''
                scRegion (Sigma (alphaB h B) (clEta D) D.R) Lsup (alphaB h B)))) ∧
            (beta (alphaB h B) < ENNReal.ofReal (Real.log (1 / clEta D) -
                Cst * wnorm s₀ (Real.log (A / clEta D)) D.R) →
              ∀ᵐ k ∂volume, HasCompleteEigenbasisOn (D.fibre k) D.cluster) ∧
            (beta (alphaB h B) = 0 → ∀ᵐ k ∂volume, HasCompleteEigenbasisOn (D.fibre k) D.cluster) ∧
            (ENNReal.ofReal (Real.log (1 / clEta D) +
                Cst * wnorm s₀ (Real.log (A / clEta D)) D.R) < beta (alphaB h B) →
              ∀ᵐ k ∂volume, PurelySCOnH (D.fibre k) D.cluster)) := by
  obtain ⟨A, hA, s₀, hs₀, hin⟩ := analytic_input P.dryTenMartini P.spectralTransition
  refine ⟨A, hA, s₀, hs₀, ?_⟩
  intro h B Vbar ax ay hh hB hax hay hxy hα w hw hw0 σ ρ hσs hσρ hwρ
  have hastar : 0 < aStar ax ay := lt_max_of_lt_left hax
  have hσ : 0 < σ := (hs₀.trans_le (le_max_left _ _)).trans hσs
  set η := min ax ay / aStar ax ay with hηdef
  have hη0 : 0 < η := div_pos (lt_min hax hay) hastar
  have hη1 : η < 1 := by
    rw [hηdef, div_lt_one hastar]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · rw [min_eq_left hlt.le, aStar, max_eq_right hlt.le]; exact hlt
    · rw [min_eq_right hgt.le, aStar, max_eq_left hgt.le]; exact hgt
  have hL : 0 < Real.log (1 / η) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hη0, hη1⟩)
  obtain ⟨εs, hεs, Cst, hCst, hthm⟩ := hin (1 - η) ⟨by linarith, by linarith⟩
  obtain ⟨C, hC, δ, hδ, -, hredn⟩ := hred (Vbar := Vbar) hh hB hax hay hα hw hw0 hσ hσρ hwρ
  set ε' := min εs (Real.log (1 / η) / (2 * Cst)) with hε'def
  have hε' : 0 < ε' := lt_min hεs (by positivity)
  refine ⟨4 * C / ε', by positivity, Cst, hCst, fun ε hε hW => ?_⟩
  filter_upwards [exists_small_cluster hC hδ hredn hastar hε' hε hW] with n hn hgood
  obtain ⟨D, hWσ, -⟩ := hn hgood
  have hsmall : WSmall s₀ (Real.log (A / η)) D.R ε' :=
    hWσ.mono_weights ((le_max_left _ _).trans hσs.le) ((le_max_right _ _).trans hσs.le)
  have hlog : 0 ≤ Real.log (A / η) := Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)
  have hR : SymbolSummable D.R := hsmall.summable hs₀.le hlog
  obtain ⟨hD, hT⟩ := hthm _ η D.R hα hη0 (by linarith) D.R_sa
    (WSmall.of_le hsmall (min_le_left _ _))
  obtain ⟨hcl, -, -, -, -, -, hspecf, hacf, hsuper⟩ := cluster_offcritical D hα hax hR hD hT
  refine ⟨D, hspecf, hacf, fun hlt => ?_⟩
  obtain ⟨Lsup, hb, hloc, hnoac, hsc⟩ := hsuper hlt.le
  have hb' : ∀ E ∈ Sigma (alphaB h B) η D.R, 0 < Lsup E ∧
      |Lsup E - Real.log (1 / η)| ≤ Cst * wnorm s₀ (Real.log (A / η)) D.R := hb
  have hεn : Cst * wnorm s₀ (Real.log (A / η)) D.R < Real.log (1 / η) / 2 := by
    have h1 : wnorm s₀ (Real.log (A / η)) D.R < Real.log (1 / η) / (2 * Cst) :=
      hsmall.2.trans_le (min_le_right _ _)
    have h2 : Cst * (Real.log (1 / η) / (2 * Cst)) = Real.log (1 / η) / 2 := by
      field_simp
    calc Cst * wnorm s₀ (Real.log (A / η)) D.R < Cst * (Real.log (1 / η) / (2 * Cst)) :=
          mul_lt_mul_of_pos_left h1 hCst
      _ = Real.log (1 / η) / 2 := h2
  have hloc_all : beta (alphaB h B) < ENNReal.ofReal (Real.log (1 / η) -
      Cst * wnorm s₀ (Real.log (A / η)) D.R) →
      ∀ᵐ k ∂volume, HasCompleteEigenbasisOn (D.fibre k) D.cluster := by
    intro hβ
    have hreg : locRegion (Sigma (alphaB h B) η D.R) Lsup (alphaB h B) = Sigma (alphaB h B) η D.R :=
      locRegion_eq_of_lt fun E hE => hβ.trans_le (ENNReal.ofReal_le_ofReal (by
        have := (abs_le.1 (hb' E hE).2).1; linarith))
    rw [hcl]
    rwa [hreg] at hloc
  refine ⟨⟨Lsup, hb, hloc, hnoac, hsc⟩, hloc_all, fun hβ0 => hloc_all ?_, fun hβ => ?_⟩
  · rw [hβ0]
    exact ENNReal.ofReal_pos.2 (by linarith)
  · have hβ' : ENNReal.ofReal (Real.log (1 / η) + Cst * wnorm s₀ (Real.log (A / η)) D.R) <
        beta (alphaB h B) := hβ
    have hreg : scRegion (Sigma (alphaB h B) η D.R) Lsup (alphaB h B) = Sigma (alphaB h B) η D.R :=
      scRegion_eq_of_gt fun E hE => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by
        have := (abs_le.1 (hb' E hE).2).2; linarith)) hβ'
    rw [hcl]
    rwa [hreg] at hsc

/-- **Corollary `cor:high-energy-fibres`** (iv): in the rotation-symmetric critical case, if
`β(α_B) > 0` then almost every fibre restricted to the cluster is purely singular continuous. -/
theorem high_landau_fibres_critical (P : PaperInputs) (hred : LandauReductionClaim) :
    ∃ S > (0 : ℝ), ∀ {h B Vbar a₀ : ℝ}, 0 < h → 0 < B → 0 < a₀ → Irrational (alphaB h B) →
      ∀ {w : Symbol}, SymbolSelfAdjoint w →
      (w 0 = 0 ∧ w (1, 0) = 0 ∧ w (-1, 0) = 0 ∧ w (0, 1) = 0 ∧ w (0, -1) = 0) →
      AMO.fourier w = w → ∀ {σ ρ : ℝ}, S < σ → σ < ρ →
        (Summable fun p : ℤ × ℤ => ‖w p‖ * Real.exp (ρ * |(p.1 : ℝ)| + ρ * |(p.2 : ℝ)|)) →
      ∃ K > (0 : ℝ), ∀ ε, 0 < ε → wnorm ρ ρ w ≤ ε * aStar a₀ a₀ →
        ∀ᶠ n in atTop, K * ε ≤ goodCos h B n → ∃ D : LandauCluster h B Vbar a₀ a₀ w n,
          0 < beta (alphaB h B) → ∀ᵐ k ∂volume, PurelySCH (D.fibre k) := by
  obtain ⟨S₁, hS₁, ε₁, hε₁, hcrit⟩ := analytic_input_iv P.critical
  obtain ⟨S₂, hS₂, ε₂, hε₂, hids⟩ := P.criticalIDS
  refine ⟨max S₁ S₂, lt_max_of_lt_left hS₁, ?_⟩
  intro h B Vbar a₀ hh hB ha₀ hα w hw hw0 hFw σ ρ hσS hσρ hwρ
  have hastar : 0 < aStar a₀ a₀ := lt_max_of_lt_left ha₀
  have hσ : 0 < σ := (lt_max_of_lt_left hS₁).trans hσS
  obtain ⟨C, hC, δ, hδ, -, hredn⟩ := hred (Vbar := Vbar) hh hB ha₀ ha₀ hα hw hw0 hσ hσρ hwρ
  have hε' : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  refine ⟨4 * C / min ε₁ ε₂, by positivity, fun ε hε hW => ?_⟩
  filter_upwards [exists_small_cluster hC hδ hredn hastar hε' hε hW] with n hn hgood
  obtain ⟨D, hWσ, hsymm⟩ := hn hgood
  have hF := hsymm rfl hFw
  have h₁ : WSmall S₁ S₁ D.R ε₁ := WSmall.of_le
    (hWσ.mono_weights ((le_max_left _ _).trans hσS.le) ((le_max_left _ _).trans hσS.le))
    (min_le_left _ _)
  have h₂ : WSmall S₂ S₂ D.R ε₂ := WSmall.of_le
    (hWσ.mono_weights ((le_max_right _ _).trans hσS.le) ((le_max_right _ _).trans hσS.le))
    (min_le_right _ _)
  have hR : SymbolSummable D.R := h₁.summable hS₁.le hS₁.le
  obtain ⟨hcantor, hnull, -, hfib⟩ := hcrit _ D.R hα D.R_sa hF h₁
  obtain ⟨ν, hν, hat⟩ := hids _ D.R hα D.R_sa hF h₂
  exact ⟨D, (cluster_critical D hα ha₀ hR hF hcantor hnull hfib hν hat).2.2.2.2⟩

/-- The critical cluster is the island spectrum of the critical symbol. -/
lemma LandauCluster.cluster_eq_crit {h B Vbar a₀ : ℝ} {w : Symbol} {n : ℕ}
    (D : LandauCluster h B Vbar a₀ a₀ w n) (ha₀ : 0 < a₀) (hF : AMO.fourier D.R = D.R) :
    D.cluster = islandSpec (alphaB h B) (critSym (clE D) (clA D) D.R) :=
  (D.critical_symbols ha₀ hF).1.spec

/-- **Corollary `cor:high-critical-dimension`.**  In the rotation-symmetric critical case, for each
irrational reciprocal flux there is a critical stability weight `S_*(α_B)` such that, for every
analytic reserve `σ ≥ S_*` and width `ρ > σ`, there are `K, ε₀ > 0` with: if `‖W‖_ρ ≤ ε a_*`,
`0 < ε < ε₀`, `Kε < 1`, then the good indices have density `1 - (2/π) arcsin(Kε)` and for all large
good `n` every internal allowed gap of `𝒞_n` is open, `𝓗^{1/2}(𝒞_n) < ∞`, and
`dim_H 𝒞_n = 0` at ordinary Liouville reciprocal flux.  One choice works for every gap label. -/
theorem high_landau_critical_dimension (P : PaperInputs) (hred : LandauReductionClaim)
    {h B Vbar a₀ : ℝ} (hh : 0 < h) (hB : 0 < B) (ha₀ : 0 < a₀) (hα : Irrational (alphaB h B)) :
    ∃ Sstar > (0 : ℝ), ∀ {w : Symbol}, SymbolSelfAdjoint w →
      (w 0 = 0 ∧ w (1, 0) = 0 ∧ w (-1, 0) = 0 ∧ w (0, 1) = 0 ∧ w (0, -1) = 0) →
      AMO.fourier w = w → ∀ {σ ρ : ℝ}, Sstar ≤ σ → σ < ρ →
        (Summable fun p : ℤ × ℤ => ‖w p‖ * Real.exp (ρ * |(p.1 : ℝ)| + ρ * |(p.2 : ℝ)|)) →
      ∃ K > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ → K * ε < 1 →
        wnorm ρ ρ w ≤ ε * aStar a₀ a₀ →
        HasNatDensity {n | K * ε ≤ goodCos h B n} (1 - 2 / Real.pi * Real.arcsin (K * ε)) ∧
        ∀ᶠ n in atTop, K * ε ≤ goodCos h B n → ∃ D : LandauCluster h B Vbar a₀ a₀ w n,
          (∃ ν, IsDOSMeasure (op (alphaB h B) (critSym (clE D) (clA D) D.R)) ν ∧
            AllGapsOpen D.cluster ν (alphaB h B)) ∧
          μH[1 / 2] D.cluster < ⊤ ∧
          (OrdinaryLiouville (alphaB h B) → dimH D.cluster = 0) := by
  obtain ⟨Sstar, hSs, hgeo⟩ := critical_continuum_geometry P (alphaB h B) hα
  refine ⟨Sstar, hSs, fun {w} hw hw0 hFw {σ ρ} hσS hσρ hwρ => ?_⟩
  have hσ : 0 < σ := hSs.trans_le hσS
  have hastar : 0 < aStar a₀ a₀ := lt_max_of_lt_left ha₀
  obtain ⟨ρg, hρg, hρgeo⟩ := hgeo σ hσS
  obtain ⟨ρL, hρL, hliou⟩ : ∃ ρL > (0 : ℝ), OrdinaryLiouville (alphaB h B) →
      ∀ (E₀ a : ℝ) (R : Symbol), a ≠ 0 → SymbolSelfAdjoint R → AMO.fourier R = R →
        WSmall σ σ R ρL → dimH (islandSpec (alphaB h B) (critSym E₀ a R)) = 0 := by
    by_cases hL : OrdinaryLiouville (alphaB h B)
    · obtain ⟨ρL, hρL, h⟩ := critical_continuum_liouville P _ hα hL σ hσ
      exact ⟨ρL, hρL, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hL⟩
  obtain ⟨C, hC, δ, hδ, -, hredn⟩ := hred (Vbar := Vbar) hh hB ha₀ ha₀ hα hw hw0 hσ hσρ hwρ
  have hε' : 0 < min ρg ρL := lt_min hρg hρL
  refine ⟨4 * C / min ρg ρL, by positivity, 1, one_pos, fun ε hε _ hKε hW =>
    ⟨goodIndex_density hh hB (by positivity) hKε.le, ?_⟩⟩
  filter_upwards [exists_small_cluster hC hδ hredn hastar hε' hε hW] with n hn hgood
  obtain ⟨D, hWσ, hsymm⟩ := hn hgood
  have hF := hsymm rfl hFw
  have ha : clA D ≠ 0 := D.scale_ne ha₀
  have hcl := D.cluster_eq_crit ha₀ hF
  obtain ⟨hgaps, hH, -⟩ := hρgeo (clE D) (clA D) D.R ha D.R_sa hF (WSmall.of_le hWσ (min_le_left _ _))
  refine ⟨D, ?_, by rw [hcl]; exact hH, fun hL => by
    rw [hcl]; exact hliou hL _ _ _ ha D.R_sa hF (WSmall.of_le hWσ (min_le_right _ _))⟩
  obtain ⟨ν, hν, hg⟩ := hgaps
  exact ⟨ν, hν, by rw [hcl]; exact hg⟩

/-- **Corollary `cor:high-critical-dimension` for `W = 0`**: the conclusions hold on the
density-one set `𝒢₀`, without an additional width hypothesis beyond `σ ≥ S_*`. -/
theorem high_landau_critical_dimension_W0 (P : PaperInputs) (hred : LandauReductionClaim)
    {h B Vbar a₀ : ℝ} (hh : 0 < h) (hB : 0 < B) (ha₀ : 0 < a₀) (hα : Irrational (alphaB h B)) :
    ∃ Sstar > (0 : ℝ), ∀ {σ ρ : ℝ}, Sstar ≤ σ → σ < ρ →
      HasNatDensity (G0 (sB h B)) 1 ∧
      ∀ᶠ n in atTop, n ∈ G0 (sB h B) → ∃ D : LandauCluster h B Vbar a₀ a₀ 0 n,
        (∃ ν, IsDOSMeasure (op (alphaB h B) (critSym (clE D) (clA D) D.R)) ν ∧
          AllGapsOpen D.cluster ν (alphaB h B)) ∧
        μH[1 / 2] D.cluster < ⊤ ∧
        (OrdinaryLiouville (alphaB h B) → dimH D.cluster = 0) := by
  obtain ⟨Sstar, hSs, hgeo⟩ := critical_continuum_geometry P (alphaB h B) hα
  refine ⟨Sstar, hSs, fun {σ ρ} hσS hσρ => ⟨G0_density hh hB, ?_⟩⟩
  have hσ : 0 < σ := hSs.trans_le hσS
  obtain ⟨ρg, hρg, hρgeo⟩ := hgeo σ hσS
  obtain ⟨ρL, hρL, hliou⟩ : ∃ ρL > (0 : ℝ), OrdinaryLiouville (alphaB h B) →
      ∀ (E₀ a : ℝ) (R : Symbol), a ≠ 0 → SymbolSelfAdjoint R → AMO.fourier R = R →
        WSmall σ σ R ρL → dimH (islandSpec (alphaB h B) (critSym E₀ a R)) = 0 := by
    by_cases hL : OrdinaryLiouville (alphaB h B)
    · obtain ⟨ρL, hρL, h⟩ := critical_continuum_liouville P _ hα hL σ hσ
      exact ⟨ρL, hρL, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hL⟩
  obtain ⟨C, hC, δ, hδ, hδ8, hredn⟩ := hred (Vbar := Vbar) (w := 0) hh hB ha₀ ha₀ hα
    symbolSelfAdjoint_zero (by simp) hσ hσρ (summable_zero_weighted ρ)
  filter_upwards [exists_small_cluster_G0 hδ8 hredn (lt_min hρg hρL)] with n hn hG
  obtain ⟨D, hWσ, hsymm⟩ := hn hG
  have hF := hsymm rfl
  have ha : clA D ≠ 0 := D.scale_ne ha₀
  have hcl := D.cluster_eq_crit ha₀ hF
  obtain ⟨hgaps, hH, -⟩ := hρgeo (clE D) (clA D) D.R ha D.R_sa hF (WSmall.of_le hWσ (min_le_left _ _))
  refine ⟨D, ?_, by rw [hcl]; exact hH, fun hL => by
    rw [hcl]; exact hliou hL _ _ _ ha D.R_sa hF (WSmall.of_le hWσ (min_le_right _ _))⟩
  obtain ⟨ν, hν, hg⟩ := hgaps
  exact ⟨ν, hν, by rw [hcl]; exact hg⟩

end Theorems

end CMS
