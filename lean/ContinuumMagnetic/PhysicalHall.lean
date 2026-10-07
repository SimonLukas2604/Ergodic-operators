/-
# Physical density of states and Hall integers  (paper Theorem `thm:physical-hall` and Lemma
`lem:magnetic-gap-persistence`)

**Theorem `thm:physical-hall`.**  Lemma `lem:physical-trace` (the exact reductions identify the
physical trace per unit area with the normalized IDS), the continuum gap labelling and the
persistence of gaps in the field give, near the field `𝓑`, a physical density of the Fermi
projection equal to a *local line* in the field, `r/μ - k𝓑'/(2πh)` (low energy) or
`r B'/(2πh) + k` (high energy).  The Hall integer is the Středa derivative
`Ch = 2πh ∂_B T` (`CMS.stredaChern`).  Here we take that local-line identity as the hypothesis
(it is what Lemmas `lem:physical-trace` and `lem:magnetic-gap-persistence` provide; their proofs
need the trace per unit area of unbounded magnetic operators, which is not formalized) and prove:

* `physical_hall_low`: `Ch_𝓑(Q_h(E)) = -k` for a gap with label `N_h(E) = r + kα`, and in particular
  `-k` for the label `{kα}`;
* `physical_hall_high`: `Ch_B(Q_n(E)) = r` for `N_n(E) = r + kα_B`, and `-⌊kα_B⌋` for `{kα_B}`;
* `physical_hall_full`: `Ch(P_h) = 0` and `Ch(Π_n) = 1`.

**Lemma `lem:magnetic-gap-persistence`** is stated as the two-sided Hölder-½ bound
`GapPersistenceBound` on a field-indexed family of spectra, and its consequence — every compact
interval in a gap stays in the resolvent set for all sufficiently close fields — is proved
(`gap_persists`).
-/
import ContinuumMagnetic.HallLabels
import ContinuumMagnetic.GoodIndices

noncomputable section

open Filter Topology Set Metric

namespace CMS

/-! ### Středa derivative of eventually equal densities -/

lemma stredaChern_congr {h B : ℝ} {T T' : ℝ → ℝ} (hT : T =ᶠ[𝓝 B] T') :
    stredaChern h T B = stredaChern h T' B := by
  unfold stredaChern; rw [hT.deriv_eq]

/-! ### Theorem `thm:physical-hall` -/

/-- **Theorem `thm:physical-hall` (i)** (low energy).  If near the field `𝓑` the physical
density of `Q_h(E)` is `N_h(E)/μ` with the persisting label `N_h(E) = r + kα(𝓑')`,
`α(𝓑') = -μ𝓑'/(2πh)`, then the Hall integer of `Q_h(E)` is `-k`; for the label `{k₀α}` it is
`-k₀`. -/
theorem physical_hall_low {μ h B : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) {T : ℝ → ℝ} {r k : ℤ}
    (hT : ∀ᶠ B' in 𝓝 B, T B' = lowDensity μ (r + k * freq (fieldParam μ h B'))) :
    stredaChern h T B = -k ∧
      ∀ k₀ : ℤ, Irrational (freq (fieldParam μ h B)) →
        (r : ℝ) + k * freq (fieldParam μ h B) = Int.fract (k₀ * freq (fieldParam μ h B)) →
        stredaChern h T B = -k₀ := by
  have hline : T =ᶠ[𝓝 B] lowLine μ h r k := by
    filter_upwards [hT] with B' hB'
    rw [hB', lowDensity_eq_lowLine hμ hh r k B']
  have hch : stredaChern h T B = -k := by
    rw [stredaChern_congr hline, stredaChern_lowLine hh r k B, lowHall]
    push_cast; ring
  refine ⟨hch, fun k₀ hirr hlab => ?_⟩
  have hl : HasLabel (freq (fieldParam μ h B)) (Int.fract (k₀ * freq (fieldParam μ h B))) r k :=
    hlab.symm
  rw [hch, (label_of_fract hirr hl).2]

/-- **Theorem `thm:physical-hall` (ii)** (high energy).  If near the field `B` the physical
density of `Q_n(E)` is `(B'/2πh) N_n(E)` with the persisting label `N_n(E) = r + kα_{B'}`,
`α_{B'} = 2πh/B'`, then the Hall integer of `Q_n(E)` is `r`; for the label `{k₀α_B}` it is
`-⌊k₀α_B⌋`. -/
theorem physical_hall_high {h B : ℝ} (hB : B ≠ 0) (hh : h ≠ 0) {T : ℝ → ℝ} {r k : ℤ}
    (hT : ∀ᶠ B' in 𝓝 B, T B' = highDensity B' h (r + k * alphaB h B')) :
    stredaChern h T B = r ∧
      ∀ k₀ : ℤ, Irrational (alphaB h B) →
        (r : ℝ) + k * alphaB h B = Int.fract (k₀ * alphaB h B) →
        stredaChern h T B = -⌊(k₀ : ℝ) * alphaB h B⌋ := by
  have hline : T =ᶠ[𝓝 B] highLine h r k := by
    filter_upwards [hT, eventually_ne_nhds hB] with B' hB' hne
    rw [hB', alphaB, highDensity_eq_highLine hne hh r k]
  have hch : stredaChern h T B = r := by
    rw [stredaChern_congr hline, stredaChern_highLine hh r k B, highHall]
  refine ⟨hch, fun k₀ hirr hlab => ?_⟩
  have hl : HasLabel (alphaB h B) (Int.fract (k₀ * alphaB h B)) r k := hlab.symm
  rw [hch, (label_of_fract hirr hl).1]
  push_cast; ring

/-- **Theorem `thm:physical-hall`, full projections:** the scalar island projection `P_h` (density
`1/μ`) has Hall integer `0`, and the Landau cluster projection `Π_n` (density `B'/2πh`) has Hall
integer `1`. -/
theorem physical_hall_full {μ h B : ℝ} (hh : h ≠ 0) {T₁ T₂ : ℝ → ℝ}
    (h₁ : ∀ᶠ B' in 𝓝 B, T₁ B' = 1 / μ) (h₂ : ∀ᶠ B' in 𝓝 B, T₂ B' = B' / (2 * Real.pi * h)) :
    stredaChern h T₁ B = 0 ∧ stredaChern h T₂ B = 1 := by
  constructor
  · rw [stredaChern_congr (h₁ : T₁ =ᶠ[𝓝 B] fun _ => 1 / μ), stredaChern_fullLow]
  · rw [stredaChern_congr (h₂ : T₂ =ᶠ[𝓝 B] fun B' => B' / (2 * Real.pi * h)),
      stredaChern_fullHigh hh]

/-- **Every nonzero relative Hall integer is realized** (paper, after Theorem
`thm:physical-hall`): for irrational `α` and `m ≠ 0`, the gap with label `{kα}`, `k = -m`, has
low-energy Hall integer `m`. -/
theorem every_hall_integer {μ h B : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0)
    (hirr : Irrational (freq (fieldParam μ h B))) (m : ℤ) (hm : m ≠ 0) :
    ∃ k : ℤ, k ≠ 0 ∧ Int.fract (k * freq (fieldParam μ h B)) ∈ Ioo 0 1 ∧
      ∀ {T : ℝ → ℝ} {r k' : ℤ},
        (∀ᶠ B' in 𝓝 B, T B' = lowDensity μ (r + k' * freq (fieldParam μ h B'))) →
        (r : ℝ) + k' * freq (fieldParam μ h B) = Int.fract (k * freq (fieldParam μ h B)) →
        stredaChern h T B = m := by
  refine ⟨-m, neg_ne_zero.2 hm, fract_mem_Ioo hirr (neg_ne_zero.2 hm), fun hT hlab => ?_⟩
  rw [((physical_hall_low hμ hh hT).2 (-m) hirr hlab)]
  push_cast; ring

/-! ### Lemma `lem:magnetic-gap-persistence` -/

/-- The two-sided Hölder-`½` spectral continuity of Lemma `lem:magnetic-gap-persistence`, for a
field-indexed family of spectra `Spec B = spec(H_B)` on fields in `I` and energies in `J`:
`sup_{E ∈ spec(H_B) ∩ J} dist(E, spec(H_{B'})) ≤ C |B - B'|^{1/2}`. -/
def GapPersistenceBound (Spec : ℝ → Set ℝ) (I J : Set ℝ) (C : ℝ) : Prop :=
  ∀ B ∈ I, ∀ B' ∈ I, |B - B'| ≤ 1 → ∀ E ∈ Spec B ∩ J,
    infDist E (Spec B') ≤ C * |B - B'| ^ (1 / 2 : ℝ)

/-- **Lemma `lem:magnetic-gap-persistence`, "in particular".**  Under the spectral continuity
bound, a compact interval contained in a gap of `spec(H_B)` remains in the resolvent set for all
sufficiently close fields. -/
theorem gap_persists {Spec : ℝ → Set ℝ} {I J : Set ℝ} {C : ℝ}
    (hbound : GapPersistenceBound Spec I J C) {B : ℝ} (hBI : I ∈ 𝓝 B)
    (hclosed : IsClosed (Spec B)) (hne : (Spec B).Nonempty) {a b : ℝ} (hJ : Icc a b ⊆ J)
    (hgap : Icc a b ∩ Spec B = ∅) :
    ∀ᶠ B' in 𝓝 B, Icc a b ∩ Spec B' = ∅ := by
  rcases lt_or_ge b a with hba | hab
  · exact Eventually.of_forall fun _ => by rw [Icc_eq_empty (not_le.2 hba), empty_inter]
  -- the distance from `[a,b]` to `spec(H_B)` is positive
  obtain ⟨E₀, hE₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab)
    (continuous_infDist_pt (Spec B)).continuousOn
  have hd : 0 < infDist E₀ (Spec B) := by
    refine (hclosed.notMem_iff_infDist_pos hne).1 fun hmem => ?_
    have : E₀ ∈ Icc a b ∩ Spec B := ⟨hE₀, hmem⟩
    rw [hgap] at this; exact this
  set d := infDist E₀ (Spec B)
  -- fields with `C |B - B'|^{1/2} < d`
  have hC0 : ∀ᶠ B' in 𝓝 B, C * |B - B'| ^ (1 / 2 : ℝ) < d := by
    have hcont : Continuous fun B' : ℝ => C * |B - B'| ^ (1 / 2 : ℝ) :=
      continuous_const.mul ((continuous_const.sub continuous_id).abs.rpow_const
        (fun _ => Or.inr (by norm_num)))
    have h0 : C * |B - B| ^ (1 / 2 : ℝ) = 0 := by simp
    exact hcont.continuousAt.eventually_lt continuousAt_const (by rw [h0]; exact hd)
  have hnear : ∀ᶠ B' in 𝓝 B, |B - B'| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds B one_pos] with B' hB'
    rw [abs_sub_comm]; exact (Real.dist_eq B' B ▸ (mem_ball.1 hB')).le
  filter_upwards [hBI, hC0, hnear] with B' hB'I hlt hle
  ext E
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hE hspec
  have h1 := hbound B' hB'I B (mem_of_mem_nhds hBI) (by rwa [abs_sub_comm]) E ⟨hspec, hJ hE⟩
  rw [abs_sub_comm] at h1
  have h2 : d ≤ infDist E (Spec B) := hmin hE
  linarith

end CMS
