/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.9: uniform results for topological ergodic families  (book pp. 380–384)

Here `E : ErgodicFamily Ω` (from `DamanikFillman/Ch4/Setting.lean`) lives on a compact metric
space, with `T`, `T⁻¹` and `f` continuous; `E.homeo` is `T` as a homeomorphism, so that the
results of `DamanikFillman/Ch4/Johnson.lean` and `.../UniformSpectrum.lean` apply to
`E.H ω = DF.Johnson.ham E.homeo E.f ω` (`E.H_eq_ham`).

## Main definitions
* `E.UH` — the set `𝒰ℋ` (4.9.2); `E.Zset = 𝒵_μ` (4.9.7); `E.NUH = 𝒩𝒰ℋ_μ` (4.9.8).

## Main results
* `E.lyap_pos_of_UH` — `E ∈ 𝒰ℋ ⇒ L_μ(E) > 0`; `E.partition` — the partition (4.9.9)
  `ℝ = 𝒵_μ ⊔ 𝒩𝒰ℋ_μ ⊔ 𝒰ℋ`;
* `E.asSpectrum_eq_compl_UH` — Corollaries 4.9.4/4.9.5: if `supp μ = Ω` then `Σ = ℝ \ 𝒰ℋ`;
  `E.asSpectrum_eq_Z_union_NUH` — **Corollary 4.9.5**: `Σ_μ = 𝒵_μ ⊔ 𝒩𝒰ℋ_μ`;
* `E.spectrum_eq_asSpectrum_of_minimal` — Theorem 4.9.1 (spectrum part) in the ergodic
  setting: for minimal `T`, `σ(H_ω) = Σ` for **every** `ω`;
* `E.limsup_le_lyap` — **Proposition 4.9.14**: for uniquely ergodic `(Ω, T)`, for every `z ∈ ℂ`
  and `ε > 0`, `(1/n) log ‖A^n_z(ω)‖ < L(z) + ε` for all large `n`, uniformly in `ω` (via
  Furman's theorem 3.5.8).

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch4.UniformSpectrum
import DamanikFillman.Ch4.Nonrandom
import DamanikFillman.Ch4.Lyapunov
import DamanikFillman.Ch3.TopErgodic
import DamanikFillman.Ch3.Furman

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace DF

namespace ErgodicFamily

open Cocycle Johnson

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (E : ErgodicFamily Ω) (hT : Continuous E.T) (hTs : Continuous E.T.symm) (hf : Continuous E.f)

/-- `T` as a homeomorphism. -/
def homeo : Ω ≃ₜ Ω := ⟨E.T.toEquiv, hT, hTs⟩

lemma homeo_apply (ω : Ω) : E.homeo hT hTs ω = E.T ω := rfl

lemma pot_eq (ω : Ω) : pot (E.homeo hT hTs) E.f ω = E.V ω := rfl

lemma H_eq_ham (ω : Ω) : E.H ω = ham (E.homeo hT hTs) E.f ω := rfl

/-- The set `𝒰ℋ` (4.9.2) of the ergodic family. -/
def UH : Set ℝ := UHset (E.homeo hT hTs) E.f

/-- `𝒵_μ = {E : L_μ(E) = 0}` (4.9.7). -/
def Zset : Set ℝ := {x | E.lyap (x : ℂ) = 0}

/-- `𝒩𝒰ℋ_μ = {E : L_μ(E) > 0, (T, A_E) not uniformly hyperbolic}` (4.9.8). -/
def NUH : Set ℝ := {x | 0 < E.lyap (x : ℂ) ∧ x ∉ E.UH hT hTs}

/-! ### `𝒰ℋ ⇒ L > 0` -/

lemma Az_eq_cplx (x : ℝ) (ω : Ω) :
    E.Az (x : ℂ) ω = cplx ((schrCoc (E.homeo hT hTs) E.f x ω : SL2R) : M2R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Az, transfer, schrCoc, schrMat_coe, cplx_apply,
    homeo_apply]

lemma An_eq_cplx (x : ℝ) (n : ℕ) (ω : Ω) :
    E.An (x : ℂ) n ω =
      cplx ((iter (E.homeo hT hTs).toEquiv (schrCoc (E.homeo hT hTs) E.f x) n ω : SL2R) : M2R) := by
  induction n with
  | zero => simp [An, cplx]
  | succ n ih =>
    rw [An, iter_succ, ← An, ih, iter_succ, Matrix.SpecialLinearGroup.coe_mul, cplx_mul,
      Az_eq_cplx]
    rfl

/-- Uniform hyperbolicity forces a positive Lyapunov exponent. -/
theorem lyap_pos_of_UH {x : ℝ} (hx : x ∈ E.UH hT hTs) : 0 < E.lyap (x : ℂ) := by
  obtain ⟨C, hC, l, hl, hg⟩ := hx
  obtain ⟨ω, hω⟩ := (E.lyap_spec (x : ℂ)).2.2.exists
  have hlog : 0 < Real.log l := Real.log_pos hl
  have hlow : Tendsto (fun n : ℕ => Real.log C / n + Real.log l) atTop (𝓝 (0 + Real.log l)) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).add_const _
  rw [zero_add] at hlow
  have hle : Real.log l ≤ E.lyap (x : ℂ) := by
    refine le_of_tendsto_of_tendsto hlow hω ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := hg n ω
    simp only [Int.natAbs_natCast, iterZ_natCast] at h1
    have h2 := norm_le_norm_cplx
      ((iter (E.homeo hT hTs).toEquiv (schrCoc (E.homeo hT hTs) E.f x) n ω : SL2R) : M2R)
    rw [← An_eq_cplx] at h2
    have hpos : 0 < C * l ^ n := by positivity
    have h3 : Real.log (C * l ^ n) ≤ Real.log ‖E.An (x : ℂ) n ω‖ :=
      Real.log_le_log hpos (h1.trans h2)
    rw [Real.log_mul hC.ne' (by positivity), Real.log_pow] at h3
    rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
    linarith
  linarith

/-- The partition (4.9.9): `ℝ = 𝒵_μ ⊔ 𝒩𝒰ℋ_μ ⊔ 𝒰ℋ`. -/
theorem partition :
    E.Zset ∪ E.NUH hT hTs ∪ E.UH hT hTs = univ ∧ Disjoint (E.Zset) (E.NUH hT hTs) ∧
      Disjoint (E.Zset ∪ E.NUH hT hTs) (E.UH hT hTs) := by
  refine ⟨eq_univ_of_forall fun x => ?_, ?_, ?_⟩
  · by_cases hU : x ∈ E.UH hT hTs
    · exact Or.inr hU
    · rcases (E.lyap_nonneg (x : ℂ)).lt_or_eq with h | h
      · exact Or.inl (Or.inr ⟨h, hU⟩)
      · exact Or.inl (Or.inl h.symm)
  · refine Set.disjoint_left.2 fun x h1 h2 => ?_
    have : E.lyap (x : ℂ) = 0 := h1
    linarith [h2.1]
  · refine Set.disjoint_left.2 fun x h1 h2 => ?_
    have := E.lyap_pos_of_UH hT hTs h2
    rcases h1 with h1 | h1
    · have : E.lyap (x : ℂ) = 0 := h1
      linarith
    · exact h1.2 h2

lemma Z_union_NUH : E.Zset ∪ E.NUH hT hTs = (E.UH hT hTs)ᶜ := by
  obtain ⟨h1, -, h3⟩ := E.partition hT hTs
  ext x
  constructor
  · intro hx hU; exact Set.disjoint_left.1 h3 hx hU
  · intro hx
    have : x ∈ E.Zset ∪ E.NUH hT hTs ∪ E.UH hT hTs := h1 ▸ mem_univ x
    rcases this with h | h
    · exact h
    · exact absurd h hx

/-! ### Corollary 4.9.5 -/

include hf in
/-- **Corollaries 4.9.4 / 4.9.5**: if `supp μ = Ω`, the almost sure spectrum is
`Σ = ℝ \ 𝒰ℋ`. -/
theorem asSpectrum_eq_compl_UH [E.μ.IsOpenPosMeasure] :
    E.asSpectrum = (E.UH hT hTs)ᶜ := by
  obtain ⟨ω, h1, h2⟩ := ((ae_dense_orbit (μ := E.μ) (T := ⇑E.T) E.ergodic).and
    E.ae_spectrum_eq).exists
  have hd : Dense (orbit (E.homeo hT hTs) ω) := h1.mono subset_union_left
  rw [← h2, H_eq_ham E hT hTs]
  exact spectrum_eq_compl_UH_of_dense hf hd

include hf in
/-- **Corollary 4.9.5**: if `supp μ = Ω`, then `Σ_μ = 𝒵_μ ⊔ 𝒩𝒰ℋ_μ`. -/
theorem asSpectrum_eq_Z_union_NUH [E.μ.IsOpenPosMeasure] :
    E.asSpectrum = E.Zset ∪ E.NUH hT hTs := by
  rw [E.asSpectrum_eq_compl_UH hT hTs hf, Z_union_NUH]

include hf in
/-- **Theorem 4.9.1** (spectrum part): if `(Ω, T)` is minimal, then `σ(H_ω) = Σ` for every
`ω ∈ Ω`. -/
theorem spectrum_eq_asSpectrum_of_minimal (hmin : IsMinimalSys (E.homeo hT hTs)) (ω : Ω) :
    spectrum ℝ (E.H ω) = E.asSpectrum := by
  obtain ⟨ω', hω'⟩ := E.exists_spectrum_eq
  rw [← hω', H_eq_ham E hT hTs, H_eq_ham E hT hTs]
  exact spectrum_const_of_minimal hf hmin ω ω'

/-! ### Proposition 4.9.14 -/

include hT hf in
lemma continuous_Az (z : ℂ) : Continuous (E.Az z) := by
  have hc : Continuous fun ω => ((E.f (E.T ω) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hf.comp hT)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [Az, transfer] <;>
    first | exact continuous_const | exact continuous_const.sub hc

include hT hf in
lemma continuous_An (z : ℂ) (n : ℕ) : Continuous (E.An z n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have : E.An z (n + 1) = fun ω => E.Az z ((⇑E.T)^[n] ω) * E.An z n ω := funext fun ω => rfl
    rw [this]
    exact ((E.continuous_Az hT hf z).comp (hT.iterate n)).mul ih

include hT hf in
/-- **Proposition 4.9.14**: if `(Ω, T)` is uniquely ergodic, then for every `z ∈ ℂ`,
`limsup (1/n) log ‖A^n_z(ω)‖ ≤ L(z)` uniformly in `ω ∈ Ω`. -/
theorem limsup_le_lyap (hue : invMeasures (⇑E.T) = {E.μ}) (z : ℂ) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ ω, Real.log ‖E.An z n ω‖ / n < E.lyap z + ε := by
  set g : ℕ → C(Ω, ℝ) := fun n =>
    ⟨fun ω => Real.log ‖E.An z n ω‖,
      ((E.continuous_An hT hf z n).norm).log fun ω => by
        linarith [E.one_le_norm_An z n ω]⟩
  have hsub : ∀ n m x, 1 ≤ n → 1 ≤ m → g (n + m) x ≤ g n x + g m ((⇑E.T)^[n] x) := by
    intro n m x _ _
    show Real.log ‖E.An z (n + m) x‖ ≤ Real.log ‖E.An z n x‖ + Real.log ‖E.An z m _‖
    rw [E.An_add, ← Real.log_mul (by linarith [E.one_le_norm_An z n x])
      (by linarith [E.one_le_norm_An z m ((⇑E.T)^[n] x)]), mul_comm (‖E.An z n x‖)]
    have h1 := E.one_le_norm_An z (n + m) x
    rw [E.An_add] at h1
    exact Real.log_le_log (by linarith) (norm_mul_le _ _)
  have hC : ∀ n x, 1 ≤ n → |g n x| ≤ Real.log (‖z‖ + E.fBound + 1) * n := by
    intro n x _
    show |Real.log ‖E.An z n x‖| ≤ _
    rw [abs_of_nonneg (E.log_norm_An_nonneg z n x), mul_comm]
    exact E.log_norm_An_le z n x
  intro ε hε
  obtain ⟨N, hN⟩ := furman hT hue hsub hC ε hε
  refine ⟨N, fun n hn ω => ?_⟩
  have := hN n hn ω
  rw [lyap_eq_iInf]
  exact this

end ErgodicFamily

end DF
