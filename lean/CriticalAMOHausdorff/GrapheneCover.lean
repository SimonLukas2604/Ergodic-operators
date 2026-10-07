/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Graphene: blocks, flow, spectral cover and `dim_H Σ_Φ ≤ 1/2`
  (Appendix §9, Theorem 9.1 `gr`, Jacobi-matrix part; tex l. 1836–1925)

* `gr_phase_variation`: Lemma `lemma-flow` (`Flow.flow_bound`) applied to
  `G_N^± = G_N ± τP_N` with `K = K_N^g`: `∑_j Var_{J_n} λ_j^± ≤ C|J_n|` (tex l. 1905–1914);
* `gr_block_cover_of_two_le`: Proposition `prop-cover1` for graphene (via `Flow.cover_bdry`);
* `cJacobi v b α θ`: the Jacobi operator `(H2)` with **complex** `b` (coefficient of `φ(n-1)` is
  `conj b(θ+(n-1)α)`), realised as `AMO.jac`; `cBlock`: the complex blocks;
* `spectrum_cJacobi`: gauge `σ(H_{v,b}) = σ(H_{v,|b|})` (`AMO.gauge_identity`);
  `spectrum_block_gauge`: the real `|b|`-block with boundary perturbation `V` is unitarily
  equivalent to the complex `b`-block with a boundary perturbation `V'`, `‖V'‖ ≤ ‖V‖`;
* `prop_blocks_complex`: **Proposition `prop-blocks` for complex-valued `1`-periodic `b`**
  with `b(0) = 0`, `b` `L`-Lipschitz (the Remark, tex l. 1322–1334).  The proof reduces to the
  real Lemma `lemma-subm` (`lemma_subm_jacobi`) through the two gauges; block phases: since `b`
  is `1`-periodic the blocks are `1`-periodic in `x` (`cBlock_add_int`), so no sign gauge is
  needed;
* `grJacobi α θ = cJacobi vB cB α θ`, `SigmaPhi α = closure ⋃_θ σ(grJacobi α θ)` (`Σ_Φ`);
  `prop_blocks_graphene` (`|c(y)-c(z)| ≤ 2π|y-z|`, `c(0) = 0`, so `‖V‖ ≤ 4π|J_n|`);
* `gr_thm_cover`, `gr_thm_cover_SigmaPhi`: covers of every fibre spectrum and of `Σ_Φ` by
  `≤ q_n + q_{n-1}` intervals of total length `≤ C/q_n` (tex l. 1919–1923);
* **`dimH_spectrum_grJacobi_le_half`, `dimH_SigmaPhi_le_half`**: `dim_H ≤ 1/2` (and
  `𝓗^{1/2} < ∞`) for every irrational `α` — unconditional.

No `sorry`, no axioms.
-/
import CriticalAMOHausdorff.GrapheneLaxPair
import CriticalAMOHausdorff.MainTheorems
import AnalyticPerturbationsAMO.Gauge

noncomputable section

open Matrix Real Set MeasureTheory L2
open scoped ComplexConjugate Matrix.Norms.L2Operator ENNReal

namespace CAH
namespace Graphene

variable {α : ℝ}

/-! ## 1. Variation of the block eigenvalues (Lemma `lemma-flow` for `G_N^±`) -/

lemma continuous_cm (α : ℝ) (m : ℤ) : Continuous fun y => cm α y m := by
  unfold cm cB ex; fun_prop

lemma continuous_EG (α : ℝ) (N : ℕ) : Continuous fun y => EG α y N := by
  have h1 := fun m => continuous_cm α m
  have h2 := fun m => Complex.continuous_conj.comp (continuous_cm α m)
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [EG, of_apply]
  refine ((Continuous.add ?_ ?_).sub ?_).sub ?_ <;>
    refine Continuous.if_const _ ?_ continuous_const
  · exact (h1 0).mul continuous_const
  · exact (h2 N).mul continuous_const
  · exact (h2 0).mul continuous_const
  · exact (h1 N).mul continuous_const

lemma continuous_Epm (α : ℝ) (N : ℕ) (s : ℝ) : Continuous fun y => Epm α N s y :=
  (continuous_EG α N).sub continuous_const

/-- The flow equation `(G_N^±)' = [K_N^g, G_N^±] + E_N^±` with `G_N^± = G_N ± τ P_N`
(tex l. 1880–1884), in the form `H = G_N + s P_N`, `E = E_N - s[K_N^g, P_N]`. -/
lemma hasDerivAt_Gpm (hα : Irrational α) (N : ℕ) (s x : ℝ) :
    HasDerivAt (fun y => GN α y N + (s : ℂ) • Pd N)
      (KG α N * (GN α x N + (s : ℂ) • Pd N) - (GN α x N + (s : ℂ) • Pd N) * KG α N +
        Epm α N s x) x := by
  refine ((commutator_identity hα N x).add_const ((s : ℂ) • Pd N)).congr_deriv ?_
  simp only [Epm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

lemma Gpm_isHermitian (α x : ℝ) (N : ℕ) (s : ℝ) : (GN α x N + (s : ℂ) • Pd N).IsHermitian :=
  (GN_isHermitian α x N).add (Flow.isHermitian_real_smul (Pd_isHermitian N) s)

/-- **Variation of the block eigenvalues** (tex l. 1905–1914, via Lemma `lemma-flow`): for
`N ∈ {q_n, q_{n-1}}`, `N ≥ 2`, and `|s| ≤ C₀|J_n|`, the ordered eigenvalues of
`G_N(x) + s P_N` satisfy `∑_j Var_{J_n} λ_j ≤ C_g(C₀) |J_n|`. -/
theorem gr_phase_variation (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN2 : 2 ≤ N)
    (hN : N = qN α n ∨ N = qN α (n - 1)) {C₀ s : ℝ}
    (hs : |s| ≤ C₀ * (2 * |delta α (n - 1)|)) :
    ∑ j, eVariationOn (fun x => Flow.eig (GN α x N + (s : ℂ) • Flow.bdryProj N) j)
        (Set.Icc (-|delta α (n - 1)|) (|delta α (n - 1)|)) ≤
      ENNReal.ofReal (grPhaseConst C₀ * (2 * |delta α (n - 1)|)) := by
  set d := |delta α (n - 1)| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hab : -d ≤ d := by linarith
  rw [← Pd_eq_bdryProj hN2]
  have key := Flow.flow_bound hab (H := fun y => GN α y N + (s : ℂ) • Pd N)
    (E := fun y => Epm α N s y) (KG_skew α N)
    (fun x _ => Gpm_isHermitian α x N s)
    (fun x _ => (hasDerivAt_Gpm hα N s x).hasDerivWithinAt)
    (continuous_Epm α N s).continuousOn
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := -d) (b := d)
    (C := grPhaseConst C₀) (f := fun y => Flow.traceNorm (Epm α N s y))
    (fun y hy => by
      rw [Set.uIoc_of_le hab] at hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Flow.traceNorm_nonneg _)]
      exact traceNorm_Epm_le_const hα hn hN2 hN hs (abs_le.2 ⟨hy.1.le, hy.2⟩))
  rw [show d - -d = 2 * d by ring, abs_of_nonneg (by linarith)] at hint
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hint)

/-- The constant of the graphene block cover: `2(4C₀ + 2 C_g(C₀))`. -/
def grCoverConst (C₀ : ℝ) : ℝ := 2 * (4 * C₀ + 2 * grPhaseConst C₀)

lemma grCoverConst_nonneg {C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 0 ≤ grCoverConst C₀ := by
  have := grPhaseConst_nonneg C₀; unfold grCoverConst; positivity

/-- **Proposition `prop-cover1` for graphene** (tex l. 1919–1923, repeating the proof of
`prop-cover1`): for `N ∈ {q_n, q_{n-1}}`, `N ≥ 2`, there are `N` intervals, independent of
`x ∈ J_n` and of `V = V^*` with `‖V‖ ≤ C₀|J_n|`, covering `σ(G_N(x) + Γ̂_N^* V Γ̂_N)`, of total
length `≤ grCoverConst C₀ / q_n`. -/
theorem gr_block_cover_of_two_le (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {N : ℕ}
    (hN2 : 2 ≤ N) (hN : N = qN α n ∨ N = qN α (n - 1)) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ lo hi : Fin N → ℝ, (∀ j, lo j ≤ hi j) ∧
      ∑ j, (hi j - lo j) ≤ grCoverConst C₀ / q α n ∧
      ∀ x ∈ Set.Icc (-|delta α (n - 1)|) (|delta α (n - 1)|),
      ∀ V : Matrix (Fin 2) (Fin 2) ℂ, ∀ hV : V.IsHermitian,
        (∀ i, |hV.eigenvalues i| ≤ C₀ * (2 * |delta α (n - 1)|)) →
        spectrum ℝ (GN α x N + (Flow.bdry N)ᴴ * V * Flow.bdry N) ⊆
          ⋃ j, Set.Icc (lo j) (hi j) := by
  set d := |delta α (n - 1)| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hab : -d ≤ d := by linarith
  set c := C₀ * (2 * d) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hP := grPhaseConst_nonneg C₀
  have hplus := gr_phase_variation hα hn hN2 hN (C₀ := C₀) (s := c) (by rw [abs_of_nonneg hc0])
  have hminus := gr_phase_variation hα hn hN2 hN (C₀ := C₀) (s := -c)
    (by rw [abs_neg, abs_of_nonneg hc0])
  have e : ∀ x, GN α x N - (c : ℂ) • Flow.bdryProj N =
      GN α x N + ((-c : ℝ) : ℂ) • Flow.bdryProj N := fun x => by
    rw [Complex.ofReal_neg, neg_smul, sub_eq_add_neg]
  have hV : ∑ j, eVariationOn (fun x => Flow.eig (GN α x N + (c : ℂ) •
        Flow.bdryProj N) j) (Set.Icc (-d) d) +
      ∑ j, eVariationOn (fun x => Flow.eig (GN α x N - (c : ℂ) •
        Flow.bdryProj N) j) (Set.Icc (-d) d) ≤
      ENNReal.ofReal (2 * (grPhaseConst C₀ * (2 * d))) := by
    simp only [e]
    rw [two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hplus hminus
  obtain ⟨lo, hi, hle, hlen, hcov⟩ :=
    Flow.cover_bdry hab (by omega : 1 ≤ N) (fun x => GN α x N) hc0 (by positivity)
      (fun x _ => GN_isHermitian α x N) hV
  refine ⟨lo, hi, hle, ?_, fun x hx V hV₁ hV₂ => hcov x hx V hV₁ hV₂⟩
  have hlen' : ∑ j, (hi j - lo j) ≤ (4 * C₀ + 2 * grPhaseConst C₀) * (2 * d) := by
    have : 4 * c + 2 * (grPhaseConst C₀ * (2 * d)) = (4 * C₀ + 2 * grPhaseConst C₀) * (2 * d) := by
      rw [hcdef]; ring
    linarith
  have hQ := q_pos hα n
  have hdQ := BlockCover.abs_delta_mul_q_lt hα hn
  have hK : 0 ≤ 4 * C₀ + 2 * grPhaseConst C₀ := by positivity
  rw [le_div_iff₀ hQ]
  calc (∑ j, (hi j - lo j)) * q α n ≤ (4 * C₀ + 2 * grPhaseConst C₀) * (2 * d) * q α n :=
        mul_le_mul_of_nonneg_right hlen' hQ.le
    _ = 2 * (4 * C₀ + 2 * grPhaseConst C₀) * (d * q α n) := by ring
    _ ≤ 2 * (4 * C₀ + 2 * grPhaseConst C₀) * 1 := by gcongr
    _ = grCoverConst C₀ := by rw [grCoverConst, mul_one]

/-! ## 2. Complex Jacobi operators and the phase gauge -/

/-- The phase `z/|z|` of a complex number (`1` for `z = 0`). -/
def ph (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

lemma norm_ph (z : ℂ) : ‖ph z‖ = 1 := by
  unfold ph; split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h)]

lemma norm_mul_ph (z : ℂ) : (‖z‖ : ℂ) * ph z = z := by
  unfold ph; split_ifs with h
  · simp [h]
  · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
    field_simp

lemma conj_mul_self_of_norm_one {z : ℂ} (h : ‖z‖ = 1) : conj z * z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp

/-- **The complex Jacobi operator** (`(H2)` with complex-valued `b`, Remark after
Prop. `prop-blocks`, tex l. 1322–1334):
`(H φ)(n) = b(θ+nα) φ(n+1) + conj b(θ+(n-1)α) φ(n-1) + v(θ+nα) φ(n)`. -/
def cJacobi (v : ℝ → ℝ) (b : ℝ → ℂ) (α θ : ℝ) : Op :=
  AMO.jac (fun n : ℤ => b (θ + n * α)) (fun n : ℤ => ((v (θ + n * α) : ℝ) : ℂ))

/-- The complex block `B̂_N(x)` with subdiagonal the conjugate of the superdiagonal
(Remark after Prop. `prop-blocks`). -/
def cBlock (v : ℝ → ℝ) (b : ℝ → ℂ) (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    if i = j then ((v (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ)
    else if (j : ℕ) = i + 1 then b (x + ((i : ℕ) + 1) * α)
    else if (i : ℕ) = j + 1 then conj (b (x + ((j : ℕ) + 1) * α))
    else 0

/-- A bounded complex function. -/
def CBdd (b : ℝ → ℂ) : Prop := ∃ M, ∀ x, ‖b x‖ ≤ M

lemma bddFun_norm {b : ℝ → ℂ} (hb : CBdd b) : BddFun fun y => ‖b y‖ := by
  obtain ⟨M, hM⟩ := hb; exact ⟨M, fun x => by rw [abs_norm]; exact hM x⟩

lemma diagOp_unit {γ : ℤ → ℂ} (hγ : ∀ n, ‖γ n‖ = 1) :
    AMO.diagOp γ * star (AMO.diagOp γ) = 1 ∧ star (AMO.diagOp γ) * AMO.diagOp γ = 1 := by
  have hb : Bdd γ := bdd_of_norm_eq_one hγ
  rw [AMO.star_diagOp hb]
  have hb' : Bdd (fun n => conj (γ n)) := hb.conj
  constructor
  · ext u n
    simp only [ContinuousLinearMap.mul_apply, AMO.diagOp_apply hb, AMO.diagOp_apply hb',
      ContinuousLinearMap.one_apply]
    rw [← mul_assoc, mul_comm (γ n), conj_mul_self_of_norm_one (hγ n), one_mul]
  · ext u n
    simp only [ContinuousLinearMap.mul_apply, AMO.diagOp_apply hb, AMO.diagOp_apply hb',
      ContinuousLinearMap.one_apply]
    rw [← mul_assoc, conj_mul_self_of_norm_one (hγ n), one_mul]

/-- **Gauge to real hoppings**: `σ(H_{v,b,α,θ}) = σ(H_{v,|b|,α,θ})` for complex `b`. -/
theorem spectrum_cJacobi {v : ℝ → ℝ} {b : ℝ → ℂ} (hv : BddFun v) (hb : CBdd b) (α θ : ℝ) :
    spectrum ℝ (cJacobi v b α θ) = spectrum ℝ (jacobi v (fun y => ‖b y‖) α θ) := by
  set q : ℤ → ℂ := fun n => ph (b (θ + n * α))
  have hq : ∀ n, ‖q n‖ = 1 := fun n => norm_ph _
  obtain ⟨hγ, hrec⟩ := AMO.gaugeSeq_spec hq
  set c : ℤ → ℂ := fun n => ((‖b (θ + n * α)‖ : ℝ) : ℂ)
  set w : ℤ → ℂ := fun n => ((v (θ + n * α) : ℝ) : ℂ)
  have hc : Bdd c := by
    obtain ⟨M, hM⟩ := hb; exact ⟨M, fun n => by simpa [c] using hM _⟩
  have hw : Bdd w := by
    obtain ⟨M, hM⟩ := hv; exact ⟨M, fun n => by simpa [w, Complex.norm_real] using hM _⟩
  have hgauge := AMO.gauge_identity hc hw hq hγ hrec
  have e1 : AMO.jac (fun n => c n * q n) w = cJacobi v b α θ := by
    unfold cJacobi; congr 1; funext n; exact norm_mul_ph _
  have e2 : AMO.jac c w = jacobi v (fun y => ‖b y‖) α θ := by
    ext u n
    rw [AMO.jac_apply hc hw, jacobi_apply hv (bddFun_norm hb)]
    simp only [c, w, Complex.conj_ofReal]
    push_cast; ring
  rw [e1] at hgauge
  rw [← e2, ← hgauge]
  obtain ⟨h1, h2⟩ := diagOp_unit hγ
  let u : (Op)ˣ := ⟨AMO.diagOp (AMO.gaugeSeq q), star (AMO.diagOp (AMO.gaugeSeq q)), h1, h2⟩
  exact (spectrum.units_conjugate' (u := u)).symm

/-! ## 3. The block gauge -/

/-- The block gauge phases `w_j = ∏_{i<j} ph(b(x+(i+1)α))`. -/
def wph (b : ℝ → ℂ) (α x : ℝ) (j : ℕ) : ℂ :=
  ∏ i ∈ Finset.range j, ph (b (x + ((i : ℝ) + 1) * α))

lemma norm_wph (b : ℝ → ℂ) (α x : ℝ) (j : ℕ) : ‖wph b α x j‖ = 1 := by
  unfold wph; rw [norm_prod]; exact Finset.prod_eq_one fun i _ => norm_ph _

lemma wph_succ (b : ℝ → ℂ) (α x : ℝ) (j : ℕ) :
    wph b α x (j + 1) = wph b α x j * ph (b (x + ((j : ℝ) + 1) * α)) := by
  unfold wph; rw [Finset.prod_range_succ]

/-- `W = diag(w_j)`. -/
def Wd (b : ℝ → ℂ) (α x : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun j => wph b α x (j : ℕ)

/-- `S = diag(w_0, w_{N-1})`. -/
def Sd (b : ℝ → ℂ) (α x : ℝ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun i => if (i : ℕ) = 0 then wph b α x 0 else wph b α x (N - 1)

lemma Wd_unitary (b : ℝ → ℂ) (α x : ℝ) (N : ℕ) :
    (Wd b α x N)ᴴ * Wd b α x N = 1 ∧ Wd b α x N * (Wd b α x N)ᴴ = 1 := by
  rw [Wd, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  constructor <;> congr 1 <;> funext j <;> simp only [Pi.star_apply, RCLike.star_def]
  · exact conj_mul_self_of_norm_one (norm_wph _ _ _ _)
  · rw [mul_comm]; exact conj_mul_self_of_norm_one (norm_wph _ _ _ _)

lemma bdry_mul_Wd (b : ℝ → ℂ) (α x : ℝ) (N : ℕ) :
    bdry N * Wd b α x N = Sd b α x N * bdry N := by
  ext i j
  rw [Wd, Sd, mul_diagonal, diagonal_mul]
  simp only [bdry, of_apply]
  fin_cases i
  · by_cases hj : (j : ℕ) = 0
    · simp [hj]
    · simp [hj]
  · by_cases hj : (j : ℕ) + 1 = N
    · have : (j : ℕ) = N - 1 := by omega
      simp [hj, this]
    · simp [hj]

lemma norm_Sd_le (b : ℝ → ℂ) (α x : ℝ) (N : ℕ) : ‖Sd b α x N‖ ≤ 1 := by
  rw [Sd, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  split_ifs <;> simp [norm_wph]

/-- `W^* B̂_N(x) W` is the complex block, `B̂_N` built from `|b|`. -/
lemma Wd_conj_blockMatrix (v : ℝ → ℝ) (b : ℝ → ℂ) (α x : ℝ) (N : ℕ) :
    (Wd b α x N)ᴴ * blockMatrix v (fun y => ‖b y‖) α N x * Wd b α x N = cBlock v b α N x := by
  ext i j
  rw [Wd, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  simp only [blockMatrix, cBlock, of_apply, Pi.star_apply, RCLike.star_def]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
    have := conj_mul_self_of_norm_one (norm_wph b α x i)
    linear_combination ((v (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ) * this
  · simp only [if_neg hij]
    by_cases h1 : (j : ℕ) = i + 1
    · simp only [if_pos h1]
      rw [h1, wph_succ]
      have := conj_mul_self_of_norm_one (norm_wph b α x i)
      have e := norm_mul_ph (b (x + (((i : ℕ) : ℝ) + 1) * α))
      linear_combination (↑‖b (x + (((i : ℕ) : ℝ) + 1) * α)‖ *
        ph (b (x + (((i : ℕ) : ℝ) + 1) * α))) * this + e
    · simp only [if_neg h1]
      by_cases h3 : (i : ℕ) = j + 1
      · simp only [if_pos h3]
        rw [h3, wph_succ, map_mul]
        have := conj_mul_self_of_norm_one (norm_wph b α x j)
        have e := congrArg conj (norm_mul_ph (b (x + (((j : ℕ) : ℝ) + 1) * α)))
        rw [map_mul, Complex.conj_ofReal] at e
        linear_combination (↑‖b (x + (((j : ℕ) : ℝ) + 1) * α)‖ *
          conj (ph (b (x + (((j : ℕ) : ℝ) + 1) * α)))) * this + e
      · simp [if_neg h3]

/-- Conjugation by a unitary matrix preserves the spectrum. -/
lemma spectrum_unitary_conj {n : Type*} [Fintype n] [DecidableEq n] (W M : Matrix n n ℂ)
    (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) : spectrum ℝ (Wᴴ * M * W) = spectrum ℝ M := by
  let u : (Matrix n n ℂ)ˣ := ⟨W, Wᴴ, h2, h1⟩
  exact spectrum.units_conjugate' (u := u)

/-- **The block gauge** (Remark after Prop. `prop-blocks`): the real block of `|b|` with a
Hermitian boundary perturbation `V` is unitarily equivalent to the complex block of `b` with a
Hermitian boundary perturbation `V'`, `‖V'‖ ≤ ‖V‖`. -/
theorem spectrum_block_gauge (v : ℝ → ℝ) (b : ℝ → ℂ) (α x : ℝ) (N : ℕ)
    (V : Matrix (Fin 2) (Fin 2) ℂ) (hV : V.IsHermitian) :
    ∃ V' : Matrix (Fin 2) (Fin 2) ℂ, V'.IsHermitian ∧ ‖V'‖ ≤ ‖V‖ ∧
      spectrum ℝ (blockMatrix v (fun y => ‖b y‖) α N x + (bdry N)ᴴ * V * bdry N) =
        spectrum ℝ (cBlock v b α N x + (bdry N)ᴴ * V' * bdry N) := by
  set W := Wd b α x N
  set S := Sd b α x N
  obtain ⟨h1, h2⟩ := Wd_unitary b α x N
  refine ⟨Sᴴ * V * S, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hV.eq, Matrix.mul_assoc]
  · have hS := norm_Sd_le b α x N
    have hS' : ‖Sᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact hS
    calc ‖Sᴴ * V * S‖ ≤ ‖Sᴴ * V‖ * ‖S‖ := l2_opNorm_mul _ _
      _ ≤ (‖Sᴴ‖ * ‖V‖) * ‖S‖ := by gcongr; exact l2_opNorm_mul _ _
      _ ≤ (1 * ‖V‖) * 1 := by gcongr
      _ = ‖V‖ := by ring
  · rw [← spectrum_unitary_conj W _ h1 h2]
    congr 1
    rw [Matrix.mul_add, Matrix.add_mul, Wd_conj_blockMatrix]
    congr 1
    have hB := bdry_mul_Wd b α x N
    have hB' : Wᴴ * (bdry N)ᴴ = (bdry N)ᴴ * Sᴴ := by
      rw [← conjTranspose_mul, hB, conjTranspose_mul]
    calc Wᴴ * ((bdry N)ᴴ * V * bdry N) * W = (Wᴴ * (bdry N)ᴴ) * V * (bdry N * W) := by
          simp only [Matrix.mul_assoc]
      _ = (bdry N)ᴴ * (Sᴴ * V * S) * bdry N := by
          rw [hB', hB]; simp only [Matrix.mul_assoc]; rfl

/-! ## 4. Proposition `prop-blocks` for complex-valued `b` (the Remark, tex l. 1322–1334) -/

lemma cBlock_add_int {v : ℝ → ℝ} {b : ℝ → ℂ} (hv : Function.Periodic v 1)
    (hb : Function.Periodic b 1) (α : ℝ) (N : ℕ) (x : ℝ) (m : ℤ) :
    cBlock v b α N (x + m) = cBlock v b α N x := by
  have hv' : ∀ y, v (y + m) = v y := fun y => by simpa using (hv.int_mul m) y
  have hb' : ∀ y, b (y + m) = b y := fun y => by simpa using (hb.int_mul m) y
  ext i j
  simp only [cBlock, of_apply]
  rw [show x + m + ((i : ℕ) + 1) * α = x + ((i : ℕ) + 1) * α + m by ring,
    show x + m + ((j : ℕ) + 1) * α = x + ((j : ℕ) + 1) * α + m by ring, hv', hb', hb']

/-- **Proposition `prop-blocks` for complex-valued `b`** (Remark, tex l. 1322–1334).  Let `v`
be real, `b` complex, both bounded and `1`-periodic, `b(0) = 0`, `b` Lipschitz with constant `L`,
`α` irrational, `n ≥ 4`.  Then for every `θ`
`σ(H_{v,b,α,θ}) ⊆ closure ⋃_{N ∈ {q_n, q_{n-1}}} ⋃_{x ∈ J_n} ⋃_{V = V^*, ‖V‖ ≤ 2L|J_n|}
  σ(B̂_N(x) + Γ̂_N^* V Γ̂_N)`, with the complex blocks `B̂_N` (`cBlock`).  As in the Remark the
removed bonds are `[[0, b(x_k)], [conj b(x_k), 0]]` of norm `|b(x_k)|`; the proof reduces to the
real case by the gauges `spectrum_cJacobi`, `spectrum_block_gauge` (no sign gauge is needed since
`b` is `1`-periodic). -/
theorem prop_blocks_complex {v : ℝ → ℝ} {b : ℝ → ℂ} (hv : BddFun v) (hb : CBdd b)
    (hvp : Function.Periodic v 1) (hbp : Function.Periodic b 1) (hb0 : b 0 = 0) {L : ℝ}
    (hL : ∀ y z, ‖b y - b z‖ ≤ L * |y - z|) (hα : Irrational α) {n : ℕ} (hn : 4 ≤ n)
    (θ : ℝ) :
    spectrum ℝ (cJacobi v b α θ) ⊆
      closure (⋃ N ∈ {N : ℕ | (N : ℝ) = q α n ∨ (N : ℝ) = q α (n - 1)},
        ⋃ x ∈ Jn α n,
        ⋃ V ∈ {V : Matrix (Fin 2) (Fin 2) ℂ | V.IsHermitian ∧ ‖V‖ ≤ 2 * (L * JnLen α n)},
          spectrum ℝ (cBlock v b α N x + (bdry N)ᴴ * V * bdry N)) := by
  obtain ⟨c, hc, hgap, hx⟩ := exists_cuts hα hn θ
  have hL0 : 0 ≤ L := by
    have := hL 1 0
    have h1 : (0 : ℝ) ≤ L * |1 - 0| := (norm_nonneg _).trans this
    simpa using h1
  have hτ : 0 ≤ L * JnLen α n := mul_nonneg hL0 (by unfold JnLen; positivity)
  have hbond : ∀ k, |‖b (bondPhase α θ c k)‖| ≤ L * JnLen α n := by
    intro k
    obtain ⟨m, hm⟩ := hx k
    rw [abs_norm]
    have hper : b (bondPhase α θ c k) = b (θ + (c k - 1) * α - m) := by
      have := (hbp.int_mul m) (θ + (c k - 1) * α - m)
      rw [mul_one, sub_add_cancel] at this
      rw [bondPhase, this]
    rw [hper]
    have h := hL (θ + (c k - 1) * α - m) 0
    rw [hb0, sub_zero, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hL0)
    have hz : |θ + (c k - 1) * α - m| ≤ |q α (n - 1) * α - p α (n - 1)| := abs_le.2 ⟨hm.1, hm.2⟩
    unfold JnLen; linarith [abs_nonneg (q α (n - 1) * α - p α (n - 1))]
  rw [spectrum_cJacobi hv hb]
  refine (lemma_subm_jacobi hc hv (bddFun_norm hb) hτ hbond).trans (closure_mono ?_)
  refine Set.iUnion_subset fun k => ?_
  refine Set.subset_iUnion₂_of_subset (cutLen c k) ?_ ?_
  · have := cutLen_eq c hc k
    have h := hgap k
    rw [← this] at h
    simpa using h
  obtain ⟨m, hm⟩ := hx k
  refine Set.subset_iUnion₂_of_subset (bondPhase α θ c k - m) hm ?_
  refine Set.iUnion₂_subset fun V hV => ?_
  obtain ⟨V', hV', hVn, hs⟩ := spectrum_block_gauge v b α (bondPhase α θ c k) (cutLen c k) V hV.1
  rw [blocks, hs]
  refine Set.subset_iUnion₂_of_subset V' ⟨hV', hVn.trans hV.2⟩ ?_
  have e := cBlock_add_int hvp hbp α (cutLen c k) (bondPhase α θ c k - m) m
  rw [sub_add_cancel] at e
  exact (congrArg (fun M => spectrum ℝ (M + (bdry (cutLen c k))ᴴ * V' * bdry (cutLen c k))) e).le

/-! ## 5. The graphene Jacobi operator -/

/-- **The auxiliary Jacobi operator of the graphene model** ([bhj, (5.4)] translated by `1/2`,
tex l. 1843–1846): `c(x) = 1 - e^{-2πix}`, `v(x) = -2cos(2πx)`,
`(H φ)(n) = c(θ+nα) φ(n+1) + conj c(θ+(n-1)α) φ(n-1) + v(θ+nα) φ(n)`. -/
def grJacobi (α θ : ℝ) : Op := cJacobi vB cB α θ

/-- `Σ_Φ`: the closure of the union of the fibre spectra of the graphene Jacobi operator (for
irrational `α` all fibre spectra coincide, and this is the phase-independent spectrum). -/
def SigmaPhi (α : ℝ) : Set ℝ := closure (⋃ θ : ℝ, spectrum ℝ (grJacobi α θ))

lemma GN_eq_cBlock (α x : ℝ) (N : ℕ) : GN α x N = cBlock vB cB α N x := by
  ext i j
  simp [GN, cBlock, vm, cm]

lemma bddFun_vB : BddFun vB :=
  ⟨2, fun x => by
    unfold vB
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]; nlinarith [abs_cos_le_one (2 * π * x)]⟩

lemma ex_add_int (t : ℝ) (m : ℤ) : ex (t + m) = ex t := by
  rw [ex_add]
  have : ex m = 1 := by
    unfold ex
    rw [show -(2 * (π : ℂ) * Complex.I) * ((m : ℝ) : ℂ) = ((-m : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [this, mul_one]

lemma cB_periodic : Function.Periodic cB 1 := fun y => by
  unfold cB; congr 1; exact_mod_cast ex_add_int y 1

lemma vB_periodic : Function.Periodic vB 1 := fun y => by
  unfold vB; congr 1
  rw [show 2 * π * (y + 1) = 2 * π * y + 2 * π by ring, Real.cos_add_two_pi]

lemma cBdd_cB : CBdd cB :=
  ⟨2, fun y => by
    unfold cB
    calc ‖1 - ex y‖ ≤ ‖(1 : ℂ)‖ + ‖ex y‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_ex]; norm_num⟩

/-- `|c(y) - c(z)| ≤ 2π |y - z|` (so `|c(x)| ≤ 2π‖x‖_𝕋`, tex l. 1906). -/
lemma cB_lipschitz (y z : ℝ) : ‖cB y - cB z‖ ≤ 2 * π * |y - z| := by
  have e : cB y - cB z = ex z * -(ex (y - z) - 1) := by
    unfold cB; rw [show ex y = ex z * ex (y - z) from ex_shift (by ring)]; ring
  rw [e, norm_mul, norm_ex, one_mul, norm_neg, norm_ex_sub_one]
  have := Real.abs_sin_le_abs (x := π * (y - z))
  rw [abs_mul, abs_of_pos Real.pi_pos] at this
  linarith

lemma cB_zero : cB 0 = 0 := by simp [cB, ex_zero]

/-- **Proposition `prop-blocks` for the graphene Jacobi operator** (tex l. 1918–1921). -/
theorem prop_blocks_graphene (hα : Irrational α) {n : ℕ} (hn : 4 ≤ n) (θ : ℝ) :
    spectrum ℝ (grJacobi α θ) ⊆
      closure (⋃ N ∈ {N : ℕ | (N : ℝ) = q α n ∨ (N : ℝ) = q α (n - 1)},
        ⋃ x ∈ Jn α n,
        ⋃ V ∈ {V : Matrix (Fin 2) (Fin 2) ℂ | V.IsHermitian ∧ ‖V‖ ≤ 4 * π * JnLen α n},
          spectrum ℝ (GN α x N + (bdry N)ᴴ * V * bdry N)) := by
  refine (prop_blocks_complex bddFun_vB cBdd_cB vB_periodic cB_periodic cB_zero cB_lipschitz hα
    hn θ).trans (closure_mono ?_)
  simp only [GN_eq_cBlock]
  refine Set.iUnion₂_mono fun N _ => Set.iUnion₂_mono fun x _ => ?_
  refine Set.iUnion₂_subset fun V hV => Set.subset_iUnion₂_of_subset V ⟨hV.1, ?_⟩ subset_rfl
  have := hV.2; linarith

/-! ## 6. The spectral cover of `Σ_Φ` and `dim_H Σ_Φ ≤ 1/2` -/

/-- **The cover of `Σ_Φ`** (tex l. 1916–1923, the graphene analogue of Theorem `thm-cover`):
for irrational `α` there is a constant `C` such that for every `n ≥ 4` there are
`m ≤ q_n + q_{n-1}` closed intervals, independent of `θ`, of total length `≤ C/q_n`, covering
`σ(H_θ)` for every `θ`. -/
theorem gr_thm_cover (hα : Irrational α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ 4, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / q α n ∧
      ∀ θ : ℝ, spectrum ℝ (grJacobi α θ) ⊆ ⋃ i, Icc (a i) (b i) := by
  have hC₀ : (0 : ℝ) ≤ 4 * π := by positivity
  refine ⟨2 * grCoverConst (4 * π), by have := grCoverConst_nonneg hC₀; positivity,
    fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have h2a : 2 ≤ qN α n := le_trans (two_le_qN hα hn) (by
    have := qN_le_succ hα (n - 1); rwa [Nat.sub_add_cancel hn1] at this)
  have h2b : 2 ≤ qN α (n - 1) := two_le_qN hα hn
  obtain ⟨lo₁, hi₁, hle₁, hlen₁, hcov₁⟩ :=
    gr_block_cover_of_two_le hα hn1 h2a (Or.inl rfl) hC₀
  obtain ⟨lo₂, hi₂, hle₂, hlen₂, hcov₂⟩ :=
    gr_block_cover_of_two_le hα hn1 h2b (Or.inr rfl) hC₀
  refine ⟨qN α n + qN α (n - 1), Fin.append lo₁ lo₂, Fin.append hi₁ hi₂, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hle₁ j
    · simpa using hle₂ j
  · push_cast; rw [qN_cast hα, qN_cast hα]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [two_mul, add_div]; exact add_le_add hlen₁ hlen₂
  · intro θ
    set T := ⋃ i, Icc (Fin.append lo₁ lo₂ i) (Fin.append hi₁ hi₂ i)
    have hT : IsClosed T := isClosed_iUnion_of_finite fun i => isClosed_Icc
    refine (prop_blocks_graphene hα hn θ).trans (closure_minimal ?_ hT)
    refine Set.iUnion₂_subset fun N hN => Set.iUnion₂_subset fun x hx =>
      Set.iUnion₂_subset fun V hV => ?_
    have hr : 0 ≤ 4 * π * JnLen α n := by
      have := Real.pi_pos; unfold JnLen; positivity
    have heig := (norm_le_iff_abs_eigenvalues_le hV.1 hr).1 hV.2
    rw [bdry_eq_flow_bdry]
    rcases hN with hN | hN
    · have hNe : N = qN α n := by
        have : (N : ℝ) = (qN α n : ℝ) := by rw [hN, qN_cast hα]
        exact_mod_cast this
      subst hNe
      refine (hcov₁ x hx V hV.1 heig).trans (Set.iUnion_subset fun j => ?_)
      exact Set.subset_iUnion_of_subset (Fin.castAdd (qN α (n - 1)) j) (by simp)
    · have hNe : N = qN α (n - 1) := by
        have : (N : ℝ) = (qN α (n - 1) : ℝ) := by rw [hN, qN_cast hα]
        exact_mod_cast this
      subst hNe
      refine (hcov₂ x hx V hV.1 heig).trans (Set.iUnion_subset fun j => ?_)
      exact Set.subset_iUnion_of_subset (Fin.natAdd (qN α n) j) (by simp)

/-- The same intervals cover `Σ_Φ`. -/
theorem gr_thm_cover_SigmaPhi (hα : Irrational α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ 4, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / q α n ∧
      SigmaPhi α ⊆ ⋃ i, Icc (a i) (b i) := by
  obtain ⟨C, hC, hcov⟩ := gr_thm_cover hα
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨m, a, b, hab, hm, hlen, hsub⟩ := hcov n hn
  exact ⟨m, a, b, hab, hm, hlen,
    (isClosed_iUnion_Icc a b).closure_subset_iff.2 (iUnion_subset hsub)⟩

/-- **Theorem 9.1, Jacobi-matrix part** (tex l. 1916–1925): for irrational `α = Φ/2π`, every
fibre spectrum of the graphene Jacobi operator has `dim_H ≤ 1/2` (and finite
`1/2`-dimensional Hausdorff measure). -/
theorem dimH_spectrum_grJacobi_le_half (hα : Irrational α) (θ : ℝ) :
    dimH (spectrum ℝ (grJacobi α θ)) ≤ 1 / 2 ∧ μH[1 / 2] (spectrum ℝ (grJacobi α θ)) < ⊤ := by
  obtain ⟨C, hC, hcov⟩ := gr_thm_cover hα
  refine dimH_le_half_of_thm_cover hα ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨m, a, b, h1, h2, h3, h4⟩ := hcov n hn
  exact ⟨m, a, b, h1, h2, h3, h4 θ⟩

/-- **Theorem 9.1, Jacobi-matrix part**: `dim_H Σ_Φ ≤ 1/2` for irrational `Φ/2π`. -/
theorem dimH_SigmaPhi_le_half (hα : Irrational α) :
    dimH (SigmaPhi α) ≤ 1 / 2 ∧ μH[1 / 2] (SigmaPhi α) < ⊤ :=
  dimH_le_half_of_thm_cover hα (gr_thm_cover_SigmaPhi hα)

end Graphene
end CAH
