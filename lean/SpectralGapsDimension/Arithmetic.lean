/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Arithmetic of the frequency  (paper §1, eq. (1.5), and Lemma 4.17 `dim:lem:arithmetic`)

For a sequence of denominators `q : ℕ → ℝ` we define
* the irrationality exponent `μ(q) = 1 + limsup log q_{n+1} / log q_n`,
* the exponential approximation exponent `β(q) = limsup log q_{n+1} / q_n`,
* the Brjuno sum `𝓑(q) = ∑ log q_{n+1} / q_n`,

all valued in `[0, ∞]`; for a real `α` they are evaluated at the continued-fraction
denominators `q_n = cfDen α n` (the same `cfDen`/`beta` as in Paper I).

The only properties of continued-fraction denominators that the arguments use are
`q_n ≥ 1` and `q_{n+2} ≥ 2 q_n` (`CFGrowth`), which we prove for every irrational `α`.

Main results:
* `brjuno_lt_top_of_mu_lt_top`, `beta_eq_zero_of_brjuno_lt_top`, `mu_eq_top_of_brjuno_eq_top`:
  the chain `μ < ∞ ⇒ 𝓑 < ∞ ⇒ β = 0` and `𝓑 = ∞ ⇒ μ = ∞` (§1.2 and first half of Lemma 4.17);
* `exists_convergent_liouville`: for Liouville `α` there are convergents `p/q` with
  `2π q² |α - p/q| ≤ q^{-M}` for every `M`, arbitrarily far out (second half of Lemma 4.17);
* `gapLabels_eq`: `(ℤ + αℤ) ∩ (0,1) = {{nα} : n ≠ 0}` (the label set `Λ_α`).

-/
import AnalyticPerturbationsAMO.Spectral

noncomputable section

open scoped ENNReal
open Filter Topology Set

namespace SGD

/-! ### Sequence-level arithmetic parameters -/

/-- `μ(q) = 1 + limsup_n log q_{n+1} / log q_n`. -/
def muSeq (q : ℕ → ℝ) : ℝ≥0∞ :=
  1 + limsup (fun n => ENNReal.ofReal (Real.log (q (n + 1)) / Real.log (q n))) atTop

/-- `β(q) = limsup_n log q_{n+1} / q_n`. -/
def betaSeq (q : ℕ → ℝ) : ℝ≥0∞ :=
  limsup (fun n => ENNReal.ofReal (Real.log (q (n + 1)) / q n)) atTop

/-- The Brjuno sum `𝓑(q) = ∑_n log q_{n+1} / q_n`. -/
def brjunoSeq (q : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (Real.log (q (n + 1)) / q n)

/-- The ordinary irrationality exponent `μ_irr(α)`. -/
def muIrr (α : ℝ) : ℝ≥0∞ := muSeq (AMO.cfDen α)

/-- The Brjuno sum `𝓑(α)`. -/
def brjuno (α : ℝ) : ℝ≥0∞ := brjunoSeq (AMO.cfDen α)

/-- Paper I's exponential approximation exponent is `betaSeq` of the denominators. -/
lemma beta_eq (α : ℝ) : AMO.beta α = betaSeq (AMO.cfDen α) := rfl

/-- `α` is Liouville (in the ordinary sense): `μ_irr(α) = ∞`. -/
def Liouville (α : ℝ) : Prop := muIrr α = ⊤

/-- `α` is Brjuno: `𝓑(α) < ∞`. -/
def Brjuno (α : ℝ) : Prop := brjuno α < ⊤

/-- `log t / t ≤ 2 t^{-1/2}` for `t ≥ 0`. -/
private lemma log_div_le (t : ℝ) (ht : 0 < t) : Real.log t / t ≤ 2 * (t ^ (1 / 2 : ℝ))⁻¹ := by
  have h := Real.log_le_rpow_div ht.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hs : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
  have ht' : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_add ht, add_halves, Real.rpow_one]
  rw [div_le_iff₀ ht]
  set s := t ^ (1 / 2 : ℝ)
  calc Real.log t ≤ s / (1 / 2) := h
    _ = 2 * s⁻¹ * (s * s) := by field_simp
    _ = 2 * s⁻¹ * t := by rw [ht']

/-- The growth properties of continued-fraction denominators used below. -/
structure CFGrowth (q : ℕ → ℝ) : Prop where
  one_le : ∀ n, 1 ≤ q n
  two_mul_le : ∀ n, 2 * q n ≤ q (n + 2)

namespace CFGrowth

variable {q : ℕ → ℝ} (hq : CFGrowth q)
include hq

lemma pos (n : ℕ) : 0 < q n := zero_lt_one.trans_le (hq.one_le n)

lemma log_nonneg (n : ℕ) : 0 ≤ Real.log (q n) := Real.log_nonneg (hq.one_le n)

/-- `q_n ≥ 2^{(n-1)/2}`. -/
lemma rpow_le (n : ℕ) : (2 : ℝ) ^ (((n : ℝ) - 1) / 2) ≤ q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      refine le_trans ?_ (hq.one_le 0)
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    | 1 => simpa using hq.one_le 1
    | k + 2 =>
      have h := ih k (by omega)
      have e : (((k + 2 : ℕ) : ℝ) - 1) / 2 = 1 + ((k : ℝ) - 1) / 2 := by push_cast; ring
      rw [e, Real.rpow_add (by norm_num), Real.rpow_one]
      nlinarith [hq.two_mul_le k]

lemma one_lt (n : ℕ) (hn : 2 ≤ n) : 1 < q n := by
  refine lt_of_lt_of_le ?_ (hq.rpow_le n)
  apply Real.one_lt_rpow (by norm_num)
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma log_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Real.log (q n) := Real.log_pos (hq.one_lt n hn)

lemma tendsto_atTop : Tendsto q atTop atTop := by
  refine tendsto_atTop_mono hq.rpow_le ?_
  refine (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp ?_
  refine Tendsto.atTop_div_const (by norm_num) ?_
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- `∑ log q_n / q_n < ∞` (paper, proof of Lemma 4.17). -/
lemma summable_log_div : Summable fun n => Real.log (q n) / q n := by
  set r : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ))
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hg : Summable fun n : ℕ => 2 * 2 ^ (1 / 4 : ℝ) * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine hg.of_nonneg_of_le (fun n => div_nonneg (hq.log_nonneg n) (hq.pos n).le) (fun n => ?_)
  refine (log_div_le _ (hq.pos n)).trans ?_
  rw [mul_assoc]
  gcongr
  have hlow : (2 : ℝ) ^ (((n : ℝ) - 1) / 4) ≤ q n ^ (1 / 2 : ℝ) := by
    calc (2 : ℝ) ^ (((n : ℝ) - 1) / 4) = ((2 : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]; ring_nf
      _ ≤ q n ^ (1 / 2 : ℝ) := by
          gcongr
          exact hq.rpow_le n
  have hpos : 0 < (2 : ℝ) ^ (((n : ℝ) - 1) / 4) := by positivity
  calc (q n ^ (1 / 2 : ℝ))⁻¹ ≤ ((2 : ℝ) ^ (((n : ℝ) - 1) / 4))⁻¹ := by gcongr
    _ = 2 ^ (1 / 4 : ℝ) * r ^ n := by
      rw [← Real.rpow_natCast r, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num),
        ← Real.rpow_add (by norm_num)]
      ring_nf

end CFGrowth

/-! ### The arithmetic chain `μ < ∞ ⇒ 𝓑 < ∞ ⇒ β = 0` -/

section chain

variable {q : ℕ → ℝ}

lemma term_nonneg (hq : CFGrowth q) (n : ℕ) : 0 ≤ Real.log (q (n + 1)) / q n :=
  div_nonneg (hq.log_nonneg _) (hq.pos n).le

/-- If eventually `q_{n+1} ≤ q_n^B`, the Brjuno sum is finite. -/
lemma brjuno_lt_top_of_eventually (hq : CFGrowth q) {B : ℝ}
    (h : ∀ᶠ n in atTop, Real.log (q (n + 1)) ≤ B * Real.log (q n)) : brjunoSeq q < ⊤ := by
  have hs : Summable fun n => Real.log (q (n + 1)) / q n := by
    refine Summable.of_norm_bounded_eventually_nat (hq.summable_log_div.mul_left B) ?_
    filter_upwards [h] with n hn
    rw [Real.norm_of_nonneg (term_nonneg hq n), mul_div_assoc']
    exact div_le_div_of_nonneg_right hn (hq.pos n).le
  unfold brjunoSeq
  rw [← ENNReal.ofReal_tsum_of_nonneg (term_nonneg hq) hs]
  exact ENNReal.ofReal_lt_top

/-- `μ < ∞ ⇒ 𝓑 < ∞`. -/
theorem brjuno_lt_top_of_mu_lt_top (hq : CFGrowth q) (h : muSeq q < ⊤) : brjunoSeq q < ⊤ := by
  unfold muSeq at h
  set L := limsup (fun n => ENNReal.ofReal (Real.log (q (n + 1)) / Real.log (q n))) atTop
  have hL : L < ⊤ := by
    have : L ≤ 1 + L := le_add_self
    exact lt_of_le_of_lt this h
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal (Real.log (q (n + 1)) / Real.log (q n)) <
      ENNReal.ofReal (L.toReal + 1) := by
    refine eventually_lt_of_limsup_lt ?_
    calc L = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hL.ne).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  refine brjuno_lt_top_of_eventually hq (B := L.toReal + 1) ?_
  filter_upwards [hev, eventually_ge_atTop 2] with n hn h2
  have hlog := hq.log_pos n h2
  have := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn
  rw [div_lt_iff₀ hlog] at this
  exact this.le

/-- `𝓑 < ∞ ⇒ β = 0`. -/
theorem beta_eq_zero_of_brjuno_lt_top (h : brjunoSeq q < ⊤) : betaSeq q = 0 :=
  (ENNReal.tendsto_atTop_zero_of_tsum_ne_top h.ne).limsup_eq

/-- `𝓑 = ∞ ⇒ μ = ∞`: every non-Brjuno number is Liouville (Lemma 4.17, first part). -/
theorem mu_eq_top_of_brjuno_eq_top (hq : CFGrowth q) (h : brjunoSeq q = ⊤) : muSeq q = ⊤ := by
  by_contra h'
  exact (brjuno_lt_top_of_mu_lt_top hq (lt_top_iff_ne_top.2 h')).ne h

end chain

/-! ### Continued-fraction denominators -/

section cf

open GenContFract

lemma not_terminatedAt {α : ℝ} (hα : Irrational α) (n : ℕ) :
    ¬(GenContFract.of α).TerminatedAt n := by
  intro h
  obtain ⟨q, hq⟩ := (terminates_iff_rat α).1 ⟨n, h⟩
  exact hα ⟨q, hq.symm⟩

/-- Continued-fraction denominators of an irrational number satisfy `CFGrowth`. -/
theorem cfGrowth {α : ℝ} (hα : Irrational α) : CFGrowth (AMO.cfDen α) where
  one_le n := by
    have hyp : n = 0 ∨ ¬(GenContFract.of α).TerminatedAt (n - 1) := by
      rcases n with _ | n
      · exact Or.inl rfl
      · exact Or.inr (not_terminatedAt hα _)
    have := succ_nth_fib_le_of_nth_den hyp
    refine le_trans ?_ this
    exact_mod_cast Nat.fib_pos.2 n.succ_pos
  two_mul_le n := by
    obtain ⟨gp, hgp⟩ : ∃ gp, (GenContFract.of α).s.get? (n + 1) = some gp :=
      Option.ne_none_iff_exists'.1 (not_terminatedAt hα (n + 1))
    have hrec := dens_recurrence hgp rfl rfl
    have ha : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a hgp)
    have hb : 1 ≤ gp.b := of_one_le_get?_partDen (partDen_eq_s_b hgp)
    have hmono : (GenContFract.of α).dens n ≤ (GenContFract.of α).dens (n + 1) := of_den_mono
    have h0 : 0 ≤ (GenContFract.of α).dens n := zero_le_of_den
    unfold AMO.cfDen
    rw [hrec, ha]
    nlinarith

/-- The `n`-th convergent satisfies `|α - p_n/q_n| ≤ 1 / (q_n q_{n+1})`. -/
lemma abs_sub_convs_le' {α : ℝ} (hα : Irrational α) (n : ℕ) :
    |α - (GenContFract.of α).convs n| ≤ 1 / (AMO.cfDen α n * AMO.cfDen α (n + 1)) :=
  abs_sub_convs_le (not_terminatedAt hα n)

/-- `μ_irr(α) < ∞ ⇒ 𝓑(α) < ∞ ⇒ β(α) = 0` (§1.2). -/
theorem arithmetic_chain {α : ℝ} (hα : Irrational α) :
    (muIrr α < ⊤ → Brjuno α) ∧ (Brjuno α → AMO.beta α = 0) ∧ (¬Brjuno α → Liouville α) :=
  ⟨brjuno_lt_top_of_mu_lt_top (cfGrowth hα), beta_eq_zero_of_brjuno_lt_top,
    fun h => mu_eq_top_of_brjuno_eq_top (cfGrowth hα) (not_lt_top_iff.1 h)⟩

/-- **Lemma 4.17 (`dim:lem:arithmetic`), second part.**  If `α` is Liouville, then for every
exponent `M` and every `N` there is a convergent `p_n/q_n` with `n ≥ N`, `q_n > 1` and
`h = 2π q_n² |α - p_n/q_n| ≤ q_n^{-M}`.  (Taking `M → ∞` along such convergents gives the
sequence with `B_q → ∞` of the paper.) -/
theorem exists_convergent_liouville {α : ℝ} (hα : Irrational α) (hL : Liouville α) (M : ℝ)
    (N : ℕ) : ∃ n ≥ N, 1 < AMO.cfDen α n ∧
      2 * Real.pi * AMO.cfDen α n ^ 2 * |α - (GenContFract.of α).convs n| ≤
        AMO.cfDen α n ^ (-M) := by
  have hq := cfGrowth hα
  set q := AMO.cfDen α
  have hlim : limsup (fun n => ENNReal.ofReal (Real.log (q (n + 1)) / Real.log (q n))) atTop
      = ⊤ := by
    have h : muSeq q = ⊤ := hL
    unfold muSeq at h
    by_contra hne
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, lt_top_iff_ne_top.2 hne⟩).ne h
  have hfreq : ∃ᶠ n in atTop,
      ENNReal.ofReal (max (M + 3) 0) < ENNReal.ofReal (Real.log (q (n + 1)) / Real.log (q n)) :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) (hlim ▸ ENNReal.ofReal_lt_top)
  have hbig : ∀ᶠ n in atTop, 2 * Real.pi ≤ q n ^ (2 : ℝ) := by
    have : Tendsto (fun n => q n ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp hq.tendsto_atTop
    exact this.eventually_ge_atTop _
  obtain ⟨n, hn, hNn, h2n, hbn⟩ :=
    (hfreq.and_eventually ((eventually_ge_atTop N).and
      ((eventually_ge_atTop 2).and hbig))).exists
  refine ⟨n, hNn, hq.one_lt n h2n, ?_⟩
  have hlog := hq.log_pos n h2n
  have hqn := hq.pos n
  have hqn1 := hq.pos (n + 1)
  have hratio : M + 3 < Real.log (q (n + 1)) / Real.log (q n) := by
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_max_right _ _)).1 hn
    exact (le_max_left _ _).trans_lt this
  rw [lt_div_iff₀ hlog] at hratio
  have hgrow : q n ^ (M + 3) ≤ q (n + 1) := by
    rw [← Real.exp_log hqn1, Real.rpow_def_of_pos hqn]
    exact Real.exp_le_exp.2 (by linarith)
  have happrox := abs_sub_convs_le' hα n
  calc 2 * Real.pi * q n ^ 2 * |α - (GenContFract.of α).convs n|
      ≤ 2 * Real.pi * q n ^ 2 * (1 / (q n * q (n + 1))) := by gcongr
    _ = 2 * Real.pi * q n / q (n + 1) := by field_simp
    _ ≤ 2 * Real.pi * q n / q n ^ (M + 3) := by gcongr
    _ = 2 * Real.pi * q n ^ (-M - 2 : ℝ) := by
      rw [mul_div_assoc, show (-M - 2 : ℝ) = 1 - (M + 3) by ring, Real.rpow_sub hqn,
        Real.rpow_one]
    _ ≤ q n ^ (2 : ℝ) * q n ^ (-M - 2 : ℝ) := by gcongr
    _ = q n ^ (-M) := by rw [← Real.rpow_add hqn]; ring_nf

end cf

/-! ### Gap labels -/

/-- The set of allowed internal gap labels `Λ_α = (ℤ + αℤ) ∩ (0,1)`. -/
def gapLabels (α : ℝ) : Set ℝ := {t | ∃ m n : ℤ, t = m + n * α} ∩ Ioo 0 1

/-- `Λ_α = {{nα} : n ∈ ℤ ∖ {0}}` for irrational `α` (§1). -/
theorem gapLabels_eq {α : ℝ} (hα : Irrational α) :
    gapLabels α = {t | ∃ n : ℤ, n ≠ 0 ∧ t = Int.fract (n * α)} := by
  ext t
  simp only [gapLabels, mem_inter_iff, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨m, n, rfl⟩, h0, h1⟩
    have hn : n ≠ 0 := by
      rintro rfl
      have : (0 : ℝ) < m := by simpa using h0
      have : (m : ℝ) < 1 := by simpa using h1
      have h0' : (0 : ℤ) < m := by exact_mod_cast ‹(0 : ℝ) < m›
      have h1' : m < (1 : ℤ) := by exact_mod_cast this
      omega
    refine ⟨n, hn, ?_⟩
    have hfl : ⌊(n : ℝ) * α⌋ = -m := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [Int.fract, hfl]; push_cast; ring
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨-⌊(n : ℝ) * α⌋, n, by rw [Int.fract]; push_cast; ring⟩, ?_, Int.fract_lt_one _⟩
    refine lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm ?_)
    intro h
    rw [Int.fract_eq_iff] at h
    obtain ⟨-, -, k, hk⟩ := h
    have : Irrational ((n : ℝ) * α) := hα.intCast_mul hn
    exact this ⟨(k : ℚ), by push_cast; linarith⟩

end SGD
