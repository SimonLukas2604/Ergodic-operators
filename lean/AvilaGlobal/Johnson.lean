import AvilaGlobal.Background
noncomputable section
open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix Filter Topology Complex L2
namespace AvilaGlobal
open AMO

/-- Max of a continuous `1`-periodic function. -/
lemma periodic_exists_max {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∃ x₀, ∀ x, f x ≤ f x₀ := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 zero_le_one)
    (hf.continuousOn (s := Set.Icc (0:ℝ) 1))
  refine ⟨x₀, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ zero_lt_one x
  rw [hxy]
  exact hx₀ (Set.Ico_subset_Icc_self hy)

lemma periodic_exists_min {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∃ x₀, ∀ x, f x₀ ≤ f x := by
  obtain ⟨x₀, h⟩ := periodic_exists_max hf.neg (fun x => by simp [hp x])
  exact ⟨x₀, fun x => by simpa using h x⟩

lemma periodic_uniform {g : ℝ → ℂ} (hg : Continuous g) (hp : Function.Periodic g 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ s t : ℝ, |s - t| < δ → ‖g s - g t‖ < ε := by
  have huc : UniformContinuousOn g (Set.Icc (-1 : ℝ) 2) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun s t hst => ?_⟩
  set m : ℤ := ⌊s⌋
  have h1 : g s = g (s - m) := (hp.sub_int_mul_eq m).symm.trans (by simp)
  have h2 : g t = g (t - m) := (hp.sub_int_mul_eq m).symm.trans (by simp)
  have hm1 : (m : ℝ) ≤ s := Int.floor_le s
  have hm2 : s < m + 1 := Int.lt_floor_add_one s
  have hst1 : |s - t| < δ := lt_of_lt_of_le hst (min_le_left _ _)
  have hst2 : |s - t| < 1 := lt_of_lt_of_le hst (min_le_right _ _)
  rw [abs_lt] at hst2
  rw [h1, h2, ← dist_eq_norm]
  refine h (s - m) ⟨by linarith, by linarith⟩ (t - m) ⟨by linarith, by linarith⟩ ?_
  rw [Real.dist_eq]; convert hst1 using 2; ring


/-! ### The Schrödinger cocycle on the real line, solutions and Wronskians -/

/-- The Schrödinger cocycle `A^{(E-v)}` on the real line. -/
def Acoc (v : ℂ → ℂ) (E : ℝ) : ℝ → M2 := shift (schr (eShift E v)) 0

/-- The phase vector `(χ_k, χ_{k-1})`. -/
def Φ (χ : ℤ → ℂ) (k : ℤ) : Fin 2 → ℂ := ![χ k, χ (k - 1)]

/-- `χ` solves `(H_x - E) χ = 0` at the site `n`. -/
def SolAt (α : ℝ) (v : ℂ → ℂ) (E x : ℝ) (χ : ℤ → ℂ) (n : ℤ) : Prop :=
  χ (n + 1) + χ (n - 1) + (v ((x + n * α : ℝ) : ℂ) - E) * χ n = 0

/-- The `2 × 2` determinant of two column vectors. -/
def det2 (a b : Fin 2 → ℂ) : ℂ := a 0 * b 1 - a 1 * b 0

/-- A canonical vector in a real line: `(a₀ + i a₁) a + (b₀ + i b₁) b`. -/
def pc (a : Fin 2 → ℂ) : ℂ := a 0 + I * a 1

def sec (a b : Fin 2 → ℂ) : Fin 2 → ℂ := pc a • a + pc b • b

section Dyn
variable {α : ℝ} {v : ℂ → ℂ} {E : ℝ}

lemma Acoc_apply (t : ℝ) : Acoc v E t = !![(E:ℂ) - v t, -1; 1, 0] := by
  simp [Acoc, shift, schr, eShift]

lemma det_Acoc (t : ℝ) : (Acoc v E t).det = 1 := det_schr _ _

lemma Acoc_mulVec (t : ℝ) (a b : ℂ) :
    Acoc v E t *ᵥ ![a, b] = ![((E:ℂ) - v t) * a - b, a] := by
  rw [Acoc_apply]
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring

lemma step_sol {x : ℝ} {χ : ℤ → ℂ} {j : ℤ} (h : SolAt α v E x χ j) :
    Acoc v E (x + j * α) *ᵥ Φ χ j = Φ χ (j + 1) := by
  unfold SolAt at h
  have h1 : χ (j + 1) = ((E:ℂ) - v ((x + j * α : ℝ) : ℂ)) * χ j - χ (j - 1) := by
    linear_combination h
  simp only [Φ]
  rw [Acoc_mulVec, h1, add_sub_cancel_right]

lemma iter_sol {x : ℝ} {χ : ℤ → ℂ} {k : ℤ} {m : ℕ}
    (h : ∀ n : ℤ, k ≤ n → n < k + m → SolAt α v E x χ n) :
    iter α (Acoc v E) m (x + k * α) *ᵥ Φ χ k = Φ χ (k + m) := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    have ih' := ih (fun n h1 h2 => h n h1 (by push_cast; omega))
    have hs := step_sol (h (k + m) (by omega) (by push_cast; omega))
    have hph : x + (k:ℝ) * α + (m:ℝ) * α = x + ((k + m : ℤ) : ℝ) * α := by push_cast; ring
    rw [iter, ← mulVec_mulVec, ih', hph, hs]
    congr 1; push_cast; ring

lemma iter_sol0 {x : ℝ} {χ : ℤ → ℂ} (m : ℕ) (h : ∀ n : ℤ, 0 ≤ n → SolAt α v E x χ n) :
    iter α (Acoc v E) m x *ᵥ Φ χ 0 = Φ χ m := by
  have := iter_sol (α := α) (v := v) (E := E) (x := x) (χ := χ) (k := 0) (m := m)
    (fun n h1 _ => h n h1)
  simpa using this

/-- Backward version: from `-n` to `-m`. -/
lemma iter_sol_bwd {x : ℝ} {χ : ℤ → ℂ} {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ j : ℤ, j < 0 → SolAt α v E x χ j) :
    iter α (Acoc v E) (n - m) (x - n * α) *ᵥ Φ χ (-n) = Φ χ (-m) := by
  have := iter_sol (α := α) (v := v) (E := E) (x := x) (χ := χ) (k := -n) (m := n - m)
    (fun j _ h2 => h j (by push_cast [hmn] at h2; omega))
  have e1 : x + ((-(n:ℤ) : ℤ) : ℝ) * α = x - n * α := by push_cast; ring
  have e2 : -(n:ℤ) + ((n - m : ℕ) : ℤ) = -m := by push_cast [hmn]; ring
  rw [e1, e2] at this
  exact this

lemma iter_succ' (m : ℕ) (x : ℝ) :
    iter α (Acoc v E) (m + 1) x = iter α (Acoc v E) m (x + α) * Acoc v E x := by
  rw [add_comm, iter_add]
  simp [iter]

lemma det2_mulVec (M : M2) (a b : Fin 2 → ℂ) :
    det2 (M *ᵥ a) (M *ᵥ b) = M.det * det2 a b := by
  simp [det2, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]; ring

lemma det2_iter (m : ℕ) (y : ℝ) (a b : Fin 2 → ℂ) :
    det2 (iter α (Acoc v E) m y *ᵥ a) (iter α (Acoc v E) m y *ᵥ b) = det2 a b := by
  rw [det2_mulVec, det_iter (fun t => det_Acoc t), one_mul]

lemma iter_injective {m : ℕ} {y : ℝ} {a b : Fin 2 → ℂ}
    (h : iter α (Acoc v E) m y *ᵥ a = iter α (Acoc v E) m y *ᵥ b) : a = b := by
  have hu : IsUnit (iter α (Acoc v E) m y).det := by
    rw [det_iter (fun t => det_Acoc t)]; exact isUnit_one
  have h2 : (iter α (Acoc v E) m y)⁻¹ *ᵥ (iter α (Acoc v E) m y *ᵥ a) =
      (iter α (Acoc v E) m y)⁻¹ *ᵥ (iter α (Acoc v E) m y *ᵥ b) := by rw [h]
  rwa [mulVec_mulVec, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, one_mulVec] at h2

lemma norm_vec2_le (w : Fin 2 → ℂ) : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => ?_)
  fin_cases i
  · simp
  · simp

lemma norm_det2_le (a b : Fin 2 → ℂ) : ‖det2 a b‖ ≤ 2 * (‖a‖ * ‖b‖) := by
  unfold det2
  have h0 := norm_le_pi_norm a 0
  have h1 := norm_le_pi_norm a 1
  have h2 := norm_le_pi_norm b 0
  have h3 := norm_le_pi_norm b 1
  calc ‖a 0 * b 1 - a 1 * b 0‖ ≤ ‖a 0‖ * ‖b 1‖ + ‖a 1‖ * ‖b 0‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ := by gcongr
    _ = _ := by ring

lemma det2_eq_zero_of {a b : Fin 2 → ℂ} {B : ℝ}
    (h : ∀ ε > 0, ∃ a' b' : Fin 2 → ℂ, det2 a' b' = det2 a b ∧ ‖a'‖ < ε ∧ ‖b'‖ ≤ B) :
    det2 a b = 0 := by
  by_contra hne
  have hpos : 0 < ‖det2 a b‖ := norm_pos_iff.2 hne
  set d := ‖det2 a b‖
  set B' := max B 1
  have hB1 : 1 ≤ B' := le_max_right _ _
  obtain ⟨a', b', hd, ha, hb⟩ := h (d / (2 * B' + 1)) (div_pos hpos (by linarith))
  have h1 := norm_det2_le a' b'
  rw [hd] at h1
  have hB' : ‖b'‖ ≤ B' := hb.trans (le_max_left _ _)
  have h2 : 2 * (‖a'‖ * ‖b'‖) ≤ 2 * (d / (2 * B' + 1) * B') := by
    gcongr
  have hlt : 2 * (d / (2 * B' + 1) * B') < d := by
    rw [show 2 * (d / (2 * B' + 1) * B') = d * (2 * B' / (2 * B' + 1)) by ring]
    exact mul_lt_of_lt_one_right hpos ((div_lt_one (by linarith)).2 (by linarith))
  linarith

lemma par_of_det2 {a b : Fin 2 → ℂ} (hb : b ≠ 0) (h : det2 a b = 0) : ∃ c : ℂ, a = c • b := by
  unfold det2 at h
  by_cases h0 : b 0 = 0
  · have h1 : b 1 ≠ 0 := by
      intro h1; apply hb; ext i; fin_cases i <;> simp [h0, h1]
    refine ⟨a 1 / b 1, ?_⟩
    have ha0 : a 0 = 0 := by
      rw [h0, mul_zero, sub_zero] at h
      exact (mul_eq_zero.1 h).resolve_right h1
    ext i; fin_cases i <;> simp [ha0, h0, h1]
  · refine ⟨a 0 / b 0, ?_⟩
    ext i; fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      first | linear_combination h | linear_combination -h

lemma sec_ne_zero {a b : Fin 2 → ℂ} (ha : ∀ i, (a i).im = 0) (hb : ∀ i, (b i).im = 0)
    (h : a ≠ 0 ∨ b ≠ 0) : sec a b ≠ 0 := by
  intro hs
  have e0 := congrFun hs 0
  have e1 := congrFun hs 1
  simp only [sec, pc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e1
  have r0 := congrArg Complex.re e0
  have i1 := congrArg Complex.im e1
  simp [Complex.mul_re, Complex.mul_im, ha 0, ha 1, hb 0, hb 1] at r0 i1
  have h1 : (a 0).re = 0 ∧ (b 0).re = 0 := by
    constructor <;> nlinarith [sq_nonneg (a 0).re, sq_nonneg (b 0).re]
  have h2 : (a 1).re = 0 ∧ (b 1).re = 0 := by
    constructor <;> nlinarith [sq_nonneg (a 1).re, sq_nonneg (b 1).re]
  rcases h with h | h <;> apply h <;> ext i <;> fin_cases i <;> apply Complex.ext <;>
    simp [h1, h2, ha, hb]

lemma norm_pc_le (a : Fin 2 → ℂ) : ‖pc a‖ ≤ ‖a 0‖ + ‖a 1‖ := by
  unfold pc
  refine (norm_add_le _ _).trans ?_
  simp

/-- Choosing a uniform time from a uniform square-summability bound and quasi-multiplicativity. -/
lemma exists_n_of_sq_sum {g : ℕ → ℝ → ℝ} {c K : ℝ} (hc : 0 < c)
    (hsum : ∀ N x, ∑ m ∈ Finset.range N, g m x ^ 2 ≤ K)
    (hmul : ∀ x m n, m ≤ n → ∃ x', c * g n x ≤ g m x * g (n - m) x') :
    ∃ N, ∀ n ≥ N, ∀ x, g n x < c := by
  set K' := |K| + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  have hKK : K < K' := by have := le_abs_self K; linarith
  have hsq : ∀ m x, g m x ^ 2 ≤ K' := by
    intro m x
    have h1 := hsum (m + 1) x
    rw [Finset.sum_range_succ] at h1
    have h2 : 0 ≤ ∑ i ∈ Finset.range m, g i x ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  refine ⟨⌈K' ^ 2 / c ^ 4⌉₊ + 1, fun n hn x => ?_⟩
  by_contra hge
  push Not at hge
  have hlow : ∀ m ∈ Finset.range n, c ^ 4 / K' ≤ g m x ^ 2 := by
    intro m hm
    obtain ⟨x', hx'⟩ := hmul x m n (Finset.mem_range.1 hm).le
    have h1 : c ^ 2 ≤ g m x * g (n - m) x' := by
      have := mul_le_mul_of_nonneg_left hge hc.le
      nlinarith
    have h3 : (c ^ 2) ^ 2 ≤ (g m x * g (n - m) x') ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h4 : g m x ^ 2 * g (n - m) x' ^ 2 ≤ g m x ^ 2 * K' :=
      mul_le_mul_of_nonneg_left (hsq _ _) (sq_nonneg _)
    have h2 : c ^ 4 ≤ g m x ^ 2 * K' := by
      calc c ^ 4 = (c ^ 2) ^ 2 := by ring
        _ ≤ (g m x * g (n - m) x') ^ 2 := h3
        _ = g m x ^ 2 * g (n - m) x' ^ 2 := by ring
        _ ≤ _ := h4
    rw [div_le_iff₀ hK'pos]; exact h2
  have h4 := Finset.sum_le_sum hlow
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
  have h4' := (h4.trans (hsum n x)).trans hKK.le
  have h5 : (n : ℝ) * c ^ 4 ≤ K' ^ 2 := by
    have e : (n : ℝ) * (c ^ 4 / K') * K' = n * c ^ 4 := by field_simp
    calc (n : ℝ) * c ^ 4 = n * (c ^ 4 / K') * K' := e.symm
      _ ≤ K' * K' := mul_le_mul_of_nonneg_right h4' hK'pos.le
      _ = K' ^ 2 := by ring
  have h6 : K' ^ 2 / c ^ 4 < n := by
    have := Nat.le_ceil (K' ^ 2 / c ^ 4)
    have h7 : ((⌈K' ^ 2 / c ^ 4⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h7; linarith
  have := (div_lt_iff₀ (by positivity)).1 h6
  linarith

/-! ### `ℓ²` facts -/

lemma L2_norm_apply_le (u : L2 ℤ) (n : ℤ) : ‖u n‖ ≤ ‖u‖ :=
  lp.norm_apply_le_norm (by norm_num) u n

lemma L2_sum_sq_le (u : L2 ℤ) {f : ℕ → ℤ} (hf : Function.Injective f) (N : ℕ) :
    ∑ m ∈ Finset.range N, ‖u (f m)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [L2.norm_sq_eq_tsum]
  have := (L2.summable_norm_sq u).sum_le_tsum ((Finset.range N).map ⟨f, hf⟩)
    (fun _ _ => sq_nonneg _)
  simpa [Finset.sum_map] using this

lemma L2_small (u : L2 ℤ) {f : ℕ → ℤ} (hf : Function.Injective f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M, ∀ m ≥ M, ‖u (f m)‖ < ε := by
  have h1 := (L2.summable_norm_sq u).tendsto_cofinite_zero
  have h2 : Tendsto (fun m => ‖u (f m)‖ ^ 2) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]; exact h1.comp hf.tendsto_cofinite
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    (h2.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε ^ 2)))
  exact ⟨M, fun m hm =>
    (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 (hM m hm)⟩

lemma norm_Φ_le (u : L2 ℤ) (k : ℤ) : ‖Φ u k‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i => ?_)
  fin_cases i
  · simpa [Φ] using L2_norm_apply_le u k
  · simpa [Φ] using L2_norm_apply_le u (k - 1)

lemma Φ_small (u : L2 ℤ) {f : ℕ → ℤ} (hf : Function.Injective f) {ε : ℝ} (hε : 0 < ε) :
    ∃ M, ∀ m ≥ M, ‖Φ u (f m)‖ < ε := by
  obtain ⟨M1, h1⟩ := L2_small u hf hε
  obtain ⟨M2, h2⟩ := L2_small u (f := fun m => f m - 1)
    (fun a b hab => hf (by simpa using hab)) hε
  refine ⟨max M1 M2, fun m hm => (pi_norm_lt_iff hε).2 (fun i => ?_)⟩
  fin_cases i
  · simpa [Φ] using h1 m (le_of_max_le_left hm)
  · simpa [Φ] using h2 m (le_of_max_le_right hm)

lemma comb_small (u w : L2 ℤ) (p q : ℂ) {f : ℕ → ℤ} (hf : Function.Injective f) {ε : ℝ}
    (hε : 0 < ε) : ∃ M, ∀ m ≥ M, ‖p • Φ u (f m) + q • Φ w (f m)‖ < ε := by
  set ε' := ε / (‖p‖ + ‖q‖ + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨M1, h1⟩ := Φ_small u hf hε'
  obtain ⟨M2, h2⟩ := Φ_small w hf hε'
  refine ⟨max M1 M2, fun m hm => ?_⟩
  have a1 := h1 m (le_of_max_le_left hm)
  have a2 := h2 m (le_of_max_le_right hm)
  calc ‖p • Φ u (f m) + q • Φ w (f m)‖ ≤ ‖p‖ * ‖Φ u (f m)‖ + ‖q‖ * ‖Φ w (f m)‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, norm_smul]
    _ ≤ ‖p‖ * ε' + ‖q‖ * ε' := by gcongr
    _ < ε := by
        have : (‖p‖ + ‖q‖) * ε' < ε := by
          rw [show (‖p‖ + ‖q‖) * ε' = ε * ((‖p‖ + ‖q‖) / (‖p‖ + ‖q‖ + 1)) by
            simp only [ε']; ring]
          exact mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).2 (by linarith))
        linarith

lemma sq_add4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- The square-sum bound for a combination `p Φ_u(f m) + q Φ_w(f m)`. -/
lemma comb_sum_le (u w : L2 ℤ) (p q : ℂ) {C : ℝ} (hu : ‖u‖ ≤ C) (hw : ‖w‖ ≤ C)
    (hp : ‖p‖ ≤ 2 * C) (hq : ‖q‖ ≤ 2 * C) {f : ℕ → ℤ} (hf : Function.Injective f) (N : ℕ) :
    ∑ m ∈ Finset.range N, ‖p • Φ u (f m) + q • Φ w (f m)‖ ^ 2 ≤ 64 * C ^ 4 := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hu
  have hf' : Function.Injective (fun m => f m - 1) := fun a b hab => hf (by simpa using hab)
  have key : ∀ m, ‖p • Φ u (f m) + q • Φ w (f m)‖ ^ 2 ≤
      16 * C ^ 2 * (‖u (f m)‖ ^ 2 + ‖u (f m - 1)‖ ^ 2 + ‖w (f m)‖ ^ 2 + ‖w (f m - 1)‖ ^ 2) := by
    intro m
    have e1 : ‖p • Φ u (f m) + q • Φ w (f m)‖ ≤
        2 * C * (‖u (f m)‖ + ‖u (f m - 1)‖ + ‖w (f m)‖ + ‖w (f m - 1)‖) := by
      calc ‖p • Φ u (f m) + q • Φ w (f m)‖ ≤ ‖p‖ * ‖Φ u (f m)‖ + ‖q‖ * ‖Φ w (f m)‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_smul, norm_smul]
        _ ≤ 2 * C * (‖u (f m)‖ + ‖u (f m - 1)‖) + 2 * C * (‖w (f m)‖ + ‖w (f m - 1)‖) := by
            gcongr
            · simpa [Φ] using norm_vec2_le (Φ u (f m))
            · simpa [Φ] using norm_vec2_le (Φ w (f m))
        _ = _ := by ring
    have e2 := pow_le_pow_left₀ (norm_nonneg _) e1 2
    have e3 := sq_add4_le ‖u (f m)‖ ‖u (f m - 1)‖ ‖w (f m)‖ ‖w (f m - 1)‖
    calc _ ≤ _ := e2
      _ = 4 * C ^ 2 * (‖u (f m)‖ + ‖u (f m - 1)‖ + ‖w (f m)‖ + ‖w (f m - 1)‖) ^ 2 := by ring
      _ ≤ 4 * C ^ 2 * (4 * (‖u (f m)‖ ^ 2 + ‖u (f m - 1)‖ ^ 2 + ‖w (f m)‖ ^ 2
            + ‖w (f m - 1)‖ ^ 2)) := by gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum (fun m _ => key m)).trans ?_
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have s1 := L2_sum_sq_le u hf N
  have s2 := L2_sum_sq_le u hf' N
  have s3 := L2_sum_sq_le w hf N
  have s4 := L2_sum_sq_le w hf' N
  have hu2 : ‖u‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hw2 : ‖w‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  have : (∑ m ∈ Finset.range N, ‖u (f m)‖ ^ 2) + (∑ m ∈ Finset.range N, ‖u (f m - 1)‖ ^ 2) +
      (∑ m ∈ Finset.range N, ‖w (f m)‖ ^ 2) + (∑ m ∈ Finset.range N, ‖w (f m - 1)‖ ^ 2)
      ≤ 4 * C ^ 2 := by linarith
  calc 16 * C ^ 2 * _ ≤ 16 * C ^ 2 * (4 * C ^ 2) := by gcongr
    _ = 64 * C ^ 4 := by ring

end Dyn


/-! ### From Green data to uniform hyperbolicity -/

/-- Solutions of `(H_x - E) G = δ_j`, uniformly bounded, real, continuous and periodic in `x`. -/
structure Green (α : ℝ) (v : ℂ → ℂ) (E C : ℝ) (G : ℝ → ℤ → L2 ℤ) : Prop where
  eq : ∀ x j n, G x j (n + 1) + G x j (n - 1) + (v ((x + n * α : ℝ) : ℂ) - E) * G x j n =
    if n = j then 1 else 0
  norm_le : ∀ x j, ‖G x j‖ ≤ C
  real : ∀ x j n, (G x j n).im = 0
  cont : ∀ j n, Continuous fun x => G x j n
  per : ∀ x j, G (x + 1) j = G x j

/-- The stable vector. -/
def sv (G : ℝ → ℤ → L2 ℤ) (x : ℝ) : Fin 2 → ℂ := sec (Φ (G x (-1)) 0) (Φ (G x (-2)) 0)

/-- The unstable vector. -/
def uv (G : ℝ → ℤ → L2 ℤ) (x : ℝ) : Fin 2 → ℂ := sec (Φ (G x 0) 0) (Φ (G x 1) 0)

/-- Backward preimages of the unstable vector. -/
def zv (G : ℝ → ℤ → L2 ℤ) (m : ℕ) (x : ℝ) : Fin 2 → ℂ :=
  pc (Φ (G x 0) 0) • Φ (G x 0) (-m) + pc (Φ (G x 1) 0) • Φ (G x 1) (-m)

lemma det2_eq_zero_of' {a b : Fin 2 → ℂ} {B : ℝ}
    (h : ∀ ε > 0, ∃ a' b' : Fin 2 → ℂ, det2 a' b' = det2 a b ∧ ‖a'‖ ≤ B ∧ ‖b'‖ < ε) :
    det2 a b = 0 := by
  have hab : ∀ a b : Fin 2 → ℂ, det2 b a = -det2 a b := fun a b => by simp [det2]; ring
  have := det2_eq_zero_of (a := b) (b := a) (B := B) (fun ε hε => by
    obtain ⟨a', b', h1, h2, h3⟩ := h ε hε
    exact ⟨b', a', by rw [hab, h1, ← hab], h3, h2⟩)
  rw [hab] at this
  exact neg_eq_zero.1 this

lemma continuous_sec {a b : ℝ → Fin 2 → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => sec (a x) (b x) := by
  have hp : ∀ c : ℝ → Fin 2 → ℂ, Continuous c → Continuous fun x => pc (c x) := fun c hc =>
    ((continuous_apply 0).comp hc).add (continuous_const.mul ((continuous_apply 1).comp hc))
  exact ((hp a ha).smul ha).add ((hp b hb).smul hb)

section GreenUH
variable {α : ℝ} {v : ℂ → ℂ} {E C : ℝ} {G : ℝ → ℤ → L2 ℤ}

lemma wronskian_bwd {x : ℝ} {χ ξ : L2 ℤ} {k : ℤ} (hχ : ∀ n < k, SolAt α v E x χ n)
    (hξ : ∀ n < k, SolAt α v E x ξ n) : det2 (Φ χ k) (Φ ξ k) = 0 := by
  refine det2_eq_zero_of (B := ‖ξ‖) (fun ε hε => ?_)
  obtain ⟨M, hM⟩ := Φ_small χ (f := fun m : ℕ => k - m) (fun a b h => by simp only at h; omega) hε
  refine ⟨Φ χ (k - M), Φ ξ (k - M), ?_, hM M le_rfl, norm_Φ_le _ _⟩
  have h1 := iter_sol (α := α) (v := v) (E := E) (x := x) (χ := χ) (k := k - M) (m := M)
    (fun n _ h2 => hχ n (by omega))
  have h2 := iter_sol (α := α) (v := v) (E := E) (x := x) (χ := ξ) (k := k - M) (m := M)
    (fun n _ h2 => hξ n (by omega))
  rw [sub_add_cancel] at h1 h2
  rw [← h1, ← h2, det2_iter]

lemma wronskian_fwd {x : ℝ} {χ ξ : L2 ℤ} {k : ℤ} (hχ : ∀ n ≥ k, SolAt α v E x χ n)
    (hξ : ∀ n ≥ k, SolAt α v E x ξ n) : det2 (Φ χ k) (Φ ξ k) = 0 := by
  refine det2_eq_zero_of (B := ‖ξ‖) (fun ε hε => ?_)
  obtain ⟨M, hM⟩ := Φ_small χ (f := fun m : ℕ => k + m) (fun a b h => by simp only at h; omega) hε
  refine ⟨Φ χ (k + M), Φ ξ (k + M), ?_, hM M le_rfl, norm_Φ_le _ _⟩
  have h1 := iter_sol (α := α) (v := v) (E := E) (x := x) (χ := χ) (k := k) (m := M)
    (fun n h1 _ => hχ n h1)
  have h2 := iter_sol (α := α) (v := v) (E := E) (x := x) (χ := ξ) (k := k) (m := M)
    (fun n h1 _ => hξ n h1)
  rw [← h1, ← h2, det2_iter]

variable (hG : Green α v E C G)
include hG

lemma Green.sol {x : ℝ} {j n : ℤ} (h : n ≠ j) : SolAt α v E x (G x j) n := by
  have := hG.eq x j n
  rwa [if_neg h] at this

lemma Green.eq_at (x : ℝ) (j n a b : ℤ) (ha : n + 1 = a) (hb : n - 1 = b) :
    G x j a + G x j b + (v ((x + n * α : ℝ) : ℂ) - E) * G x j n = if n = j then 1 else 0 := by
  subst ha hb; exact hG.eq x j n

lemma Green.C_nonneg : 0 ≤ C := (norm_nonneg _).trans (hG.norm_le 0 0)

lemma Green.pc_le (x : ℝ) (j k : ℤ) : ‖pc (Φ (G x j) k)‖ ≤ 2 * C := by
  refine (norm_pc_le _).trans ?_
  have h1 := (L2_norm_apply_le (G x j) k).trans (hG.norm_le x j)
  have h2 := (L2_norm_apply_le (G x j) (k - 1)).trans (hG.norm_le x j)
  simp only [Φ, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

lemma Green.cont_Φ (j k : ℤ) : Continuous fun x => Φ (G x j) k := by
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · simpa [Φ] using hG.cont j k
  · simpa [Φ] using hG.cont j (k - 1)

lemma Green.real_Φ (x : ℝ) (j k : ℤ) (i : Fin 2) : (Φ (G x j) k i).im = 0 := by
  fin_cases i
  · simpa [Φ] using hG.real x j k
  · simpa [Φ] using hG.real x j (k - 1)

/-! #### The stable direction -/

lemma Green.sv_fwd (x : ℝ) (k : ℕ) : iter α (Acoc v E) k x *ᵥ sv G x =
    pc (Φ (G x (-1)) 0) • Φ (G x (-1)) k + pc (Φ (G x (-2)) 0) • Φ (G x (-2)) k := by
  simp only [sv, sec, mulVec_add, mulVec_smul]
  rw [iter_sol0 k (fun n hn => hG.sol (by omega)), iter_sol0 k (fun n hn => hG.sol (by omega))]

lemma Green.sv_small (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M, ∀ k ≥ M, ‖iter α (Acoc v E) k x *ᵥ sv G x‖ < ε := by
  obtain ⟨M, hM⟩ := comb_small (G x (-1)) (G x (-2)) (pc (Φ (G x (-1)) 0))
    (pc (Φ (G x (-2)) 0)) (f := fun m : ℕ => (m : ℤ)) Nat.cast_injective hε
  exact ⟨M, fun k hk => by rw [hG.sv_fwd]; exact hM k hk⟩

lemma Green.sv_bdd (x : ℝ) (k : ℕ) : ‖iter α (Acoc v E) k x *ᵥ sv G x‖ ≤ 4 * C * C := by
  rw [hG.sv_fwd]
  have hC := hG.C_nonneg
  calc _ ≤ ‖pc (Φ (G x (-1)) 0)‖ * ‖Φ (G x (-1)) k‖ + ‖pc (Φ (G x (-2)) 0)‖ * ‖Φ (G x (-2)) k‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, norm_smul]
    _ ≤ 2 * C * C + 2 * C * C := add_le_add
        (mul_le_mul (hG.pc_le x (-1) 0) ((norm_Φ_le _ _).trans (hG.norm_le x (-1)))
          (norm_nonneg _) (by linarith))
        (mul_le_mul (hG.pc_le x (-2) 0) ((norm_Φ_le _ _).trans (hG.norm_le x (-2)))
          (norm_nonneg _) (by linarith))
    _ = 4 * C * C := by ring

lemma Green.sv_ne (x : ℝ) : sv G x ≠ 0 := by
  refine sec_ne_zero (hG.real_Φ x (-1) 0) (hG.real_Φ x (-2) 0) ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have a0 : G x (-1) 0 = 0 := by simpa [Φ] using congrFun ha 0
  have a1 : G x (-1) (-1) = 0 := by simpa [Φ] using congrFun ha 1
  have b0 : G x (-2) 0 = 0 := by simpa [Φ] using congrFun hb 0
  have b1 : G x (-2) (-1) = 0 := by simpa [Φ] using congrFun hb 1
  have c1 : G x (-1) (-2) = 1 := by
    have e := hG.eq_at x (-1) (-1) 0 (-2) (by norm_num) (by norm_num)
    rw [a1, mul_zero, add_zero, a0, zero_add, if_pos rfl] at e; exact e
  have c2 : G x (-2) (-2) = 0 := by
    have e := hG.eq_at x (-2) (-1) 0 (-2) (by norm_num) (by norm_num)
    rw [b1, mul_zero, add_zero, b0, zero_add, if_neg (by norm_num)] at e; exact e
  have c3 : G x (-2) (-3) = 1 := by
    have e := hG.eq_at x (-2) (-2) (-1) (-3) (by norm_num) (by norm_num)
    rw [c2, mul_zero, add_zero, b1, zero_add, if_pos rfl] at e; exact e
  have hdet : det2 (Φ (G x (-1)) (-2)) (Φ (G x (-2)) (-2)) = 1 := by
    simp only [det2, Φ, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (-2 : ℤ) - 1 = -3 by norm_num, c1, c2, c3]; ring
  have hz : det2 (Φ (G x (-1)) (-2)) (Φ (G x (-2)) (-2)) = 0 :=
    wronskian_bwd (fun n hn => hG.sol (by omega)) (fun n hn => hG.sol (by omega))
  rw [hdet] at hz
  exact one_ne_zero hz

lemma Green.sv_inv (x : ℝ) : ∃ c : ℂ, Acoc v E x *ᵥ sv G x = c • sv G (x + α) := by
  refine par_of_det2 (hG.sv_ne (x + α)) (det2_eq_zero_of (B := 4 * C * C) (fun ε hε => ?_))
  obtain ⟨M, hM⟩ := hG.sv_small x hε
  refine ⟨iter α (Acoc v E) M (x + α) *ᵥ (Acoc v E x *ᵥ sv G x),
    iter α (Acoc v E) M (x + α) *ᵥ sv G (x + α), det2_iter _ _ _ _, ?_, hG.sv_bdd _ _⟩
  rw [mulVec_mulVec, ← iter_succ']
  exact hM (M + 1) (by omega)

lemma Green.sv_iter_inv (m : ℕ) (x : ℝ) :
    ∃ c : ℂ, iter α (Acoc v E) m x *ᵥ sv G x = c • sv G (x + m * α) := by
  induction m with
  | zero => exact ⟨1, by simp [iter]⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := hG.sv_inv (x + m * α)
    refine ⟨c * c', ?_⟩
    rw [iter, ← mulVec_mulVec, hc, mulVec_smul, hc', smul_smul,
      show x + (m : ℝ) * α + α = x + ((m + 1 : ℕ) : ℝ) * α by push_cast; ring]

lemma Green.sv_cont : Continuous (sv G) :=
  continuous_sec (hG.cont_Φ (-1) 0) (hG.cont_Φ (-2) 0)

lemma Green.sv_per : Function.Periodic (sv G) 1 := fun x => by
  simp only [sv, hG.per]

lemma Green.sv_sum (N : ℕ) (x : ℝ) :
    ∑ m ∈ Finset.range N, ‖iter α (Acoc v E) m x *ᵥ sv G x‖ ^ 2 ≤ 64 * C ^ 4 := by
  simp only [hG.sv_fwd]
  exact comb_sum_le _ _ _ _ (hG.norm_le x (-1)) (hG.norm_le x (-2)) (hG.pc_le x (-1) 0)
    (hG.pc_le x (-2) 0) (f := fun m : ℕ => (m : ℤ)) Nat.cast_injective N

lemma Green.sv_mul {c : ℝ} (hc : ∀ x, c ≤ ‖sv G x‖) (x : ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∃ x', c * ‖iter α (Acoc v E) n x *ᵥ sv G x‖ ≤
      ‖iter α (Acoc v E) m x *ᵥ sv G x‖ * ‖iter α (Acoc v E) (n - m) x' *ᵥ sv G x'‖ := by
  obtain ⟨l, hl⟩ := hG.sv_iter_inv m x
  refine ⟨x + m * α, ?_⟩
  have hsplit : iter α (Acoc v E) n x =
      iter α (Acoc v E) (n - m) (x + m * α) * iter α (Acoc v E) m x := by
    rw [← iter_add, Nat.add_sub_cancel' hmn]
  rw [hsplit, ← mulVec_mulVec, hl, mulVec_smul]
  simp only [norm_smul]
  set a := ‖iter α (Acoc v E) (n - m) (x + m * α) *ᵥ sv G (x + m * α)‖
  calc c * (‖l‖ * a) = (‖l‖ * a) * c := by ring
    _ ≤ (‖l‖ * a) * ‖sv G (x + m * α)‖ :=
        mul_le_mul_of_nonneg_left (hc _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖l‖ * ‖sv G (x + m * α)‖ * a := by ring

/-! #### The unstable direction -/

lemma Green.zv_bwd {m n : ℕ} (hmn : m ≤ n) (x : ℝ) :
    iter α (Acoc v E) (n - m) (x - n * α) *ᵥ zv G n x = zv G m x := by
  simp only [zv, mulVec_add, mulVec_smul]
  rw [iter_sol_bwd hmn (fun j hj => hG.sol (by omega)),
    iter_sol_bwd hmn (fun j hj => hG.sol (by omega))]

lemma Green.zv_uv (n : ℕ) (x : ℝ) :
    iter α (Acoc v E) n (x - n * α) *ᵥ zv G n x = uv G x := by
  have := hG.zv_bwd (Nat.zero_le n) x
  rw [Nat.sub_zero] at this
  rw [this]
  simp [zv, uv, sec]

lemma Green.zv_small (x : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ M, ∀ k ≥ M, ‖zv G k x‖ < ε :=
  comb_small (G x 0) (G x 1) (pc (Φ (G x 0) 0)) (pc (Φ (G x 1) 0))
    (f := fun m : ℕ => -(m : ℤ)) (fun a b h => by simp only at h; omega) hε

lemma Green.zv_bdd (k : ℕ) (x : ℝ) : ‖zv G k x‖ ≤ 4 * C * C := by
  have hC := hG.C_nonneg
  unfold zv
  calc _ ≤ ‖pc (Φ (G x 0) 0)‖ * ‖Φ (G x 0) (-k)‖ + ‖pc (Φ (G x 1) 0)‖ * ‖Φ (G x 1) (-k)‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, norm_smul]
    _ ≤ 2 * C * C + 2 * C * C := add_le_add
        (mul_le_mul (hG.pc_le x 0 0) ((norm_Φ_le _ _).trans (hG.norm_le x 0))
          (norm_nonneg _) (by linarith))
        (mul_le_mul (hG.pc_le x 1 0) ((norm_Φ_le _ _).trans (hG.norm_le x 1))
          (norm_nonneg _) (by linarith))
    _ = 4 * C * C := by ring

lemma Green.uv_ne (x : ℝ) : uv G x ≠ 0 := by
  refine sec_ne_zero (hG.real_Φ x 0 0) (hG.real_Φ x 1 0) ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have a0 : G x 0 0 = 0 := by simpa [Φ] using congrFun ha 0
  have a1 : G x 0 (-1) = 0 := by simpa [Φ] using congrFun ha 1
  have b0 : G x 1 0 = 0 := by simpa [Φ] using congrFun hb 0
  have b1 : G x 1 (-1) = 0 := by simpa [Φ] using congrFun hb 1
  have c1 : G x 0 1 = 1 := by
    have e := hG.eq_at x 0 0 1 (-1) (by norm_num) (by norm_num)
    rw [a0, mul_zero, add_zero, a1, add_zero, if_pos rfl] at e; exact e
  have c2 : G x 1 1 = 0 := by
    have e := hG.eq_at x 1 0 1 (-1) (by norm_num) (by norm_num)
    rw [b0, mul_zero, add_zero, b1, add_zero, if_neg (by norm_num)] at e; exact e
  have c3 : G x 1 2 = 1 := by
    have e := hG.eq_at x 1 1 2 0 (by norm_num) (by norm_num)
    rw [c2, mul_zero, add_zero, b0, add_zero, if_pos rfl] at e; exact e
  have hdet : det2 (Φ (G x 0) 2) (Φ (G x 1) 2) = -1 := by
    simp only [det2, Φ, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (2 : ℤ) - 1 = 1 by norm_num, c1, c2, c3]; ring
  have hz : det2 (Φ (G x 0) 2) (Φ (G x 1) 2) = 0 :=
    wronskian_fwd (fun n hn => hG.sol (by omega)) (fun n hn => hG.sol (by omega))
  rw [hdet] at hz
  exact neg_ne_zero.2 one_ne_zero hz

lemma Green.uv_inv (x : ℝ) : ∃ c : ℂ, Acoc v E x *ᵥ uv G x = c • uv G (x + α) := by
  refine par_of_det2 (hG.uv_ne (x + α)) (det2_eq_zero_of' (B := 4 * C * C) (fun ε hε => ?_))
  obtain ⟨M, hM⟩ := hG.zv_small (x + α) hε
  refine ⟨zv G M x, zv G (M + 1) (x + α), ?_, hG.zv_bdd _ _, hM (M + 1) (by omega)⟩
  have h1 := hG.zv_uv M x
  have h2 := hG.zv_uv (M + 1) (x + α)
  have e : x + α - ((M + 1 : ℕ) : ℝ) * α = x - M * α := by push_cast; ring
  rw [e] at h2
  have h3 : Acoc v E x *ᵥ uv G x = iter α (Acoc v E) (M + 1) (x - M * α) *ᵥ zv G M x := by
    rw [← h1, mulVec_mulVec, iter, sub_add_cancel]
  rw [h3, ← h2, det2_iter]

lemma Green.uv_iter_inv (m : ℕ) (x : ℝ) :
    ∃ c : ℂ, iter α (Acoc v E) m x *ᵥ uv G x = c • uv G (x + m * α) := by
  induction m with
  | zero => exact ⟨1, by simp [iter]⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := hG.uv_inv (x + m * α)
    refine ⟨c * c', ?_⟩
    rw [iter, ← mulVec_mulVec, hc, mulVec_smul, hc', smul_smul,
      show x + (m : ℝ) * α + α = x + ((m + 1 : ℕ) : ℝ) * α by push_cast; ring]

lemma Green.uv_cont : Continuous (uv G) :=
  continuous_sec (hG.cont_Φ 0 0) (hG.cont_Φ 1 0)

lemma Green.uv_per : Function.Periodic (uv G) 1 := fun x => by
  simp only [uv, hG.per]

lemma Green.zv_sum (N : ℕ) (x : ℝ) :
    ∑ m ∈ Finset.range N, ‖zv G m x‖ ^ 2 ≤ 64 * C ^ 4 :=
  comb_sum_le _ _ _ _ (hG.norm_le x 0) (hG.norm_le x 1) (hG.pc_le x 0 0)
    (hG.pc_le x 1 0) (f := fun m : ℕ => -(m : ℤ)) (fun a b h => by simp only at h; omega) N

lemma Green.zv_mul {c : ℝ} (hc : ∀ x, c ≤ ‖uv G x‖) (x : ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∃ x', c * ‖zv G n x‖ ≤ ‖zv G m x‖ * ‖zv G (n - m) x'‖ := by
  set x' := x - m * α
  refine ⟨x', ?_⟩
  -- `z_m(x)` is parallel to `u(x')`
  have hpar : det2 (zv G m x) (uv G x') = 0 := by
    refine det2_eq_zero_of (B := 4 * C * C) (fun ε hε => ?_)
    obtain ⟨M, hM⟩ := hG.zv_small x hε
    refine ⟨zv G (m + M) x, zv G M x', ?_, hM (m + M) (by omega), hG.zv_bdd _ _⟩
    have h1 := hG.zv_bwd (Nat.le_add_right m M) x
    have h2 := hG.zv_uv M x'
    have e1 : m + M - m = M := by omega
    have e2 : x - ((m + M : ℕ) : ℝ) * α = x' - M * α := by simp only [x']; push_cast; ring
    rw [e1, e2] at h1
    rw [← h1, ← h2, det2_iter]
  obtain ⟨κ, hκ⟩ := par_of_det2 (hG.uv_ne x') hpar
  have hn : zv G n x = κ • zv G (n - m) x' := by
    apply iter_injective (m := n - m) (y := x - n * α) (α := α) (v := v) (E := E)
    rw [hG.zv_bwd hmn x, mulVec_smul, hκ]
    have h2 := hG.zv_uv (n - m) x'
    have e : x' - ((n - m : ℕ) : ℝ) * α = x - n * α := by
      simp only [x']; push_cast [hmn]; ring
    rw [e] at h2
    rw [h2]
  rw [hn, hκ, norm_smul, norm_smul]
  set a := ‖zv G (n - m) x'‖
  calc c * (‖κ‖ * a) = (‖κ‖ * a) * c := by ring
    _ ≤ (‖κ‖ * a) * ‖uv G x'‖ :=
        mul_le_mul_of_nonneg_left (hc _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖κ‖ * ‖uv G x'‖ * a := by ring

/-- **Green data give uniform hyperbolicity.** -/
theorem Green.isUH : IsUH α (Acoc v E) := by
  obtain ⟨xs, hxs⟩ := periodic_exists_min hG.sv_cont.norm (fun x => by
    simp only [hG.sv_per x])
  obtain ⟨xu, hxu⟩ := periodic_exists_min hG.uv_cont.norm (fun x => by
    simp only [hG.uv_per x])
  have hcs : 0 < ‖sv G xs‖ := norm_pos_iff.2 (hG.sv_ne xs)
  have hcu : 0 < ‖uv G xu‖ := norm_pos_iff.2 (hG.uv_ne xu)
  obtain ⟨Ns, hNs⟩ := exists_n_of_sq_sum
    (g := fun m x => ‖iter α (Acoc v E) m x *ᵥ sv G x‖) hcs hG.sv_sum
    (fun x m n hmn => hG.sv_mul hxs x m n hmn)
  obtain ⟨Nu, hNu⟩ := exists_n_of_sq_sum
    (g := fun m x => ‖zv G m x‖) hcu hG.zv_sum
    (fun x m n hmn => hG.zv_mul hxu x m n hmn)
  set n := max (max Ns Nu) 1
  refine ⟨uv G, sv G, hG.uv_cont, hG.sv_cont, hG.uv_per, hG.sv_per, hG.uv_ne, hG.sv_ne,
    hG.uv_inv, hG.sv_inv, n, le_max_right _ _, fun x => ⟨?_, ?_⟩⟩
  · exact (hNs n (by omega) x).trans_le (hxs x)
  · obtain ⟨μ, hμ⟩ := hG.uv_iter_inv n x
    have h1 := hG.zv_uv n (x + n * α)
    rw [add_sub_cancel_right] at h1
    have h2 : uv G x = μ • zv G n (x + n * α) :=
      iter_injective (m := n) (y := x) (α := α) (v := v) (E := E)
        (by rw [mulVec_smul, h1, hμ])
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hG.uv_ne x (by rw [h2, zero_smul])
    rw [hμ, h2, norm_smul, norm_smul]
    have h3 : ‖zv G n (x + n * α)‖ < ‖uv G xu‖ := hNu n (by omega) (x + n * α)
    exact mul_lt_mul_of_pos_left (h3.trans_le (hxu _)) (norm_pos_iff.2 hμ0)

end GreenUH


/-! ### The operator `H_x - E` -/

/-- `H_x - E`. -/
def Lop (α : ℝ) (v : ℂ → ℂ) (E : ℝ) (x : ℝ) : L2 ℤ →L[ℂ] L2 ℤ :=
  schrOp α v x - algebraMap ℂ (L2 ℤ →L[ℂ] L2 ℤ) (E : ℂ)

section Pot
variable {δ : ℝ} {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v)
include hv

lemma IsRealAnalyticPotential.continuous_real : Continuous (fun t : ℝ => v t) :=
  hv.holo.continuousOn.comp_continuous continuous_ofReal (fun t => by simp [strip, hv.pos])

lemma IsRealAnalyticPotential.periodic_real : Function.Periodic (fun t : ℝ => v t) 1 := by
  intro t; simp [hv.periodic]

lemma IsRealAnalyticPotential.periodic_int (z : ℂ) (m : ℤ) : v (z + m) = v z := by
  have hp : Function.Periodic v 1 := hv.periodic
  simpa using (hp.int_mul m) z

lemma IsRealAnalyticPotential.bdd : ∃ M, ∀ t : ℝ, ‖v t‖ ≤ M := by
  obtain ⟨x₀, h⟩ := periodic_exists_max hv.continuous_real.norm
    (fun t => congrArg norm (hv.periodic_real t))
  exact ⟨_, h⟩

lemma IsRealAnalyticPotential.jacobiBdd (α x : ℝ) : JacobiBdd α (fun _ => 1) v x := by
  obtain ⟨M, hM⟩ := hv.bdd
  exact ⟨⟨1, fun _ => by simp⟩, ⟨M, fun n => hM _⟩⟩

lemma Lop_apply (α E x : ℝ) (u : L2 ℤ) (n : ℤ) :
    Lop α v E x u n = u (n + 1) + u (n - 1) + (v ((x + n * α : ℝ) : ℂ) - E) * u n := by
  simp only [Lop, _root_.sub_apply, lp.coeFn_sub, Pi.sub_apply, schrOp,
    jacobi_apply (hv.jacobiBdd α x), Algebra.algebraMap_eq_smul_one,
    _root_.smul_apply, one_apply_eq_self, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, map_one]
  ring

lemma isSelfAdjoint_Lop (α E x : ℝ) : IsSelfAdjoint (Lop α v E x) := by
  have h1 := isSelfAdjoint_jacobi (hv.jacobiBdd α x)
    (fun t => Complex.conj_eq_iff_im.2 (hv.real t))
  have h2 : IsSelfAdjoint (algebraMap ℂ (L2 ℤ →L[ℂ] L2 ℤ) (E : ℂ)) :=
    IsSelfAdjoint.algebraMap _ (by simp [IsSelfAdjoint])
  unfold IsSelfAdjoint at h1 h2 ⊢
  unfold Lop schrOp
  first
  | rw [star_sub, h1, h2]
  | (simp only [star_sub, h1, h2])
  | exact (star_sub _ _).trans (congrArg₂ (· - ·) h1 h2)
  | (rw [ContinuousLinearMap.star_eq_adjoint] at h1 h2 ⊢; rw [map_sub, h1, h2])

end Pot

lemma isUnit_of_selfAdjoint_bddBelow {T : L2 ℤ →L[ℂ] L2 ℤ} (hT : IsSelfAdjoint T) {C : NNReal}
    (hC : ∀ u, ‖u‖ ≤ C * ‖T u‖) : IsUnit T := by
  rw [ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz]
  refine ⟨?_, ⟨C, T.antilipschitz_of_bound hC⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
    hT.adjoint_eq, Submodule.eq_bot_iff]
  intro x hx
  have := hC x
  rw [LinearMap.mem_ker] at hx
  simp only [ContinuousLinearMap.coe_coe] at hx
  rw [hx, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this


/-! ### Operator side: from `E ∉ Σ` to Green data -/

/-- The shift `(S_k u)_n = u_{n+k}`. -/
def Sh (k : ℤ) : L2 ℤ →L[ℂ] L2 ℤ := weightedShift (fun _ => (1 : ℂ)) (Equiv.addRight k)

lemma Sh_apply (k : ℤ) (u : L2 ℤ) (n : ℤ) : Sh k u n = u (n + k) := by
  simp [Sh, weightedShift_apply (bdd_of_norm_eq_one (fun _ : ℤ => norm_one))]

lemma norm_Sh (k : ℤ) (u : L2 ℤ) : ‖Sh k u‖ = ‖u‖ := by
  have h : ‖Sh k u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [L2.norm_sq_eq_tsum, L2.norm_sq_eq_tsum]
    simp only [Sh_apply]
    exact (Equiv.addRight k).tsum_eq (fun n => ‖u n‖ ^ 2)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma bdd_of_isUnit {T : L2 ℤ →L[ℂ] L2 ℤ} (h : IsUnit T) : ∃ C > 0, ∀ u, ‖u‖ ≤ C * ‖T u‖ := by
  obtain ⟨U, rfl⟩ := h
  refine ⟨‖(↑U⁻¹ : L2 ℤ →L[ℂ] L2 ℤ)‖ + 1, by positivity, fun u => ?_⟩
  have h1 : (↑U⁻¹ : L2 ℤ →L[ℂ] L2 ℤ) ((↑U : L2 ℤ →L[ℂ] L2 ℤ) u) = u := by
    rw [← ContinuousLinearMap.mul_apply, U.inv_mul]; rfl
  calc ‖u‖ = ‖(↑U⁻¹ : L2 ℤ →L[ℂ] L2 ℤ) ((↑U : L2 ℤ →L[ℂ] L2 ℤ) u)‖ := by rw [h1]
    _ ≤ ‖(↑U⁻¹ : L2 ℤ →L[ℂ] L2 ℤ)‖ * ‖(↑U : L2 ℤ →L[ℂ] L2 ℤ) u‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by gcongr; linarith

section OpSide
variable {δ : ℝ} {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) {α : ℝ} {E : ℝ}
include hv

lemma Lop_add_int (x : ℝ) (m : ℤ) : Lop α v E (x + m) = Lop α v E x := by
  ext u n
  rw [Lop_apply hv, Lop_apply hv]
  have : ((x + m + n * α : ℝ) : ℂ) = ((x + n * α : ℝ) : ℂ) + (m : ℂ) := by push_cast; ring
  rw [this, hv.periodic_int]

lemma Lop_cov (x : ℝ) (k : ℤ) (u : L2 ℤ) :
    Lop α v E (x + k * α) u = Sh k (Lop α v E x (Sh (-k) u)) := by
  ext n
  rw [Sh_apply, Lop_apply hv, Lop_apply hv, Sh_apply, Sh_apply, Sh_apply]
  have e1 : n + k + 1 + -k = n + 1 := by ring
  have e2 : n + k - 1 + -k = n - 1 := by ring
  have e3 : n + k + -k = n := by ring
  have e4 : ((x + ((n + k : ℤ) : ℝ) * α : ℝ) : ℂ) = ((x + k * α + n * α : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1, e2, e3, e4]

lemma norm_Lop_sub_le (x y ε : ℝ) (hε : 0 ≤ ε) (h : ∀ n : ℤ,
    ‖v ((x + n * α : ℝ) : ℂ) - v ((y + n * α : ℝ) : ℂ)‖ ≤ ε) (u : L2 ℤ) :
    ‖Lop α v E x u - Lop α v E y u‖ ≤ ε * ‖u‖ := by
  have hb : Bdd (fun n : ℤ => v ((x + n * α : ℝ) : ℂ) - v ((y + n * α : ℝ) : ℂ)) := ⟨ε, h⟩
  have e : Lop α v E x u - Lop α v E y u =
      weightedShift (fun n : ℤ => v ((x + n * α : ℝ) : ℂ) - v ((y + n * α : ℝ) : ℂ))
        (Equiv.refl ℤ) u := by
    ext n
    rw [lp.coeFn_sub, Pi.sub_apply, Lop_apply hv, Lop_apply hv, weightedShift_apply hb]
    simp only [Equiv.refl_apply]
    ring
  rw [e]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_weightedShift_le hε h) (norm_nonneg _))

lemma Lop_star (x : ℝ) (w : L2 ℤ) (m : ℤ) :
    Lop α v E x (star w) m = star (Lop α v E x w m) := by
  have hreal : ∀ t : ℝ, (starRingEnd ℂ) (v t) = v t := fun t =>
    Complex.conj_eq_iff_im.2 (hv.real t)
  rw [Lop_apply hv, Lop_apply hv]
  simp only [lp.star_apply, star_add, star_mul', star_sub, Complex.star_def,
    Complex.conj_ofReal, hreal]

/-- Uniform lower bound for `H_x - E` over all phases, for irrational `α`. -/
lemma bdd_all (hα : Irrational α) (h0 : IsUnit (Lop α v E 0)) :
    ∃ C > 0, ∀ x u, ‖u‖ ≤ C * ‖Lop α v E x u‖ := by
  obtain ⟨C0, hC0, hb⟩ := bdd_of_isUnit h0
  have horb : ∀ (k m : ℤ) (u : L2 ℤ), ‖u‖ ≤ C0 * ‖Lop α v E (k * α + m) u‖ := by
    intro k m u
    rw [Lop_add_int hv, show (k : ℝ) * α = 0 + k * α by ring, Lop_cov hv, norm_Sh]
    calc ‖u‖ = ‖Sh (-k) u‖ := (norm_Sh _ _).symm
      _ ≤ _ := hb _
  refine ⟨2 * C0, by positivity, fun x u => ?_⟩
  obtain ⟨d, hd, hcont⟩ := periodic_uniform hv.continuous_real hv.periodic_real
    (ε := 1 / (2 * C0)) (by positivity)
  have hdense : Dense (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.2 (by simpa using hα)
  obtain ⟨y, hy, hxy⟩ := hdense.exists_dist_lt x hd
  obtain ⟨k, m, rfl⟩ := AddSubgroup.mem_closure_pair.1 hy
  have hdiff := norm_Lop_sub_le hv (α := α) (E := E) x (k • α + m • (1 : ℝ)) (1 / (2 * C0))
    (by positivity) (fun n => (hcont _ _ (by
      rw [Real.dist_eq] at hxy
      convert hxy using 2; ring)).le) u
  have h1 := horb k m u
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hdiff
  have h2 : ‖Lop α v E (k * α + m) u‖ ≤ ‖Lop α v E x u‖ + 1 / (2 * C0) * ‖u‖ := by
    have := norm_sub_norm_le (Lop α v E (k * α + m) u) (Lop α v E x u)
    rw [norm_sub_rev] at hdiff
    linarith
  have h3 : C0 * (1 / (2 * C0) * ‖u‖) = ‖u‖ / 2 := by field_simp
  nlinarith

lemma isUnit_all (hα : Irrational α) (h0 : IsUnit (Lop α v E 0)) (x : ℝ) :
    IsUnit (Lop α v E x) := by
  obtain ⟨C, hC, hb⟩ := bdd_all hv hα h0
  exact isUnit_of_selfAdjoint_bddBelow (isSelfAdjoint_Lop hv α E x) (C := ⟨C, hC.le⟩)
    (fun u => hb x u)

/-- The Green data `G x j = (H_x - E)⁻¹ δ_j`. -/
def greenFun (α : ℝ) (v : ℂ → ℂ) (E x : ℝ) (j : ℤ) : L2 ℤ :=
  Ring.inverse (Lop α v E x) (lp.single 2 j (1 : ℂ))

omit hv in
lemma Lop_greenFun {x : ℝ} (hx : IsUnit (Lop α v E x)) (j : ℤ) :
    Lop α v E x (greenFun α v E x j) = lp.single 2 j (1 : ℂ) := by
  unfold greenFun
  rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hx]
  rfl

theorem green_of_isUnit (hα : Irrational α) (h0 : IsUnit (Lop α v E 0)) :
    ∃ C, Green α v E C (greenFun α v E) := by
  obtain ⟨C, hC, hb⟩ := bdd_all hv hα h0
  have hu := isUnit_all hv hα h0
  have hδ : ∀ j : ℤ, ‖(lp.single 2 j (1 : ℂ) : L2 ℤ)‖ = 1 := fun j => by
    rw [lp.norm_single (by norm_num)]; simp
  have hnorm : ∀ x j, ‖greenFun α v E x j‖ ≤ C := fun x j => by
    have := hb x (greenFun α v E x j)
    rwa [Lop_greenFun (hu x), hδ, mul_one] at this
  refine ⟨C, ⟨fun x j n => ?_, hnorm, fun x j n => ?_, fun j n => ?_, fun x j => ?_⟩⟩
  · -- the equation
    have := congrArg (fun w : L2 ℤ => w n) (Lop_greenFun (hu x) j)
    simp only at this
    rw [Lop_apply hv, lp.single_apply, Pi.single_apply] at this
    exact this
  · -- realness
    set g := greenFun α v E x j
    have hst : Lop α v E x (star g) = lp.single 2 j (1 : ℂ) := by
      ext m
      rw [Lop_star hv, Lop_greenFun (hu x)]
      by_cases hm : m = j
      · subst hm; simp
      · simp [hm]
    have h0' : star g = g := by
      have := hb x (star g - g)
      rw [map_sub, hst, Lop_greenFun (hu x), sub_self, norm_zero, mul_zero] at this
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    have := congrArg (fun w : L2 ℤ => w n) h0'
    simp only [lp.star_apply] at this
    exact Complex.conj_eq_iff_im.1 this
  · -- continuity
    rw [Metric.continuous_iff]
    intro y ε hε
    obtain ⟨d, hd, hcont⟩ := periodic_uniform hv.continuous_real hv.periodic_real
      (ε := ε / (C * C + 1)) (by positivity)
    refine ⟨d, hd, fun x hxy => ?_⟩
    have hdiff := norm_Lop_sub_le hv (E := E) (α := α) y x (ε / (C * C + 1)) (by positivity)
      (fun n => (hcont _ _ (by
        rw [Real.dist_eq] at hxy
        rw [abs_sub_comm] at hxy
        convert hxy using 2; ring)).le) (greenFun α v E x j)
    have key : ‖greenFun α v E x j - greenFun α v E y j‖ ≤
        C * (ε / (C * C + 1) * C) := by
      have h1 := hb y (greenFun α v E x j - greenFun α v E y j)
      rw [map_sub, Lop_greenFun (hu y), ← Lop_greenFun (hu x) j] at h1
      refine h1.trans ?_
      gcongr
      exact hdiff.trans (by gcongr; exact hnorm x j)
    rw [dist_eq_norm]
    calc ‖greenFun α v E x j n - greenFun α v E y j n‖
        = ‖(greenFun α v E x j - greenFun α v E y j) n‖ := by rw [lp.coeFn_sub, Pi.sub_apply]
      _ ≤ ‖greenFun α v E x j - greenFun α v E y j‖ := L2_norm_apply_le _ _
      _ ≤ C * (ε / (C * C + 1) * C) := key
      _ < ε := by
        rw [show C * (ε / (C * C + 1) * C) = ε * (C * C / (C * C + 1)) by ring]
        exact mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).2 (by linarith))
  · -- periodicity
    have : Lop α v E (x + 1) = Lop α v E x := by
      simpa using Lop_add_int hv (α := α) (E := E) x 1
    simp only [greenFun, this]

end OpSide

lemma not_mem_Sigma_iff {α : ℝ} {v : ℂ → ℂ} {E : ℝ} :
    E ∉ Sigma α v ↔ IsUnit (Lop α v E 0) := by
  simp only [Sigma, Set.mem_setOf_eq, spectrum.mem_iff, not_not, Lop]
  rw [← IsUnit.neg_iff, neg_sub]

/-! ### Uniform hyperbolicity implies `E ∉ Σ` -/

lemma det2_add_left (a b c : Fin 2 → ℂ) : det2 (a + b) c = det2 a c + det2 b c := by
  simp [det2]; ring
lemma det2_add_right (a b c : Fin 2 → ℂ) : det2 a (b + c) = det2 a b + det2 a c := by
  simp [det2]; ring
lemma det2_smul_left (r : ℂ) (a b : Fin 2 → ℂ) : det2 (r • a) b = r * det2 a b := by
  simp [det2]; ring
lemma det2_smul_right (r : ℂ) (a b : Fin 2 → ℂ) : det2 a (r • b) = r * det2 a b := by
  simp [det2]; ring

lemma jensen_sq {y a b θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : 0 ≤ y) (h : y ≤ θ * a + b) : y ^ 2 ≤ θ * a ^ 2 + b ^ 2 / (1 - θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hne : 1 - θ ≠ 0 := h1θ.ne'
  have h2 : y ^ 2 ≤ (θ * a + b) ^ 2 := pow_le_pow_left₀ hy h 2
  have e : (θ * a ^ 2 + b ^ 2 / (1 - θ)) * (1 - θ) = θ * a ^ 2 * (1 - θ) + b ^ 2 := by
    field_simp
  have h3 : (θ * a + b) ^ 2 * (1 - θ) ≤ (θ * a ^ 2 + b ^ 2 / (1 - θ)) * (1 - θ) := by
    rw [e]; nlinarith [mul_nonneg hθ0 (sq_nonneg ((1 - θ) * a - b))]
  have h4 := le_of_mul_le_mul_right h3 h1θ
  linarith

set_option maxHeartbeats 1000000 in
lemma tsum_sq_le_of_contract {p ρ : ℤ → ℝ} {θ : ℝ} (a b : ℤ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hp0 : ∀ k, 0 ≤ p k) (hρ0 : ∀ k, 0 ≤ ρ k)
    (hps : Summable fun k => p k ^ 2) (hρs : Summable fun k => ρ k ^ 2)
    (h : ∀ k, p (k + a) ≤ θ * p (k + b) + ρ k) :
    ∑' k, p k ^ 2 ≤ (∑' k, ρ k ^ 2) / (1 - θ) ^ 2 := by
  have hj : ∀ k, p (k + a) ^ 2 ≤ θ * p (k + b) ^ 2 + ρ k ^ 2 / (1 - θ) := fun k =>
    jensen_sq hθ0 hθ1 (hp0 _) (hρ0 _) (hp0 _) (h k)
  have e1 : ∑' k, p (k + a) ^ 2 = ∑' k, p k ^ 2 := (Equiv.addRight a).tsum_eq (fun k => p k ^ 2)
  have e2 : ∑' k, p (k + b) ^ 2 = ∑' k, p k ^ 2 := (Equiv.addRight b).tsum_eq (fun k => p k ^ 2)
  have hsa : Summable fun k => p (k + a) ^ 2 :=
    (Equiv.addRight a).summable_iff.2 hps
  have hsb : Summable fun k => p (k + b) ^ 2 :=
    (Equiv.addRight b).summable_iff.2 hps
  have h1 : ∑' k, p (k + a) ^ 2 ≤ ∑' k, (θ * p (k + b) ^ 2 + ρ k ^ 2 / (1 - θ)) :=
    hsa.tsum_le_tsum hj ((hsb.mul_left θ).add (hρs.div_const _))
  rw [(hsb.mul_left θ).tsum_add (hρs.div_const _), tsum_mul_left, tsum_div_const, e1, e2] at h1
  have h1θ : 0 < 1 - θ := by linarith
  rw [le_div_iff₀ (pow_pos h1θ 2)]
  have h2 : (1 - θ) * ∑' k, p k ^ 2 ≤ (∑' k, ρ k ^ 2) / (1 - θ) := by linarith
  calc (∑' k, p k ^ 2) * (1 - θ) ^ 2 = ((1 - θ) * ∑' k, p k ^ 2) * (1 - θ) := by ring
    _ ≤ (∑' k, ρ k ^ 2) / (1 - θ) * (1 - θ) := mul_le_mul_of_nonneg_right h2 h1θ.le
    _ = _ := by field_simp

lemma aux_I2 {a b c θ K : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hK : 0 ≤ K) (h1 : a ≤ θ * b)
    (h2 : b ≤ c + K) : a ≤ θ * c + K := by nlinarith

section Back
variable {δ : ℝ} {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) {α : ℝ} {E : ℝ}
include hv

lemma step_inhom (x : ℝ) (χ : L2 ℤ) (j : ℤ) :
    Φ χ (j + 1) = Acoc v E (x + j * α) *ᵥ Φ χ j + ![Lop α v E x χ j, 0] := by
  rw [Lop_apply hv]
  simp only [Φ]
  rw [Acoc_mulVec]
  ext i; fin_cases i <;> simp <;> ring

lemma iter_inhom (x : ℝ) (χ : L2 ℤ) {B : ℝ} (hB : 1 ≤ B) (hAB : ∀ t, ‖Acoc v E t‖ ≤ B)
    (k : ℤ) (m : ℕ) :
    ‖Φ χ (k + m) - iter α (Acoc v E) m (x + k * α) *ᵥ Φ χ k‖ ≤
      B ^ m * ∑ i ∈ Finset.range m, ‖Lop α v E x χ (k + i)‖ := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    have hs := step_inhom hv (α := α) (E := E) x χ (k + m)
    have hph : x + (k:ℝ) * α + (m:ℝ) * α = x + ((k + m : ℤ) : ℝ) * α := by push_cast; ring
    have e : Φ χ (k + ((m + 1 : ℕ) : ℤ)) - iter α (Acoc v E) (m + 1) (x + k * α) *ᵥ Φ χ k =
        Acoc v E (x + ((k + m : ℤ) : ℝ) * α) *ᵥ
          (Φ χ (k + m) - iter α (Acoc v E) m (x + k * α) *ᵥ Φ χ k)
          + ![Lop α v E x χ (k + m), 0] := by
      rw [show k + ((m + 1 : ℕ) : ℤ) = k + m + 1 by push_cast; ring, hs, iter, hph,
        ← mulVec_mulVec, mulVec_sub]
      abel
    rw [e, Finset.sum_range_succ]
    have h1 : ‖Acoc v E (x + ((k + m : ℤ) : ℝ) * α) *ᵥ
          (Φ χ (k + m) - iter α (Acoc v E) m (x + k * α) *ᵥ Φ χ k)‖ ≤
        B * (B ^ m * ∑ i ∈ Finset.range m, ‖Lop α v E x χ (k + i)‖) :=
      (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul (hAB _) ih (norm_nonneg _) (by linarith))
    have h2 : ‖(![Lop α v E x χ (k + m), 0] : Fin 2 → ℂ)‖ ≤ ‖Lop α v E x χ (k + m)‖ := by
      simpa using norm_vec2_le (![Lop α v E x χ (k + m), 0] : Fin 2 → ℂ)
    have hBm : 1 ≤ B ^ m * B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) hB
    have hT : ‖Lop α v E x χ (k + m)‖ ≤ B ^ m * B * ‖Lop α v E x χ (k + m)‖ :=
      le_mul_of_one_le_left (norm_nonneg _) hBm
    refine (norm_add_le _ _).trans ((add_le_add h1 (h2.trans hT)).trans (le_of_eq ?_))
    rw [pow_succ]; ring

set_option maxHeartbeats 2000000 in
/-- An exponential dichotomy along the orbit gives a lower bound for `H_x - E`. -/
lemma bdd_of_dichotomy {x : ℝ} {n : ℕ} {θ KP B : ℝ}
    {Ps Pu : ℝ → (Fin 2 → ℂ) → (Fin 2 → ℂ)}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hKP : 0 ≤ KP) (hB : 1 ≤ B) (hAB : ∀ t, ‖Acoc v E t‖ ≤ B)
    (hsplit : ∀ y w, w = Ps y w + Pu y w)
    (hPs_add : ∀ y a b, Ps y (a + b) = Ps y a + Ps y b)
    (hPu_add : ∀ y a b, Pu y (a + b) = Pu y a + Pu y b)
    (hPs : ∀ y w, ‖Ps y w‖ ≤ KP * ‖w‖) (hPu : ∀ y w, ‖Pu y w‖ ≤ KP * ‖w‖)
    (hcs : ∀ y w, ‖Ps (y + n * α) (iter α (Acoc v E) n y *ᵥ w)‖ ≤ θ * ‖Ps y w‖)
    (hcu : ∀ y w, ‖Pu y w‖ ≤ θ * ‖Pu (y + n * α) (iter α (Acoc v E) n y *ᵥ w)‖)
    (χ : L2 ℤ) :
    ‖χ‖ ≤ (2 * KP * B ^ n * n / (1 - θ)) * ‖Lop α v E x χ‖ := by
  set f := Lop α v E x χ with hf
  set ρ : ℤ → ℝ := fun k => B ^ n * ∑ i ∈ Finset.range n, ‖f (k + i)‖ with hρ
  set R : ℤ → Fin 2 → ℂ := fun k => Φ χ (k + n) - iter α (Acoc v E) n (x + k * α) *ᵥ Φ χ k
  set p : ℤ → ℝ := fun k => ‖Ps (x + k * α) (Φ χ k)‖ with hp
  set q : ℤ → ℝ := fun k => ‖Pu (x + k * α) (Φ χ k)‖ with hq
  have hR : ∀ k, ‖R k‖ ≤ ρ k := fun k => iter_inhom hv x χ hB hAB k n
  have hRe : ∀ k, Φ χ (k + n) = iter α (Acoc v E) n (x + k * α) *ᵥ Φ χ k + R k := fun k => by
    simp only [R]; abel
  have hph : ∀ k : ℤ, x + ((k + n : ℤ) : ℝ) * α = x + k * α + n * α := by
    intro k; push_cast; ring
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => by
    simp only [hρ]; exact mul_nonneg (pow_nonneg (zero_le_one.trans hB) n) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have I1 : ∀ k, p (k + n) ≤ θ * p (k + 0) + KP * ρ k := by
    intro k
    simp only [hp, add_zero]
    rw [hph, hRe, hPs_add]
    calc _ ≤ ‖Ps (x + k * α + n * α) (iter α (Acoc v E) n (x + k * α) *ᵥ Φ χ k)‖ +
          ‖Ps (x + k * α + n * α) (R k)‖ := norm_add_le _ _
      _ ≤ θ * ‖Ps (x + k * α) (Φ χ k)‖ + KP * ρ k :=
          add_le_add (hcs _ _) ((hPs _ _).trans (mul_le_mul_of_nonneg_left (hR k) hKP))
  have I2 : ∀ k, q (k + 0) ≤ θ * q (k + n) + KP * ρ k := by
    intro k
    simp only [hq, add_zero]
    rw [hph, hRe, hPu_add]
    refine aux_I2 hθ0 hθ1.le (mul_nonneg hKP (hρ0 k)) (hcu (x + k * α) (Φ χ k)) ?_
    have h3 := norm_sub_le
      (Pu (x + ↑k * α + ↑n * α) (iter α (Acoc v E) n (x + ↑k * α) *ᵥ Φ χ k) +
        Pu (x + ↑k * α + ↑n * α) (R k)) (Pu (x + ↑k * α + ↑n * α) (R k))
    rw [add_sub_cancel_right] at h3
    have h4 := (hPu (x + ↑k * α + ↑n * α) (R k)).trans (mul_le_mul_of_nonneg_left (hR k) hKP)
    linarith
  -- summability
  have hχs : Summable fun k => ‖χ k‖ ^ 2 := L2.summable_norm_sq χ
  have hχs' : Summable fun k => ‖χ (k - 1)‖ ^ 2 := (Equiv.subRight (1 : ℤ)).summable_iff.2 hχs
  have hΦ : ∀ k, ‖Φ χ k‖ ^ 2 ≤ 2 * (‖χ k‖ ^ 2 + ‖χ (k - 1)‖ ^ 2) := fun k => by
    have h1 : ‖Φ χ k‖ ≤ ‖χ k‖ + ‖χ (k - 1)‖ := by simpa [Φ] using norm_vec2_le (Φ χ k)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖χ k‖ - ‖χ (k - 1)‖)]
  have hsumΦ : Summable fun k => 2 * (‖χ k‖ ^ 2 + ‖χ (k - 1)‖ ^ 2) := (hχs.add hχs').mul_left 2
  have hps : Summable fun k => p k ^ 2 := by
    refine (hsumΦ.mul_left (KP ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_)
    have h1 : p k ≤ KP * ‖Φ χ k‖ := hPs _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc p k ^ 2 ≤ (KP * ‖Φ χ k‖) ^ 2 := h2
      _ = KP ^ 2 * ‖Φ χ k‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hΦ k) (sq_nonneg _)
  have hqs : Summable fun k => q k ^ 2 := by
    refine (hsumΦ.mul_left (KP ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_)
    have h1 : q k ≤ KP * ‖Φ χ k‖ := hPu _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc q k ^ 2 ≤ (KP * ‖Φ χ k‖) ^ 2 := h2
      _ = KP ^ 2 * ‖Φ χ k‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hΦ k) (sq_nonneg _)
  have hfs : Summable fun k => ‖f k‖ ^ 2 := L2.summable_norm_sq f
  have hfsh : ∀ i : ℕ, Summable fun k => ‖f (k + i)‖ ^ 2 := fun i =>
    (Equiv.addRight (i : ℤ)).summable_iff.2 hfs
  have hρsq : ∀ k, ρ k ^ 2 ≤ B ^ (2 * n) * n * ∑ i ∈ Finset.range n, ‖f (k + i)‖ ^ 2 := by
    intro k
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := fun i => ‖f (k + i)‖)
    rw [Finset.card_range] at h1
    simp only [hρ]
    rw [mul_pow, ← pow_mul, mul_comm n 2, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (zero_le_one.trans hB) _)
  have hsum_sh : Summable fun k => ∑ i ∈ Finset.range n, ‖f (k + i)‖ ^ 2 :=
    summable_sum (fun i _ => hfsh i)
  have hρs : Summable fun k => ρ k ^ 2 :=
    (hsum_sh.mul_left (B ^ (2 * n) * n)).of_nonneg_of_le (fun _ => sq_nonneg _) hρsq
  have hKρs : Summable fun k => (KP * ρ k) ^ 2 := by
    simpa [mul_pow] using hρs.mul_left (KP ^ 2)
  have hRsum : ∑' k, ρ k ^ 2 ≤ B ^ (2 * n) * n * (n * ‖f‖ ^ 2) := by
    calc ∑' k, ρ k ^ 2 ≤ ∑' k, B ^ (2 * n) * n * ∑ i ∈ Finset.range n, ‖f (k + i)‖ ^ 2 :=
          hρs.tsum_le_tsum hρsq (hsum_sh.mul_left _)
      _ = B ^ (2 * n) * n * (n * ‖f‖ ^ 2) := by
          rw [tsum_mul_left, Summable.tsum_finsetSum (fun i _ => hfsh i)]
          congr 1
          have : ∀ i ∈ Finset.range n, ∑' k, ‖f (k + i)‖ ^ 2 = ‖f‖ ^ 2 := fun i _ => by
            rw [L2.norm_sq_eq_tsum]
            exact (Equiv.addRight (i : ℤ)).tsum_eq (fun k => ‖f k‖ ^ 2)
          rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hP := tsum_sq_le_of_contract (p := p) (ρ := fun k => KP * ρ k) n 0 hθ0 hθ1
    (fun _ => norm_nonneg _) (fun k => mul_nonneg hKP (hρ0 k)) hps hKρs I1
  have hQ := tsum_sq_le_of_contract (p := q) (ρ := fun k => KP * ρ k) 0 n hθ0 hθ1
    (fun _ => norm_nonneg _) (fun k => mul_nonneg hKP (hρ0 k)) hqs hKρs I2
  have hKR : ∑' k, (KP * ρ k) ^ 2 = KP ^ 2 * ∑' k, ρ k ^ 2 := by
    rw [← tsum_mul_left]; congr 1; funext k; ring
  -- pointwise bound for `χ`
  have hpt : ∀ k, ‖χ k‖ ^ 2 ≤ 2 * (p k ^ 2 + q k ^ 2) := fun k => by
    have h1 : ‖χ k‖ ≤ ‖Φ χ k‖ := by simpa [Φ] using norm_le_pi_norm (Φ χ k) 0
    have h2 : ‖Φ χ k‖ ≤ p k + q k := by
      simp only [hp, hq]
      calc ‖Φ χ k‖ = ‖Ps (x + k * α) (Φ χ k) + Pu (x + k * α) (Φ χ k)‖ := by
            rw [← hsplit]
        _ ≤ _ := norm_add_le _ _
    have h3 := pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    nlinarith [sq_nonneg (p k - q k)]
  have hX : ‖χ‖ ^ 2 ≤ 2 * (∑' k, p k ^ 2 + ∑' k, q k ^ 2) := by
    rw [L2.norm_sq_eq_tsum, ← hps.tsum_add hqs, ← tsum_mul_left]
    exact hχs.tsum_le_tsum hpt ((hps.add hqs).mul_left 2)
  have h1θ : 0 < 1 - θ := by linarith
  have hBn : 0 ≤ B ^ n := pow_nonneg (zero_le_one.trans hB) n
  have hK0 : 0 ≤ 2 * KP * B ^ n * n / (1 - θ) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKP) hBn) (Nat.cast_nonneg n))
      h1θ.le
  set Sρ := ∑' k, ρ k ^ 2 with hSρ
  rw [hKR] at hP hQ
  have hfinal : ‖χ‖ ^ 2 ≤ ((2 * KP * B ^ n * n / (1 - θ)) * ‖f‖) ^ 2 := by
    calc ‖χ‖ ^ 2 ≤ 2 * (∑' k, p k ^ 2 + ∑' k, q k ^ 2) := hX
      _ ≤ 2 * (KP ^ 2 * Sρ / (1 - θ) ^ 2 + KP ^ 2 * Sρ / (1 - θ) ^ 2) := by linarith
      _ = 4 * KP ^ 2 / (1 - θ) ^ 2 * Sρ := by ring
      _ ≤ 4 * KP ^ 2 / (1 - θ) ^ 2 * (B ^ (2 * n) * n * (n * ‖f‖ ^ 2)) := by gcongr
      _ = ((2 * KP * B ^ n * n / (1 - θ)) * ‖f‖) ^ 2 := by
          field_simp; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _)) two_ne_zero).1
    hfinal

end Back

/-! ### The dichotomy data of a uniformly hyperbolic Schrödinger cocycle -/

lemma iter_inv_field {α : ℝ} {v : ℂ → ℂ} {E : ℝ} {w : ℝ → Fin 2 → ℂ}
    (hinv : ∀ x, ∃ c : ℂ, Acoc v E x *ᵥ w x = c • w (x + α)) (m : ℕ) (x : ℝ) :
    ∃ c : ℂ, iter α (Acoc v E) m x *ᵥ w x = c • w (x + m * α) := by
  induction m with
  | zero => exact ⟨1, by simp [iter]⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := hinv (x + m * α)
    refine ⟨c * c', ?_⟩
    rw [iter, ← mulVec_mulVec, hc, mulVec_smul, hc', smul_smul,
      show x + (m : ℝ) * α + α = x + ((m + 1 : ℕ) : ℝ) * α by push_cast; ring]

lemma proj_equiv {M : M2} (hM : M.det = 1) {s u s' u' w : Fin 2 → ℂ} {cs cu : ℂ}
    (hs : M *ᵥ s = cs • s') (hu : M *ᵥ u = cu • u') (hcs : cs ≠ 0) (hcu : cu ≠ 0)
    (hD : det2 s u ≠ 0) :
    (det2 (M *ᵥ w) u' / det2 s' u') • s' = M *ᵥ ((det2 w u / det2 s u) • s) ∧
    (det2 s' (M *ᵥ w) / det2 s' u') • u' = M *ᵥ ((det2 s w / det2 s u) • u) := by
  have es : s' = cs⁻¹ • (M *ᵥ s) := by rw [hs, smul_smul, inv_mul_cancel₀ hcs, one_smul]
  have eu : u' = cu⁻¹ • (M *ᵥ u) := by rw [hu, smul_smul, inv_mul_cancel₀ hcu, one_smul]
  have d1 : det2 (M *ᵥ w) u' = cu⁻¹ * det2 w u := by
    rw [eu, det2_smul_right, det2_mulVec, hM, one_mul]
  have d2 : det2 s' u' = cs⁻¹ * cu⁻¹ * det2 s u := by
    rw [es, eu, det2_smul_left, det2_smul_right, det2_mulVec, hM]; ring
  have d3 : det2 s' (M *ᵥ w) = cs⁻¹ * det2 s w := by
    rw [es, det2_smul_left, det2_mulVec, hM, one_mul]
  constructor
  · rw [d1, d2, mulVec_smul, es, smul_smul]
    congr 1
    field_simp
  · rw [d3, d2, mulVec_smul, eu, smul_smul]
    congr 1
    field_simp

section UHdata
variable {δ : ℝ} {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) {α : ℝ} {E : ℝ}
include hv

theorem isUnit_of_UH (hUH : IsUH α (Acoc v E)) : IsUnit (Lop α v E 0) := by
  obtain ⟨u, s, hu, hs, hup, hsp, hu0, hs0, huinv, hsinv, n, hn1, hn⟩ := hUH
  have hA : IsSLCocycle (Acoc v E) := (hv.schr E).isSLCocycle_shift (by simpa using hv.pos)
  have hit : Continuous (iter α (Acoc v E) n) := continuous_iter hA.continuous n
  have hitp : Function.Periodic (iter α (Acoc v E) n) 1 := iter_periodic hA.periodic n
  set M := iter α (Acoc v E) n with hMdef
  have hMs : Continuous fun y => M y *ᵥ s y := hit.matrix_mulVec hs
  have hMu : Continuous fun y => M y *ᵥ u y := hit.matrix_mulVec hu
  have hdetM : ∀ y, (M y).det = 1 := fun y => det_iter (fun t => det_Acoc t) n y
  -- independence of the two directions
  have hD : ∀ y, det2 (s y) (u y) ≠ 0 := by
    intro y hD0
    have h' : det2 (u y) (s y) = 0 := by
      rw [show det2 (u y) (s y) = -det2 (s y) (u y) by simp [det2]; ring, hD0, neg_zero]
    obtain ⟨c, hc⟩ := par_of_det2 (hs0 y) h'
    have h1 := (hn y).1
    have h2 := (hn y).2
    rw [hc, mulVec_smul, norm_smul, norm_smul] at h2
    have := mul_le_mul_of_nonneg_left h1.le (norm_nonneg c)
    linarith
  have hsn : ∀ y, ‖s y‖ ≠ 0 := fun y => norm_ne_zero_iff.2 (hs0 y)
  have hun : ∀ y, ‖M y *ᵥ u y‖ ≠ 0 := fun y => by
    have h1 := (hn y).2; have h2 := norm_nonneg (u y); intro h; linarith
  -- contraction rates
  obtain ⟨ys, hys⟩ := periodic_exists_max (f := fun y => ‖M y *ᵥ s y‖ / ‖s y‖)
    (hMs.norm.div hs.norm hsn) (fun y => by
      show ‖M (y + 1) *ᵥ s (y + 1)‖ / ‖s (y + 1)‖ = ‖M y *ᵥ s y‖ / ‖s y‖
      rw [hitp y, hsp y])
  obtain ⟨yu, hyu⟩ := periodic_exists_max (f := fun y => ‖u y‖ / ‖M y *ᵥ u y‖)
    (hu.norm.div hMu.norm hun) (fun y => by
      show ‖u (y + 1)‖ / ‖M (y + 1) *ᵥ u (y + 1)‖ = ‖u y‖ / ‖M y *ᵥ u y‖
      rw [hitp y, hup y])
  set θs := ‖M ys *ᵥ s ys‖ / ‖s ys‖
  set θu := ‖u yu‖ / ‖M yu *ᵥ u yu‖
  have hθs1 : θs < 1 := (div_lt_one (norm_pos_iff.2 (hs0 ys))).2 (hn ys).1
  have hθu1 : θu < 1 :=
    (div_lt_one (lt_of_le_of_ne (norm_nonneg _) (hun yu).symm)).2 (hn yu).2
  set θ := max θs θu
  have hθ0 : 0 ≤ θ := le_max_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hθ1 : θ < 1 := max_lt hθs1 hθu1
  have hcs' : ∀ y, ‖M y *ᵥ s y‖ ≤ θ * ‖s y‖ := fun y => by
    have := (hys y).trans (le_max_left θs θu)
    rwa [div_le_iff₀ (norm_pos_iff.2 (hs0 y))] at this
  have hcu' : ∀ y, ‖u y‖ ≤ θ * ‖M y *ᵥ u y‖ := fun y => by
    have := (hyu y).trans (le_max_right θs θu)
    rwa [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (hun y).symm)] at this
  -- projection bound
  have hDc : Continuous fun y => det2 (s y) (u y) := by
    unfold det2
    exact (((continuous_apply 0).comp hs).mul ((continuous_apply 1).comp hu)).sub
      (((continuous_apply 1).comp hs).mul ((continuous_apply 0).comp hu))
  obtain ⟨yk, hyk⟩ := periodic_exists_max
    (f := fun y => 2 * ‖u y‖ * ‖s y‖ / ‖det2 (s y) (u y)‖)
    (((continuous_const.mul hu.norm).mul hs.norm).div hDc.norm
      (fun y => norm_ne_zero_iff.2 (hD y))) (fun y => by
      show 2 * ‖u (y + 1)‖ * ‖s (y + 1)‖ / ‖det2 (s (y + 1)) (u (y + 1))‖ =
        2 * ‖u y‖ * ‖s y‖ / ‖det2 (s y) (u y)‖
      rw [hup y, hsp y])
  have hKP : 0 ≤ 2 * ‖u yk‖ * ‖s yk‖ / ‖det2 (s yk) (u yk)‖ := by positivity
  set KP := 2 * ‖u yk‖ * ‖s yk‖ / ‖det2 (s yk) (u yk)‖
  -- bound on the cocycle
  obtain ⟨yb, hyb⟩ := periodic_exists_max (f := fun t => ‖Acoc v E t‖) hA.continuous.norm
    (fun t => by show ‖Acoc v E (t + 1)‖ = ‖Acoc v E t‖; rw [hA.periodic t])
  set B := max ‖Acoc v E yb‖ 1
  have hB : 1 ≤ B := le_max_right _ _
  have hAB : ∀ t, ‖Acoc v E t‖ ≤ B := fun t => (hyb t).trans (le_max_left _ _)
  -- the projections
  set Ps : ℝ → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun y w => (det2 w (u y) / det2 (s y) (u y)) • s y
  set Pu : ℝ → (Fin 2 → ℂ) → (Fin 2 → ℂ) := fun y w => (det2 (s y) w / det2 (s y) (u y)) • u y
  have hsplit : ∀ y w, w = Ps y w + Pu y w := by
    intro y w
    have hD' := hD y
    ext i
    simp only [Ps, Pu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD']
    fin_cases i <;> simp [det2] <;> ring
  have hPs_add : ∀ y a b, Ps y (a + b) = Ps y a + Ps y b := by
    intro y a b; simp only [Ps, det2_add_left, add_div, add_smul]
  have hPu_add : ∀ y a b, Pu y (a + b) = Pu y a + Pu y b := by
    intro y a b; simp only [Pu, det2_add_right, add_div, add_smul]
  have hPs : ∀ y w, ‖Ps y w‖ ≤ KP * ‖w‖ := by
    intro y w
    simp only [Ps]
    rw [norm_smul, norm_div]
    have hDp : 0 < ‖det2 (s y) (u y)‖ := norm_pos_iff.2 (hD y)
    calc ‖det2 w (u y)‖ / ‖det2 (s y) (u y)‖ * ‖s y‖
        ≤ 2 * (‖w‖ * ‖u y‖) / ‖det2 (s y) (u y)‖ * ‖s y‖ := by
          gcongr; exact norm_det2_le _ _
      _ = (2 * ‖u y‖ * ‖s y‖ / ‖det2 (s y) (u y)‖) * ‖w‖ := by ring
      _ ≤ KP * ‖w‖ := by gcongr; exact hyk y
  have hPu : ∀ y w, ‖Pu y w‖ ≤ KP * ‖w‖ := by
    intro y w
    simp only [Pu]
    rw [norm_smul, norm_div]
    have hDp : 0 < ‖det2 (s y) (u y)‖ := norm_pos_iff.2 (hD y)
    calc ‖det2 (s y) w‖ / ‖det2 (s y) (u y)‖ * ‖u y‖
        ≤ 2 * (‖s y‖ * ‖w‖) / ‖det2 (s y) (u y)‖ * ‖u y‖ := by
          gcongr; exact norm_det2_le _ _
      _ = (2 * ‖u y‖ * ‖s y‖ / ‖det2 (s y) (u y)‖) * ‖w‖ := by ring
      _ ≤ KP * ‖w‖ := by gcongr; exact hyk y
  have hequiv : ∀ y w, Ps (y + n * α) (M y *ᵥ w) = M y *ᵥ Ps y w ∧
      Pu (y + n * α) (M y *ᵥ w) = M y *ᵥ Pu y w := by
    intro y w
    obtain ⟨cs, hcs⟩ := iter_inv_field hsinv n y
    obtain ⟨cu, hcu⟩ := iter_inv_field huinv n y
    have hcs0 : cs ≠ 0 := by
      rintro rfl
      apply hs0 y
      exact iter_injective (m := n) (y := y) (α := α) (v := v) (E := E)
        (by rw [hcs, zero_smul, mulVec_zero])
    have hcu0 : cu ≠ 0 := by
      rintro rfl
      apply hu0 y
      exact iter_injective (m := n) (y := y) (α := α) (v := v) (E := E)
        (by rw [hcu, zero_smul, mulVec_zero])
    exact proj_equiv (hdetM y) hcs hcu hcs0 hcu0 (hD y)
  have hcs : ∀ y w, ‖Ps (y + n * α) (M y *ᵥ w)‖ ≤ θ * ‖Ps y w‖ := by
    intro y w
    rw [(hequiv y w).1]
    simp only [Ps]
    rw [mulVec_smul, norm_smul, norm_smul]
    calc ‖det2 w (u y) / det2 (s y) (u y)‖ * ‖M y *ᵥ s y‖
        ≤ ‖det2 w (u y) / det2 (s y) (u y)‖ * (θ * ‖s y‖) := by gcongr; exact hcs' y
      _ = θ * (‖det2 w (u y) / det2 (s y) (u y)‖ * ‖s y‖) := by ring
  have hcu : ∀ y w, ‖Pu y w‖ ≤ θ * ‖Pu (y + n * α) (M y *ᵥ w)‖ := by
    intro y w
    rw [(hequiv y w).2]
    simp only [Pu]
    rw [mulVec_smul, norm_smul, norm_smul]
    calc ‖det2 (s y) w / det2 (s y) (u y)‖ * ‖u y‖
        ≤ ‖det2 (s y) w / det2 (s y) (u y)‖ * (θ * ‖M y *ᵥ u y‖) := by gcongr; exact hcu' y
      _ = θ * (‖det2 (s y) w / det2 (s y) (u y)‖ * ‖M y *ᵥ u y‖) := by ring
  have hbdd := bdd_of_dichotomy hv (x := 0) hθ0 hθ1 hKP hB hAB hsplit hPs_add hPu_add hPs hPu
    hcs hcu
  have hK0 : 0 ≤ 2 * KP * B ^ n * n / (1 - θ) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKP)
      (pow_nonneg (zero_le_one.trans hB) n)) (Nat.cast_nonneg n)) (by linarith)
  exact isUnit_of_selfAdjoint_bddBelow (isSelfAdjoint_Lop hv α E 0) (C := ⟨_, hK0⟩) hbdd

end UHdata

/-- **Johnson's theorem.** -/
theorem johnson_proof : ∀ {δ : ℝ} {v : ℂ → ℂ}, IsRealAnalyticPotential δ v → ∀ {α : ℝ},
    Irrational α → ∀ E : ℝ, E ∉ Sigma α v ↔ UH α (schr (eShift E v)) := by
  intro δ v hv α hα E
  rw [not_mem_Sigma_iff]
  constructor
  · intro h0
    obtain ⟨C, hG⟩ := green_of_isUnit hv hα h0
    exact hG.isUH
  · intro hUH
    exact isUnit_of_UH hv hUH

/-- **Johnson's theorem**: for irrational `α` and a real-analytic potential,
`E ∉ Σ_{α,v}` iff `(α, A^{(E-v)})` is uniformly hyperbolic. -/
theorem johnson {δ : ℝ} {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) {α : ℝ}
    (hα : Irrational α) (E : ℝ) : E ∉ Sigma α v ↔ UH α (schr (eShift E v)) :=
  johnson_proof hv hα E

end AvilaGlobal
