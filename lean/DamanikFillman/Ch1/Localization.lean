/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Uniform and semi-uniform localization  (book §1.7, pp. 56–61)

Definitions 1.7.1: `DF.SULE`, `DF.SUDL`, `DF.ULE`, `DF.UDL` for a bounded self-adjoint operator on
`ℓ²(ℤ)`; the complete set of orthonormal eigenvectors is a `HilbertBasis ℕ ℂ (L2 ℤ)`.

Main results
* `DF.card_le_of_localized` — the counting estimate behind Lemma 1.7.2(b): if the eigenvectors
  centred near `j` are localized, then at most linearly many centres lie in a ball of radius
  `L` (this is the upper bound (1.7.9));
* `DF.SULE.card_centres_le` — Lemma 1.7.2(b), finiteness and linear growth of
  `#{k : |n_k| ≤ L}`;
* `DF.SULE.sudl` — **Theorem 1.7.3**: SULE implies SUDL;
* `DF.ULE.udl` — **Theorem 1.7.4**: ULE implies UDL.

Deviations
* Lemma 1.7.2(a) is not stated separately (its content is used in `card_le_of_localized`), and
  the asymptotics `#{k : |n_k| ≤ L}/(2L+1) → 1` of (1.7.6) are not formalized; only the linear
  upper bound, which is what the proof of Theorem 1.7.3 needs, is proved.
* In SUDL we obtain the weight `e^{δ|m|}` (as in (1.7.2)); the decay rate is `γ/2`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.RAGE

noncomputable section

open scoped InnerProductSpace ComplexConjugate Topology
open Filter Real L2

namespace DF

/-- The standard basis vector `δ_n` of `ℓ²(ℤ)`. -/
abbrev dlt (n : ℤ) : L2 ℤ := lp.single 2 n (1 : ℂ)

/-- **SULE** (Definition 1.7.1(a)). -/
def SULE (A : L2 ℤ →L[ℂ] L2 ℤ) : Prop :=
  ∃ (u : HilbertBasis ℕ ℂ (L2 ℤ)) (E : ℕ → ℝ) (γ : ℝ) (c : ℕ → ℤ), 0 < γ ∧
    (∀ k, A (u k) = (E k : ℂ) • u k) ∧
    ∀ δ > 0, ∃ C : ℝ, ∀ k n, ‖u k n‖ ≤ C * exp (δ * |(c k : ℝ)|) * exp (-γ * |(n : ℝ) - c k|)

/-- **ULE** (Definition 1.7.1(c)). -/
def ULE (A : L2 ℤ →L[ℂ] L2 ℤ) : Prop :=
  ∃ (u : HilbertBasis ℕ ℂ (L2 ℤ)) (E : ℕ → ℝ) (γ C : ℝ) (c : ℕ → ℤ), 0 < γ ∧
    (∀ k, A (u k) = (E k : ℂ) • u k) ∧ ∀ k n, ‖u k n‖ ≤ C * exp (-γ * |(n : ℝ) - c k|)

/-- **SUDL** (Definition 1.7.1(b)). -/
def SUDL (A : L2 ℤ →L[ℂ] L2 ℤ) (hA : IsSelfAdjoint A) : Prop :=
  ∃ γ > 0, ∀ δ > 0, ∃ C : ℝ, ∀ (m n : ℤ) (t : ℝ),
    ‖⟪dlt m, evol A hA t (dlt n)⟫_ℂ‖ ≤ C * exp (δ * |(m : ℝ)|) * exp (-γ * |(m : ℝ) - n|)

/-- **UDL** (Definition 1.7.1(d)). -/
def UDL (A : L2 ℤ →L[ℂ] L2 ℤ) (hA : IsSelfAdjoint A) : Prop :=
  ∃ C γ : ℝ, 0 < γ ∧ ∀ (m n : ℤ) (t : ℝ),
    ‖⟪dlt m, evol A hA t (dlt n)⟫_ℂ‖ ≤ C * exp (-γ * |(m : ℝ) - n|)

/-! ### Geometric sums over `ℤ` -/

lemma summable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Summable fun j : ℤ => exp (-a * |(j : ℝ)|) := by
  have hnat : Summable fun n : ℕ => exp (-a * |((n : ℤ) : ℝ)|) := by
    have := summable_geometric_of_lt_one (exp_pos (-a)).le (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← exp_nat_mul]; push_cast; rw [abs_of_nonneg (Nat.cast_nonneg n)]; ring_nf
  refine Summable.of_nat_of_neg hnat ?_
  refine hnat.congr fun n => ?_
  push_cast; rw [abs_neg]

/-- `S(a) = ∑_{j ∈ ℤ} e^{-a|j|}`. -/
def geomZ (a : ℝ) : ℝ := ∑' j : ℤ, exp (-a * |(j : ℝ)|)

lemma summable_exp_neg_abs_sub {a : ℝ} (ha : 0 < a) (c : ℤ) :
    Summable fun n : ℤ => exp (-a * |(n : ℝ) - c|) := by
  have := (Equiv.subRight c).summable_iff.2 (summable_exp_neg_abs ha)
  refine this.congr fun n => ?_
  simp

lemma tsum_exp_neg_abs_sub {a : ℝ} (c : ℤ) :
    ∑' n : ℤ, exp (-a * |(n : ℝ) - c|) = geomZ a := by
  have := (Equiv.subRight c).tsum_eq (fun j : ℤ => exp (-a * |(j : ℝ)|))
  simp only [Equiv.subRight_apply, Int.cast_sub] at this
  exact this

lemma geomZ_nonneg (a : ℝ) : 0 ≤ geomZ a := tsum_nonneg fun _ => (exp_pos _).le

/-! ### Head and tail of a vector around a centre -/

lemma head_add_tail (v : L2 ℤ) (j : ℤ) (R : ℕ) :
    ‖v‖ ^ 2 = ∑ n ∈ Finset.Icc (j - R) (j + R), ‖v n‖ ^ 2 +
      ∑' n : ℤ, if (R : ℝ) < |(n : ℝ) - j| then ‖v n‖ ^ 2 else 0 := by
  have hs := summable_norm_sq v
  have h1 : Summable fun n : ℤ => if (R : ℝ) < |(n : ℝ) - j| then ‖v n‖ ^ 2 else 0 :=
    hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> simp)
  have h2 : Summable fun n : ℤ => if (R : ℝ) < |(n : ℝ) - j| then 0 else ‖v n‖ ^ 2 :=
    hs.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> simp)
  have hmem : ∀ n : ℤ, n ∈ Finset.Icc (j - R) (j + R) ↔ ¬ (R : ℝ) < |(n : ℝ) - j| := by
    intro n
    rw [Finset.mem_Icc, not_lt, abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ((j - R : ℤ) : ℝ) ≤ n := by exact_mod_cast h1
      have h2' : (n : ℝ) ≤ ((j + R : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at h1' h2'
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      constructor
      · have : ((j - R : ℤ) : ℝ) ≤ n := by push_cast; linarith
        exact_mod_cast this
      · have : (n : ℝ) ≤ ((j + R : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
  rw [norm_sq_eq_tsum]
  have : (fun n : ℤ => ‖v n‖ ^ 2) = fun n : ℤ => (if (R : ℝ) < |(n : ℝ) - j| then 0 else ‖v n‖ ^ 2) +
      (if (R : ℝ) < |(n : ℝ) - j| then ‖v n‖ ^ 2 else 0) := by
    funext n; split_ifs <;> simp
  conv_lhs => rw [this]
  rw [h2.tsum_add h1]
  congr 1
  rw [tsum_eq_sum (s := Finset.Icc (j - R) (j + R))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_neg ((hmem n).1 hn)]
  · intro n hn
    rw [if_pos (not_not.1 (fun h => hn ((hmem n).2 h)))]

/-! ### Counting localization centres -/

/-- Parseval for the eigenbasis at a site: `∑_k |u_k(n)|² = 1`. -/
lemma tsum_norm_sq_basis (u : HilbertBasis ℕ ℂ (L2 ℤ)) (n : ℤ) :
    ∑' k, ‖u k n‖ ^ 2 = 1 := by
  have h := norm_sq_eq_tsum (u.repr (dlt n))
  rw [LinearIsometryEquiv.norm_map, lp.norm_single (by norm_num), norm_one, one_pow] at h
  rw [h]
  congr 1; funext k
  rw [HilbertBasis.repr_apply_apply, lp.inner_single_right]
  simp

lemma summable_norm_sq_basis (u : HilbertBasis ℕ ℂ (L2 ℤ)) (n : ℤ) :
    Summable fun k => ‖u k n‖ ^ 2 := by
  have h := summable_norm_sq (u.repr (dlt n))
  refine h.congr fun k => ?_
  rw [HilbertBasis.repr_apply_apply, lp.inner_single_right]
  simp

/-- Counting estimate behind Lemma 1.7.2(b) / (1.7.9). -/
theorem card_le_of_localized (u : HilbertBasis ℕ ℂ (L2 ℤ)) (c : ℕ → ℤ) {γ B : ℝ} (hγ : 0 < γ)
    (j : ℤ) (L R : ℕ) (hLR : L ≤ R)
    (hbound : ∀ k, |(c k : ℝ) - j| ≤ L → ∀ n : ℤ, ‖u k n‖ ≤ B * exp (-γ * |(n : ℝ) - c k|))
    (hsmall : B ^ 2 * geomZ γ * exp (-γ * ((R : ℝ) - L)) ≤ 1 / 2)
    (F : Finset ℕ) (hF : ∀ k ∈ F, |(c k : ℝ) - j| ≤ L) :
    (F.card : ℝ) ≤ 2 * (2 * R + 1) := by
  -- each eigenvector has at least half of its mass in the window
  have hhead : ∀ k ∈ F, (1 / 2 : ℝ) ≤ ∑ n ∈ Finset.Icc (j - R) (j + R), ‖u k n‖ ^ 2 := by
    intro k hk
    have hsplit := head_add_tail (u k) j R
    rw [u.orthonormal.1 k, one_pow] at hsplit
    have htail : (∑' n : ℤ, if (R : ℝ) < |(n : ℝ) - j| then ‖u k n‖ ^ 2 else 0) ≤ 1 / 2 := by
      refine le_trans ?_ hsmall
      refine le_trans (Summable.tsum_le_tsum (g := fun n : ℤ => exp (-γ * ((R : ℝ) - L)) *
        (B ^ 2 * exp (-γ * |(n : ℝ) - c k|))) (fun n => ?_) ?_ ?_) (le_of_eq ?_)
      rotate_right
      · rw [tsum_mul_left, tsum_mul_left, tsum_exp_neg_abs_sub]; ring
      · split_ifs with h
        · have hb := hbound k (hF k hk) n
          have hdist : (R : ℝ) - L ≤ |(n : ℝ) - c k| := by
            have := abs_sub_abs_le_abs_sub ((n : ℝ) - j) ((c k : ℝ) - j)
            have h' := hF k hk
            rw [show (n : ℝ) - j - ((c k : ℝ) - j) = (n : ℝ) - c k by ring] at this
            linarith
          calc ‖u k n‖ ^ 2 ≤ (B * exp (-γ * |(n : ℝ) - c k|)) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) hb 2
            _ = B ^ 2 * (exp (-γ * |(n : ℝ) - c k|) * exp (-γ * |(n : ℝ) - c k|)) := by ring
            _ ≤ B ^ 2 * (exp (-γ * ((R : ℝ) - L)) * exp (-γ * |(n : ℝ) - c k|)) := by
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                  (exp_le_exp.2 (by nlinarith)) (exp_pos _).le) (sq_nonneg B)
            _ = exp (-γ * ((R : ℝ) - L)) * (B ^ 2 * exp (-γ * |(n : ℝ) - c k|)) := by ring
        · positivity
      · exact (summable_norm_sq (u k)).of_nonneg_of_le
          (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> simp)
      · exact ((summable_exp_neg_abs_sub hγ (c k)).mul_left _).mul_left _
    linarith
  -- sum over the window and use Parseval at each site
  have hsum : (F.card : ℝ) * (1 / 2) ≤ 2 * R + 1 := by
    calc (F.card : ℝ) * (1 / 2) = ∑ k ∈ F, (1 / 2 : ℝ) := by simp
      _ ≤ ∑ k ∈ F, ∑ n ∈ Finset.Icc (j - R) (j + R), ‖u k n‖ ^ 2 := Finset.sum_le_sum hhead
      _ = ∑ n ∈ Finset.Icc (j - R) (j + R), ∑ k ∈ F, ‖u k n‖ ^ 2 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.Icc (j - R) (j + R), (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [← tsum_norm_sq_basis u n]
          exact (summable_norm_sq_basis u n).sum_le_tsum _ fun k _ => by positivity
      _ = 2 * R + 1 := by
          simp only [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
          rw [show j + R + 1 - (j - R) = ((2 * R + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
          push_cast; ring
  linarith

/-- Summation of `e^{-a d_k}` given a linear counting bound. -/
theorem summable_of_card_le (c : ℕ → ℤ) (j : ℤ) {a α β : ℝ} (ha : 0 < a) (hα : 0 ≤ α)
    (hβ : 0 ≤ β)
    (hcard : ∀ (L : ℕ) (F : Finset ℕ), (∀ k ∈ F, |(c k : ℝ) - j| ≤ L) → (F.card : ℝ) ≤ α * L + β) :
    Summable (fun k => exp (-a * |(c k : ℝ) - j|)) ∧
      ∑' k, exp (-a * |(c k : ℝ) - j|) ≤ ∑' L : ℕ, (α * L + β) * exp (-a * L) := by
  have hS : Summable fun L : ℕ => (α * L + β) * exp (-a * L) := by
    have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 ha
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 ha
    refine ((h1.mul_left α).add (h0.mul_left β)).congr fun L => ?_
    simp; ring
  have hgeo : Summable fun L : ℕ => exp (-a * L) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 ha
  set d : ℕ → ℕ := fun k => (c k - j).natAbs
  have hd : ∀ k, |(c k : ℝ) - j| = d k := by
    intro k; simp only [d]; rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl
  have hfin : ∀ F : Finset ℕ, ∑ k ∈ F, exp (-a * |(c k : ℝ) - j|) ≤
      ∑' L : ℕ, (α * L + β) * exp (-a * L) := by
    intro F
    have hterm : ∀ k, exp (-a * |(c k : ℝ) - j|) ≤
        ∑' L : ℕ, if d k ≤ L then exp (-a * L) else 0 := by
      intro k
      have hs : Summable fun L : ℕ => if d k ≤ L then exp (-a * L) else 0 :=
        hgeo.of_nonneg_of_le (fun L => by split_ifs <;> positivity)
          (fun L => by split_ifs <;> simp [(exp_pos _).le])
      have := hs.le_tsum (d k) (fun L _ => by split_ifs <;> positivity)
      rw [if_pos le_rfl] at this
      rw [hd]; exact this
    calc ∑ k ∈ F, exp (-a * |(c k : ℝ) - j|)
        ≤ ∑ k ∈ F, ∑' L : ℕ, (if d k ≤ L then exp (-a * L) else 0) := Finset.sum_le_sum
          fun k _ => hterm k
      _ = ∑' L : ℕ, ∑ k ∈ F, (if d k ≤ L then exp (-a * L) else 0) := by
          rw [Summable.tsum_finsetSum]
          intro k _
          exact hgeo.of_nonneg_of_le (fun L => by split_ifs <;> positivity)
            (fun L => by split_ifs <;> simp [(exp_pos _).le])
      _ ≤ ∑' L : ℕ, (α * L + β) * exp (-a * L) := by
          refine Summable.tsum_le_tsum (fun L => ?_) ?_ hS
          · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
            refine hcard L _ fun k hk => ?_
            rw [Finset.mem_filter] at hk
            rw [hd]; exact_mod_cast hk.2
          · refine summable_of_sum_le (c := ∑' L : ℕ, (α * L + β) * exp (-a * L)) ?_ ?_ |>.congr
              fun _ => rfl
            · intro L; exact Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
            · intro G
              refine (Finset.sum_le_sum fun L _ => ?_).trans (hS.sum_le_tsum G fun L _ => by
                have : (0 : ℝ) ≤ α * L + β := by positivity
                positivity)
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
              refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
              refine hcard L _ fun k hk => ?_
              rw [Finset.mem_filter] at hk
              rw [hd]; exact_mod_cast hk.2
  exact ⟨summable_of_sum_le (fun k => (exp_pos _).le) hfin,
    Real.tsum_le_of_sum_le (fun k => (exp_pos _).le) hfin⟩

/-! ### Matrix elements of the evolution in an eigenbasis -/

section Dynamics

variable {A : L2 ℤ →L[ℂ] L2 ℤ} {hA : IsSelfAdjoint A}

lemma norm_inner_dlt_left (v : L2 ℤ) (m : ℤ) : ‖⟪dlt m, v⟫_ℂ‖ = ‖v m‖ := by
  rw [lp.inner_single_left]; simp

lemma norm_inner_dlt_right (v : L2 ℤ) (n : ℤ) : ‖⟪v, dlt n⟫_ℂ‖ = ‖v n‖ := by
  rw [lp.inner_single_right]; simp

/-- Expansion of `⟪δ_m, e^{-itA} δ_n⟫` in an eigenbasis and the resulting bound
`|⟪δ_m, e^{-itA} δ_n⟫| ≤ ∑_k |u_k(m)| |u_k(n)|`. -/
lemma norm_inner_evol_le (u : HilbertBasis ℕ ℂ (L2 ℤ)) (E : ℕ → ℝ)
    (heig : ∀ k, A (u k) = (E k : ℂ) • u k) (m n : ℤ) (t : ℝ) {g : ℕ → ℝ}
    (hg : ∀ k, ‖u k m‖ * ‖u k n‖ ≤ g k) (hgs : Summable g) :
    ‖⟪dlt m, evol A hA t (dlt n)⟫_ℂ‖ ≤ ∑' k, g k := by
  rw [← u.tsum_inner_mul_inner]
  have hterm : ∀ k, ‖⟪dlt m, u k⟫_ℂ * ⟪u k, evol A hA t (dlt n)⟫_ℂ‖ = ‖u k m‖ * ‖u k n‖ := by
    intro k
    rw [norm_mul, norm_inner_dlt_left, ← ContinuousLinearMap.adjoint_inner_left, adjoint_evol,
      evol_eigenvector (heig k), inner_smul_left, norm_mul, RCLike.norm_conj, norm_expPhase,
      one_mul, norm_inner_dlt_right]
  have hs : Summable fun k => ‖⟪dlt m, u k⟫_ℂ * ⟪u k, evol A hA t (dlt n)⟫_ℂ‖ :=
    hgs.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => (hterm k).le.trans (hg k))
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  exact Summable.tsum_le_tsum (fun k => (hterm k).le.trans (hg k)) hs hgs

lemma exists_nat_small (K γ : ℝ) (hγ : 0 < γ) : ∃ R : ℕ, K * exp (-γ * R) ≤ 1 / 2 := by
  have h : Tendsto (fun R : ℕ => K * exp (-γ * R)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hγ)).const_mul K
    rw [mul_zero] at this
    refine this.congr fun R => ?_
    simp [neg_mul]
  exact (h.eventually (ge_mem_nhds (by norm_num))).exists

/-- **Lemma 1.7.2(b)** (linear growth, cf. (1.7.9)): under SULE the number of localization
centres in `[-L, L]` grows at most linearly; in particular it is finite. -/
theorem SULE.card_centres_le (u : HilbertBasis ℕ ℂ (L2 ℤ)) (c : ℕ → ℤ) {γ : ℝ} (hγ : 0 < γ)
    (hloc : ∀ δ > 0, ∃ C : ℝ, ∀ k n, ‖u k n‖ ≤ C * exp (δ * |(c k : ℝ)|) *
      exp (-γ * |(n : ℝ) - c k|)) :
    ∃ R₁ : ℕ, ∀ (L : ℕ) (F : Finset ℕ), (∀ k ∈ F, |(c k : ℝ) - ((0 : ℤ) : ℝ)| ≤ L) →
      (F.card : ℝ) ≤ 8 * L + (4 * R₁ + 2) := by
  obtain ⟨C, hC⟩ := hloc (γ / 4) (by positivity)
  obtain ⟨R₁, hR₁⟩ := exists_nat_small (C ^ 2 * geomZ γ) γ hγ
  refine ⟨R₁, fun L F hF => ?_⟩
  have := card_le_of_localized u c (B := |C| * exp (γ / 4 * L)) hγ 0 L (2 * L + R₁)
    (by omega) (fun k hk n => ?_) ?_ F hF
  · push_cast at this; linarith
  · refine (hC k n).trans ?_
    rw [Int.cast_zero, sub_zero] at hk
    refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
    refine mul_le_mul (le_abs_self C) (exp_le_exp.2 ?_) (exp_pos _).le (abs_nonneg _)
    nlinarith
  · have hexp : (|C| * exp (γ / 4 * L)) ^ 2 * geomZ γ * exp (-γ * (((2 * L + R₁ : ℕ) : ℝ) - L))
        = C ^ 2 * geomZ γ * exp (-γ * R₁) * exp (-(γ / 2) * L) := by
      rw [mul_pow, sq_abs, ← exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (γ / 4 * L) = γ / 2 * L := by push_cast; ring
      rw [this]
      push_cast
      rw [show C ^ 2 * exp (γ / 2 * L) * geomZ γ * exp (-γ * (2 * L + R₁ - L)) =
        C ^ 2 * geomZ γ * (exp (γ / 2 * L) * exp (-γ * (2 * L + R₁ - L))) by ring, ← exp_add]
      rw [show C ^ 2 * geomZ γ * exp (-γ * R₁) * exp (-(γ / 2) * L) =
        C ^ 2 * geomZ γ * (exp (-γ * R₁) * exp (-(γ / 2) * L)) by ring, ← exp_add]
      congr 2; ring
    rw [hexp]
    have h1 : exp (-(γ / 2) * L) ≤ 1 := exp_le_one_iff.2 (by
      have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith)
    have h2 : 0 ≤ C ^ 2 * geomZ γ * exp (-γ * R₁) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (geomZ_nonneg _)) (exp_pos _).le
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.7.3**: SULE implies SUDL. -/
theorem SULE.sudl (hA : IsSelfAdjoint A) (h : SULE A) : SUDL A hA := by
  obtain ⟨u, E, γ, c, hγ, heig, hloc⟩ := h
  obtain ⟨R₁, hcard⟩ := SULE.card_centres_le u c hγ hloc
  refine ⟨γ / 2, half_pos hγ, fun δ hδ => ?_⟩
  set δ' := min δ (γ / 6) / 3
  have hδ' : 0 < δ' := by positivity
  have h3δ : 3 * δ' ≤ δ := by simp only [δ']; linarith [min_le_left δ (γ / 6)]
  have h3γ : 3 * δ' ≤ γ / 2 := by simp only [δ']; linarith [min_le_right δ (γ / 6)]
  obtain ⟨C, hC⟩ := hloc δ' hδ'
  obtain ⟨hsum, htsum⟩ := summable_of_card_le c 0 hδ' (by norm_num : (0 : ℝ) ≤ 8)
    (by positivity : (0 : ℝ) ≤ 4 * R₁ + 2) hcard
  set M := ∑' L : ℕ, (8 * (L : ℝ) + (4 * R₁ + 2)) * exp (-δ' * L)
  refine ⟨C ^ 2 * M, fun m n t => ?_⟩
  set g : ℕ → ℝ := fun k => C ^ 2 * exp (3 * δ' * |(m : ℝ)|) *
    exp (-(γ - 3 * δ') * |(m : ℝ) - n|) * exp (-δ' * |(c k : ℝ) - ((0 : ℤ) : ℝ)|)
  have hg : ∀ k, ‖u k m‖ * ‖u k n‖ ≤ g k := by
    intro k
    have hm := hC k m
    have hn := hC k n
    refine (mul_le_mul hm hn (norm_nonneg _) ((norm_nonneg _).trans hm)).trans ?_
    have e1 : C * exp (δ' * |(c k : ℝ)|) * exp (-γ * |(m : ℝ) - c k|) *
        (C * exp (δ' * |(c k : ℝ)|) * exp (-γ * |(n : ℝ) - c k|)) =
        C ^ 2 * exp (2 * δ' * |(c k : ℝ)| - γ * (|(m : ℝ) - c k| + |(n : ℝ) - c k|)) := by
      rw [show 2 * δ' * |(c k : ℝ)| - γ * (|(m : ℝ) - c k| + |(n : ℝ) - c k|) =
        δ' * |(c k : ℝ)| + -γ * |(m : ℝ) - c k| + (δ' * |(c k : ℝ)| + -γ * |(n : ℝ) - c k|) by ring,
        exp_add, exp_add, exp_add]; ring
    have e2 : g k = C ^ 2 * exp (3 * δ' * |(m : ℝ)| - (γ - 3 * δ') * |(m : ℝ) - n| -
        δ' * |(c k : ℝ)|) := by
      simp only [g, Int.cast_zero, sub_zero]
      rw [show 3 * δ' * |(m : ℝ)| - (γ - 3 * δ') * |(m : ℝ) - n| - δ' * |(c k : ℝ)| =
        3 * δ' * |(m : ℝ)| + -(γ - 3 * δ') * |(m : ℝ) - n| + -δ' * |(c k : ℝ)| by ring,
        exp_add, exp_add]; ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (sq_nonneg _)
    have h1 : |(m : ℝ) - n| ≤ |(m : ℝ) - c k| + |(n : ℝ) - c k| := by
      have := abs_sub_le (m : ℝ) (c k) n
      rw [abs_sub_comm (c k : ℝ) n] at this; exact this
    have h2 : |(c k : ℝ)| - |(m : ℝ)| ≤ |(m : ℝ) - c k| + |(n : ℝ) - c k| := by
      have := abs_sub_abs_le_abs_sub (c k : ℝ) m
      rw [abs_sub_comm] at this
      linarith [abs_nonneg ((n : ℝ) - c k)]
    have hpos : 0 ≤ γ - 3 * δ' := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hpos, mul_le_mul_of_nonneg_left h2 hδ'.le]
  have hgs : Summable g := hsum.mul_left _
  refine (norm_inner_evol_le u E heig m n t hg hgs).trans ?_
  rw [tsum_mul_left]
  have hM : ∑' k, exp (-δ' * |(c k : ℝ) - ((0 : ℤ) : ℝ)|) ≤ M := htsum
  have hpre : 0 ≤ C ^ 2 * exp (3 * δ' * |(m : ℝ)|) * exp (-(γ - 3 * δ') * |(m : ℝ) - n|) := by
    positivity
  calc C ^ 2 * exp (3 * δ' * |(m : ℝ)|) * exp (-(γ - 3 * δ') * |(m : ℝ) - n|) *
        ∑' k, exp (-δ' * |(c k : ℝ) - ((0 : ℤ) : ℝ)|)
      ≤ C ^ 2 * exp (3 * δ' * |(m : ℝ)|) * exp (-(γ - 3 * δ') * |(m : ℝ) - n|) * M :=
        mul_le_mul_of_nonneg_left hM hpre
    _ ≤ C ^ 2 * exp (δ * |(m : ℝ)|) * exp (-(γ / 2) * |(m : ℝ) - n|) * M := by
        have hM0 : 0 ≤ M := le_trans (tsum_nonneg fun _ => (exp_pos _).le) hM
        refine mul_le_mul_of_nonneg_right ?_ hM0
        refine mul_le_mul (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (sq_nonneg _))
          (exp_le_exp.2 ?_) (exp_pos _).le (by positivity)
        · nlinarith [abs_nonneg (m : ℝ)]
        · nlinarith [abs_nonneg ((m : ℝ) - n)]
    _ = C ^ 2 * M * exp (δ * |(m : ℝ)|) * exp (-(γ / 2) * |(m : ℝ) - n|) := by ring

/-- **Theorem 1.7.4**: ULE implies UDL. -/
theorem ULE.udl (hA : IsSelfAdjoint A) (h : ULE A) : UDL A hA := by
  obtain ⟨u, E, γ, C, c, hγ, heig, hloc⟩ := h
  obtain ⟨R₁, hR₁⟩ := exists_nat_small (C ^ 2 * geomZ γ) γ hγ
  have hcard : ∀ (j : ℤ) (L : ℕ) (F : Finset ℕ), (∀ k ∈ F, |(c k : ℝ) - j| ≤ L) →
      (F.card : ℝ) ≤ 4 * L + (4 * R₁ + 2) := by
    intro j L F hF
    have := card_le_of_localized u c (B := C) hγ j L (L + R₁) (by omega)
      (fun k _ n => hloc k n) (by push_cast; rw [show (L : ℝ) + R₁ - L = R₁ by ring]; exact hR₁)
      F hF
    push_cast at this; linarith
  set M := ∑' L : ℕ, (4 * (L : ℝ) + (4 * R₁ + 2)) * exp (-(γ / 2) * L)
  refine ⟨C ^ 2 * M, γ / 2, half_pos hγ, fun m n t => ?_⟩
  obtain ⟨hsum, htsum⟩ := summable_of_card_le c m (half_pos hγ) (by norm_num : (0 : ℝ) ≤ 4)
    (by positivity : (0 : ℝ) ≤ 4 * R₁ + 2) (hcard m)
  set g : ℕ → ℝ := fun k => C ^ 2 * exp (-(γ / 2) * |(m : ℝ) - n|) *
    exp (-(γ / 2) * |(c k : ℝ) - m|)
  have hg : ∀ k, ‖u k m‖ * ‖u k n‖ ≤ g k := by
    intro k
    have hm := hloc k m
    have hn := hloc k n
    refine (mul_le_mul hm hn (norm_nonneg _) ((norm_nonneg _).trans hm)).trans ?_
    have e1 : C * exp (-γ * |(m : ℝ) - c k|) * (C * exp (-γ * |(n : ℝ) - c k|)) =
        C ^ 2 * exp (-γ * (|(m : ℝ) - c k| + |(n : ℝ) - c k|)) := by
      rw [mul_add, exp_add]; ring
    have e2 : g k = C ^ 2 * exp (-(γ / 2) * |(m : ℝ) - n| + -(γ / 2) * |(c k : ℝ) - m|) := by
      simp only [g]; rw [exp_add]; ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (sq_nonneg _)
    have h1 : |(m : ℝ) - n| ≤ |(m : ℝ) - c k| + |(n : ℝ) - c k| := by
      have := abs_sub_le (m : ℝ) (c k) n
      rw [abs_sub_comm (c k : ℝ) n] at this; exact this
    have h2 : |(c k : ℝ) - m| ≤ |(m : ℝ) - c k| + |(n : ℝ) - c k| := by
      rw [abs_sub_comm]; linarith [abs_nonneg ((n : ℝ) - c k)]
    nlinarith
  have hgs : Summable g := hsum.mul_left _
  refine (norm_inner_evol_le u E heig m n t hg hgs).trans ?_
  rw [tsum_mul_left]
  have hpre : 0 ≤ C ^ 2 * exp (-(γ / 2) * |(m : ℝ) - n|) := by positivity
  calc C ^ 2 * exp (-(γ / 2) * |(m : ℝ) - n|) * ∑' k, exp (-(γ / 2) * |(c k : ℝ) - m|)
      ≤ C ^ 2 * exp (-(γ / 2) * |(m : ℝ) - n|) * M := mul_le_mul_of_nonneg_left htsum hpre
    _ = C ^ 2 * M * exp (-(γ / 2) * |(m : ℝ) - n|) := by ring

end Dynamics

end DF
