/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Continuity of the spectrum  (paper §5: Lemma 5.1, (5.2), Theorem 5.2)

Paper references (`Arxiv_version-5.tex`):
* Lemma 5.1 (`lemma-S`, tex l. 748–795), inequality (5.1) (`bt-ineq`):
  `lemma_S` — for `α` of bounded type, `∑_{k<L} 1/|b(αk+θ)| ≥ C L ln L`;
* the definition of `S_*(L)` and the bound `S_*(q_k) ≥ c q_k ln q_k` (tex l. 798–815):
  `Sstar`, `orbit_sum_ge`, `exists_large_good_denominator`;
* (5.2) (`sum-superlinear`, tex l. 816–820): `superlinear`, `tendsto_Sstar_div`;
* Theorem 5.2 (`continuitylemma1`, tex l. 823–855), with (5.7) `cgeneral`, (5.8)
  `cbounded`, (5.9) `csingular`: `cgeneral`, `cgeneral_convergents`, `cbounded`,
  `csingular`, `csingular_convergents`.  The proof (tex l. 858–1024) is in
  `AMSCore.lean` (`infDist_sigmaM_le`).

## The Denjoy–Koksma step
The paper applies the Denjoy–Koksma inequality to `g_q(x) = min(q, ‖x‖⁻¹)`.  We prove the
needed lower bound directly (`orbit_sum_ge`): for coprime `p, q` with `|α - p/q| ≤ 1/q²`,
the points `θ + kα`, `0 ≤ k < q`, are `2/q`-close to the points `(a + kp)/q`, which run
through all residues `j/q` (mod 1) exactly once; hence
`∑_{k<q} 1/|b(θ+kα)| ≥ (q/K) ∑_{j<q} 1/(j+2) ≥ (q/K) ln((q+2)/2)`, where `K` is a Lipschitz
constant of `b` (so `|b(x)| ≤ K ‖x‖_𝕋` as `b(0) = 0`).

## Conventions and hypotheses made explicit
* `1/0 = ∞` in the paper: we only sum over phases `θ` whose orbit avoids the zeros of
  `b`; `Sstar` is the infimum over such phases (which is the paper's `S_*`, phases with a
  zero on the orbit contributing `+∞`).
* "bounded type" is taken in its Diophantine form `BoundedType α`:
  `∃ c > 0, ∀ q ≥ 1, ∀ p, |qα - p| ≥ c/q` (badly approximable numbers), which is
  classically equivalent to bounded partial quotients.
* `b, v` are bounded and Lipschitz (`C¹` periodic in the paper); `b` is `1`-periodic with
  a zero, and its zero set is countable (finitely many zeros per period in the paper).

Everything in this file is proved completely (no `sorry`, no extra hypotheses beyond
those listed above).
-/
import CriticalAMOHausdorff.AMSCore
import SpectralGapsDimension.SmallDivisors
import SpectralGapsDimension.Arithmetic

noncomputable section

open Real Finset Filter Topology

namespace CAH

/-! ### Elementary arithmetic -/

/-- `ln((q+2)/2) ≤ ∑_{j<q} 1/(j+2)`. -/
lemma log_sub_log_two_le_sum (q : ℕ) :
    Real.log (q + 2) - Real.log 2 ≤ ∑ j ∈ range q, 1 / ((j : ℝ) + 2) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    have h1 : Real.log ((n : ℝ) + 1 + 2) - Real.log (n + 2) ≤ 1 / (n + 2) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1 + 2) / (n + 2) by positivity)
      have e : ((n : ℝ) + 1 + 2) / (n + 2) - 1 = 1 / (n + 2) := by field_simp; ring
      linarith
    linarith

/-- Dirichlet's theorem with a reduced fraction: for `n ≥ 1` there are coprime `p, q` with
`1 ≤ q ≤ n` and `|qξ - p| ≤ 1/(n+1)`. -/
lemma dirichlet_coprime (ξ : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ q ≤ n ∧ IsCoprime p (q : ℤ) ∧ |q * ξ - p| ≤ 1 / (n + 1) := by
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le ξ hn
  have hg : 0 < Int.gcd j k := Int.gcd_pos_of_ne_zero_right j hk0.ne'
  obtain ⟨j', k', hco, hj, hk⟩ := Int.exists_gcd_one hg
  set g : ℕ := Int.gcd j k
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hk'0 : 0 < k' := by
    by_contra h
    push_neg at h
    have : k ≤ 0 := by rw [hk]; exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    omega
  refine ⟨j', k'.toNat, by omega, ?_, ?_, ?_⟩
  · have : k' ≤ k := by
      rw [hk]; exact le_mul_of_one_le_right hk'0.le (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg.ne')
    omega
  · rw [Int.toNat_of_nonneg hk'0.le]
    exact Int.isCoprime_iff_gcd_eq_one.2 hco
  · have hcast : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
      rw [show ((k'.toNat : ℕ) : ℝ) = ((k'.toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg hk'0.le]
    rw [hcast]
    have e : (k : ℝ) * ξ - j = g * ((k' : ℝ) * ξ - j') := by
      rw [hk, hj]; push_cast; ring
    rw [e, abs_mul, abs_of_pos hg'] at hjk
    have h1 : (1 : ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg.ne'
    have h2 : 0 ≤ |(k' : ℝ) * ξ - j'| := abs_nonneg _
    nlinarith

/-- `|b(x)| ≤ K |x - z|` for integers `z`, if `b` is `1`-periodic, `b(0) = 0` and
`K`-Lipschitz. -/
lemma abs_le_of_zero {b : ℝ → ℝ} (hper : Function.Periodic b 1) (h0 : b 0 = 0) {K : ℝ}
    (hK : ∀ x y, |b x - b y| ≤ K * |x - y|) (x : ℝ) (z : ℤ) : |b x| ≤ K * |x - z| := by
  have : b x = b (x - z) := by
    rw [show x - (z : ℝ) = x - (z : ℝ) * 1 by ring]; exact (hper.sub_int_mul_eq z).symm
  rw [this, ← sub_zero (b (x - z)), ← h0]
  simpa using hK (x - z) 0

/-! ### The Denjoy–Koksma substitute -/

/-- **Lower bound on an orbit segment of length `q`** (the `q_n`-step of the proof of
Lemma 5.1, tex l. 763–785).  If `b` is `1`-periodic, `K`-Lipschitz with `b(0) = 0`, and
`p, q` are coprime with `|α - p/q| ≤ 1/q²`, then for every phase `θ` whose first `q` orbit
points avoid the zeros of `b`,
`∑_{k<q} 1/|b(θ+kα)| ≥ (q/K) (ln(q+2) - ln 2)`. -/
theorem orbit_sum_ge {b : ℝ → ℝ} (hper : Function.Periodic b 1) (h0 : b 0 = 0) {K : ℝ}
    (hK0 : 0 < K) (hK : ∀ x y, |b x - b y| ≤ K * |x - y|) {α θ : ℝ} {p : ℤ} {q : ℕ}
    (hq : 0 < q) (hpq : IsCoprime p (q : ℤ)) (happ : |α - p / q| ≤ 1 / (q : ℝ) ^ 2)
    (hgood : ∀ k < q, b (θ + k * α) ≠ 0) :
    (q / K) * (Real.log (q + 2) - Real.log 2) ≤ ∑ k ∈ range q, 1 / |b (θ + k * α)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  set a : ℤ := ⌊(q : ℝ) * θ⌋ with ha
  set σ : ℕ → ℕ := fun k => ((a + k * p) % (q : ℤ)).toNat with hσ
  have hmod0 : ∀ k : ℕ, 0 ≤ (a + k * p) % (q : ℤ) := fun k => Int.emod_nonneg _ hqZ
  have hmodlt : ∀ k : ℕ, (a + k * p) % (q : ℤ) < q := fun k =>
    Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  have hσcast : ∀ k, ((σ k : ℕ) : ℤ) = (a + k * p) % (q : ℤ) := fun k =>
    Int.toNat_of_nonneg (hmod0 k)
  have hσlt : ∀ k, σ k < q := fun k => by have := hmodlt k; have := hσcast k; omega
  -- injectivity of `k ↦ (a + kp) mod q` on `[0, q)`
  have hσinj : Set.InjOn σ (range q : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    simp only [coe_range, Set.mem_Iio] at hk₁ hk₂
    have h1 : (a + k₁ * p) % (q : ℤ) = (a + k₂ * p) % (q : ℤ) := by
      rw [← hσcast, ← hσcast, heq]
    have h2 : (q : ℤ) ∣ ((k₁ : ℤ) - k₂) * p := by
      have e1 := Int.mul_ediv_add_emod (a + k₁ * p) q
      have e2 := Int.mul_ediv_add_emod (a + k₂ * p) q
      exact ⟨(a + k₁ * p) / q - (a + k₂ * p) / q, by linear_combination h1 - e1 + e2⟩
    have h3 : (q : ℤ) ∣ ((k₁ : ℤ) - k₂) := hpq.symm.dvd_of_dvd_mul_right h2
    have h4 : |(k₁ : ℤ) - k₂| < q := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd h3 h4
    omega
  have himage : (range q).image σ = range q := by
    apply eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨k, -, rfl⟩ := mem_image.1 hj
      exact mem_range.2 (hσlt k)
    · rw [card_image_of_injOn hσinj]
  -- the termwise bound
  have hterm : ∀ k ∈ range q, (q : ℝ) / (K * ((σ k : ℝ) + 2)) ≤ 1 / |b (θ + k * α)| := by
    intro k hk
    have hk' : k < q := mem_range.1 hk
    set z : ℤ := (a + k * p) / q
    have hdecomp := Int.mul_ediv_add_emod (a + k * p) q
    have hr : ((σ k : ℕ) : ℝ) = (((a + k * p) % (q : ℤ) : ℤ) : ℝ) := by
      rw [← hσcast]; norm_cast
    have hzR : (z : ℝ) = ((a : ℝ) + k * p - σ k) / q := by
      rw [hr]
      field_simp
      have := congrArg (fun t : ℤ => (t : ℝ)) hdecomp
      push_cast at this
      linarith
    have hρ0 : 0 ≤ (q : ℝ) * θ - a := by rw [ha]; linarith [Int.floor_le ((q : ℝ) * θ)]
    have hρ1 : (q : ℝ) * θ - a < 1 := by rw [ha]; linarith [Int.lt_floor_add_one ((q : ℝ) * θ)]
    have hkq : (k : ℝ) ≤ q := by exact_mod_cast hk'.le
    have herr : |(k : ℝ) * (α - p / q)| ≤ 1 / q := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
      calc (k : ℝ) * |α - p / q| ≤ q * (1 / (q : ℝ) ^ 2) :=
            mul_le_mul hkq happ (abs_nonneg _) hqR.le
        _ = 1 / q := by field_simp
    have hdist : |θ + k * α - z| ≤ ((σ k : ℝ) + 2) / q := by
      have e : θ + k * α - z = ((q : ℝ) * θ - a) / q + (σ k : ℝ) / q + k * (α - p / q) := by
        rw [hzR]; field_simp; ring
      rw [e]
      have hσ0 : (0 : ℝ) ≤ σ k := Nat.cast_nonneg _
      calc |((q : ℝ) * θ - a) / q + (σ k : ℝ) / q + k * (α - p / q)|
          ≤ |((q : ℝ) * θ - a) / q| + |(σ k : ℝ) / q| + |(k : ℝ) * (α - p / q)| :=
            abs_add_three _ _ _
        _ ≤ 1 / q + (σ k : ℝ) / q + 1 / q := by
            gcongr
            · rw [abs_of_nonneg (by positivity)]
              exact div_le_div_of_nonneg_right hρ1.le hqR.le
            · rw [abs_of_nonneg (by positivity)]
        _ = ((σ k : ℝ) + 2) / q := by ring
    have hbx := abs_le_of_zero hper h0 hK (θ + k * α) z
    have hbpos : 0 < |b (θ + k * α)| := abs_pos.2 (hgood k hk')
    have hle : |b (θ + k * α)| ≤ K * (((σ k : ℝ) + 2) / q) :=
      hbx.trans (mul_le_mul_of_nonneg_left hdist hK0.le)
    calc (q : ℝ) / (K * ((σ k : ℝ) + 2)) = 1 / (K * (((σ k : ℝ) + 2) / q)) := by
          field_simp
      _ ≤ 1 / |b (θ + k * α)| := one_div_le_one_div_of_le hbpos hle
  calc (q / K) * (Real.log (q + 2) - Real.log 2)
      ≤ (q / K) * ∑ j ∈ range q, 1 / ((j : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (log_sub_log_two_le_sum q) (by positivity)
    _ = ∑ j ∈ range q, (q : ℝ) / (K * ((j : ℝ) + 2)) := by
        rw [mul_sum]
        refine sum_congr rfl (fun j _ => ?_)
        field_simp
    _ = ∑ k ∈ range q, (q : ℝ) / (K * ((σ k : ℝ) + 2)) := by
        conv_lhs => rw [← himage]
        rw [sum_image hσinj]
    _ ≤ _ := sum_le_sum hterm

/-- Good rational approximations with arbitrarily large denominators: for irrational `α`
and any `Q`, there are coprime `p, q` with `q > Q` and `|α - p/q| ≤ 1/q²`. -/
lemma exists_large_good_denominator {α : ℝ} (hα : Irrational α) (Q : ℕ) :
    ∃ p : ℤ, ∃ q : ℕ, Q < q ∧ IsCoprime p (q : ℤ) ∧ |α - p / q| ≤ 1 / (q : ℝ) ^ 2 := by
  -- `c = min_{1 ≤ d ≤ Q} ‖dα‖ > 0`
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d → d ≤ Q →
      c ≤ SGD.SmallDivisors.nint (d * α) := by
    rcases Nat.eq_zero_or_pos Q with hQ | hQ
    · exact ⟨1, one_pos, fun d h1 h2 => by omega⟩
    · obtain ⟨d₀, hd₀, hmin⟩ := (Finset.Icc 1 Q).exists_min_image
        (fun d : ℕ => SGD.SmallDivisors.nint (d * α)) ⟨1, by simp; omega⟩
      refine ⟨SGD.SmallDivisors.nint (d₀ * α),
        SGD.SmallDivisors.nint_pos_of_irrational hα (by simp at hd₀; omega),
        fun d h1 h2 => hmin d (by simp; omega)⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc0
  obtain ⟨p, q, hq0, hqn, hcop, hpq⟩ := dirichlet_coprime α (n := n + 1) (by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  refine ⟨p, q, ?_, hcop, ?_⟩
  · by_contra hle
    push_neg at hle
    have h1 := hc q hq0 hle
    have h2 := SGD.SmallDivisors.nint_le (q * α) p
    have h3 : 1 / ((n + 1 : ℕ) + 1 : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
    linarith
  · have e : α - p / q = (q * α - p) / q := by field_simp
    rw [e, abs_div, abs_of_pos hqR, div_le_iff₀ hqR]
    have hqn' : (q : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hqn
    calc |(q : ℝ) * α - p| ≤ 1 / ((n + 1 : ℕ) + 1 : ℝ) := hpq
      _ ≤ 1 / q := one_div_le_one_div_of_le hqR (by linarith)
      _ = 1 / (q : ℝ) ^ 2 * q := by field_simp

/-! ### `S_*` and superlinearity (5.2) -/

/-- `S_*(L) = inf_θ ∑_{j<L} 1/|b(θ+jα)|`, the infimum over the phases whose first `L`
orbit points avoid the zeros of `b` (phases hitting a zero contribute `+∞` in the paper). -/
def Sstar (b : ℝ → ℝ) (α : ℝ) (L : ℕ) : ℝ :=
  ⨅ θ : {θ : ℝ // ∀ j < L, b (θ + j * α) ≠ 0}, ∑ j ∈ range L, 1 / |b (θ.1 + j * α)|

/-- Block splitting: `∑_{j<L} F j ≥ ∑_{i < L/q} ∑_{j<q} F(iq+j)` for `F ≥ 0`. -/
lemma sum_range_ge_blocks {F : ℕ → ℝ} (hF : ∀ j, 0 ≤ F j) (L q : ℕ) :
    ∑ i ∈ range (L / q), ∑ j ∈ range q, F (i * q + j) ≤ ∑ j ∈ range L, F j := by
  have hblocks : ∀ n : ℕ, ∑ i ∈ range n, ∑ j ∈ range q, F (i * q + j) =
      ∑ j ∈ range (n * q), F j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, show (n + 1) * q = n * q + q by ring, sum_range_add]
  rw [hblocks]
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.div_mul_le_self L q))
    (fun j _ _ => hF j)

/-- **(5.2), quantitative form.** For irrational `α` and `b` `1`-periodic, Lipschitz,
with `b(0) = 0`: for every `A` there is `L₀` such that `∑_{j<L} 1/|b(θ+jα)| ≥ A L` for all
`L ≥ L₀` and all phases `θ` whose first `L` orbit points avoid the zeros of `b`. -/
theorem superlinear {b : ℝ → ℝ} (hper : Function.Periodic b 1) (h0 : b 0 = 0) {K : ℝ}
    (hK : ∀ x y, |b x - b y| ≤ K * |x - y|) {α : ℝ} (hα : Irrational α) (A : ℝ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ θ : ℝ, (∀ j < L, b (θ + j * α) ≠ 0) →
      A * L ≤ ∑ j ∈ range L, 1 / |b (θ + j * α)| := by
  set K' := max K 1
  have hK'0 : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK' : ∀ x y, |b x - b y| ≤ K' * |x - y| := fun x y =>
    (hK x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  set A' := max A 0
  obtain ⟨p, q, hQq, hcop, happ⟩ :=
    exists_large_good_denominator hα ⌈2 * Real.exp (2 * A' * K')⌉₊
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  -- `(1/K') (ln(q+2) - ln 2) ≥ 2A'`
  have hlog : 2 * A' * K' ≤ Real.log (q + 2) - Real.log 2 := by
    rw [← Real.log_div (by positivity) (by norm_num), ← Real.log_exp (2 * A' * K')]
    apply Real.log_le_log (Real.exp_pos _)
    have := Nat.lt_of_ceil_lt hQq
    rw [le_div_iff₀ (by norm_num)]
    linarith
  refine ⟨2 * q, fun L hL θ hgood => ?_⟩
  have hF : ∀ j : ℕ, 0 ≤ 1 / |b (θ + (j : ℝ) * α)| := fun j => by positivity
  refine le_trans ?_ (sum_range_ge_blocks (F := fun j : ℕ => 1 / |b (θ + j * α)|) hF L q)
  have hblock : ∀ i ∈ range (L / q), (q / K') * (Real.log (q + 2) - Real.log 2) ≤
      ∑ j ∈ range q, 1 / |b (θ + ((i * q + j : ℕ) : ℝ) * α)| := by
    intro i hi
    have hi' : i < L / q := mem_range.1 hi
    have := orbit_sum_ge hper h0 hK'0 hK' (θ := θ + (i * q : ℕ) * α) hq0 hcop happ
      (fun k hk => by
        have hlt : i * q + k < L := by
          have h1 : (i + 1) * q ≤ L :=
            (Nat.mul_le_mul_right q (Nat.succ_le_of_lt hi')).trans (Nat.div_mul_le_self L q)
          nlinarith
        have := hgood (i * q + k) hlt
        push_cast at this ⊢
        rwa [show θ + ((i : ℝ) * q + k) * α = θ + (i : ℝ) * q * α + k * α by ring] at this)
    refine this.trans (le_of_eq (sum_congr rfl (fun j _ => ?_)))
    push_cast
    ring_nf
  have hsum := sum_le_sum hblock
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  refine le_trans ?_ hsum
  -- `A L ≤ ⌊L/q⌋ (q/K') (ln(q+2) - ln 2)`
  have hA : A ≤ A' := le_max_left _ _
  have hA0 : 0 ≤ A' := le_max_right _ _
  have hdiv : ((L : ℝ) / 2) ≤ ((L / q : ℕ) : ℝ) * q := by
    have h1 : L < (L / q + 1) * q := by
      nlinarith [Nat.div_add_mod L q, Nat.mod_lt L hq0]
    have h2 : (L : ℝ) < (((L / q : ℕ) : ℝ) + 1) * q := by exact_mod_cast h1
    have h3 : (2 * q : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  calc A * L ≤ A' * L := mul_le_mul_of_nonneg_right hA hL0
    _ = (L / 2) * (2 * A' * K') / K' := by first | (field_simp; ring) | field_simp
    _ ≤ ((L / q : ℕ) * q) * (Real.log (q + 2) - Real.log 2) / K' :=
        div_le_div_of_nonneg_right (mul_le_mul hdiv hlog
          (mul_nonneg (mul_nonneg two_pos.le hA0) hK'0.le) (by positivity)) hK'0.le
    _ = ((L / q : ℕ) : ℝ) * ((q / K') * (Real.log (q + 2) - Real.log 2)) := by
        first | (field_simp; ring) | field_simp

/-- **(5.2) (`sum-superlinear`).** `S_*(L)/L → ∞`, for irrational `α` and `b` `1`-periodic,
Lipschitz, with `b(0) = 0` and countably many zeros. -/
theorem tendsto_Sstar_div {b : ℝ → ℝ} (hper : Function.Periodic b 1) (h0 : b 0 = 0) {K : ℝ}
    (hK : ∀ x y, |b x - b y| ≤ K * |x - y|) (hZ : {x | b x = 0}.Countable) {α : ℝ}
    (hα : Irrational α) : Tendsto (fun L : ℕ => Sstar b α L / L) atTop atTop := by
  rw [tendsto_atTop]
  intro A
  obtain ⟨L₀, hL₀⟩ := superlinear hper h0 hK hα A
  filter_upwards [eventually_ge_atTop (max L₀ 1)] with L hL
  have hL1 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨θ₀, -, hθ₀⟩ := exists_good_phase hZ α 0 one_pos
  haveI : Nonempty {θ : ℝ // ∀ j < L, b (θ + j * α) ≠ 0} :=
    ⟨⟨θ₀, fun j _ => by simpa using hθ₀ j⟩⟩
  rw [le_div_iff₀ hL1]
  exact le_ciInf (fun θ => hL₀ L (le_of_max_le_left hL) θ.1 θ.2)

/-- `S_{+,m}` for the weights `1/|b(θ + kα)|` is an orbit sum starting at `θ + mα`. -/
lemma Splus_bw_eq (b : ℝ → ℝ) (α θ : ℝ) (L : ℕ) (m : ℤ) :
    Splus (bw b α θ) L m = ∑ j ∈ range L, 1 / |b ((θ + m * α) + j * α)| := by
  induction L with
  | zero => simp [Splus]
  | succ L ih =>
    rw [sum_range_succ, ← ih]
    simp only [Splus]
    rw [show m + ((L + 1 : ℕ) : ℤ) = (m + L) + 1 by push_cast; ring,
      sum_Ico_succ_right (by omega)]
    simp only [bw]
    push_cast
    congr 1
    ring_nf

/-- An orbit lower bound valid for all phases gives the hypothesis `S ≤ S_{+,m}` of
`infDist_sigmaM_le`. -/
lemma Splus_ge_of_orbit {b : ℝ → ℝ} {α : ℝ} {L : ℕ} {S : ℝ}
    (h : ∀ θ : ℝ, (∀ j < L, b (θ + j * α) ≠ 0) → S ≤ ∑ j ∈ range L, 1 / |b (θ + j * α)|) :
    ∀ θ : ℝ, (∀ k : ℤ, b (θ + k * α) ≠ 0) → ∀ m : ℤ, S ≤ Splus (bw b α θ) L m := by
  intro θ hθ m
  rw [Splus_bw_eq]
  refine h _ (fun j _ => ?_)
  have := hθ (m + j)
  push_cast at this
  rwa [show θ + ((m : ℝ) + j) * α = θ + m * α + j * α by ring] at this

/-! ### Bounded type: Lemma 5.1 -/

/-- `α` is of **bounded type** (badly approximable): `|qα - p| ≥ c/q` for all `q ≥ 1`. -/
def BoundedType (α : ℝ) : Prop :=
  ∃ c > 0, ∀ q : ℕ, 0 < q → ∀ p : ℤ, c / q ≤ |q * α - p|

/-- **Lemma 5.1 (`lemma-S`), (5.1).** Let `b` be `1`-periodic, Lipschitz, with `b(0) = 0`,
and `α` of bounded type.  Then there is `C > 0` such that for all `θ` and all integers
`L ≥ 2` (with the convention `1/0 = ∞`, i.e. for phases avoiding the zeros of `b`),
`∑_{k<L} 1/|b(αk+θ)| ≥ C L ln L`. -/
theorem lemma_S {b : ℝ → ℝ} (hper : Function.Periodic b 1) (h0 : b 0 = 0) {K : ℝ}
    (hK : ∀ x y, |b x - b y| ≤ K * |x - y|) {α : ℝ} (hα : BoundedType α) :
    ∃ C > 0, ∀ θ : ℝ, ∀ L : ℕ, 2 ≤ L → (∀ k < L, b (θ + k * α) ≠ 0) →
      C * L * Real.log L ≤ ∑ k ∈ range L, 1 / |b (θ + k * α)| := by
  obtain ⟨c, hc0, hc⟩ := hα
  set K' := max K 1
  have hK'0 : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK' : ∀ x y, |b x - b y| ≤ K' * |x - y| := fun x y =>
    (hK x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  set c' := min c 1
  have hc'0 : 0 < c' := lt_min hc0 one_pos
  have hc'1 : c' ≤ 1 := min_le_right _ _
  refine ⟨c' * (c' / 2) / K', by positivity, fun θ L hL hgood => ?_⟩
  obtain ⟨p, q, hq0, hqL, hcop, hpq⟩ := dirichlet_coprime α (n := L) (by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  -- `q ≥ c (L+1) ≥ c' L`
  have hqlow : c' * L ≤ q := by
    have h1 := hc q hq0 p
    have h2 : c / q ≤ 1 / ((L : ℝ) + 1) := h1.trans hpq
    rw [div_le_div_iff₀ hqR (by positivity)] at h2
    have : c' ≤ c := min_le_left _ _
    nlinarith
  have happ : |α - p / q| ≤ 1 / (q : ℝ) ^ 2 := by
    have e : α - p / q = (q * α - p) / q := by field_simp
    rw [e, abs_div, abs_of_pos hqR, div_le_iff₀ hqR]
    have hqL' : (q : ℝ) ≤ L := by exact_mod_cast hqL
    calc |(q : ℝ) * α - p| ≤ 1 / ((L : ℝ) + 1) := hpq
      _ ≤ 1 / q := one_div_le_one_div_of_le hqR (by linarith)
      _ = 1 / (q : ℝ) ^ 2 * q := by field_simp
  have horb := orbit_sum_ge hper h0 hK'0 hK' hq0 hcop happ
    (fun k hk => hgood k (lt_of_lt_of_le hk hqL))
  have hsub : ∑ k ∈ range q, 1 / |b (θ + k * α)| ≤ ∑ k ∈ range L, 1 / |b (θ + k * α)| :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hqL) (fun k _ _ => by positivity)
  refine le_trans ?_ (horb.trans hsub)
  -- `ln((q+2)/2) ≥ ln(1 + c' L/2) ≥ (c'/2) ln L`
  have hBern : (L : ℝ) ^ (c' / 2) ≤ 1 + c' / 2 * ((L : ℝ) - 1) := by
    have := rpow_one_add_le_one_add_mul_self (s := (L : ℝ) - 1) (by linarith)
      (p := c' / 2) (by positivity) (by linarith)
    simpa using this
  have hlogL : c' / 2 * Real.log L ≤ Real.log (q + 2) - Real.log 2 := by
    rw [← Real.log_div (by positivity) (by norm_num), ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _)
    have : (1 : ℝ) + c' / 2 * ((L : ℝ) - 1) ≤ (q + 2) / 2 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    exact hBern.trans this
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  calc c' * (c' / 2) / K' * L * Real.log L = (c' * L) / K' * (c' / 2 * Real.log L) := by ring
    _ ≤ q / K' * (Real.log (q + 2) - Real.log 2) :=
        mul_le_mul (div_le_div_of_nonneg_right hqlow hK'0.le) hlogL
          (mul_nonneg (by positivity) hlog0) (by positivity)

/-! ### Theorem 5.2 -/

/-- Lower bound `S_{+,m} ≥ L/M` from `|b| ≤ M` ("the trivial estimate `S_min ≥ CL`",
case 2 of the proof). -/
lemma Splus_ge_trivial {b : ℝ → ℝ} {M : ℝ} (hM0 : 0 < M) (hM : ∀ x, |b x| ≤ M) (α : ℝ)
    (L : ℕ) : ∀ θ : ℝ, (∀ k : ℤ, b (θ + k * α) ≠ 0) → ∀ m : ℤ,
      L / M ≤ Splus (bw b α θ) L m := by
  refine Splus_ge_of_orbit (fun θ hθ => ?_)
  calc (L : ℝ) / M = ∑ j ∈ range L, 1 / M := by
        rw [sum_const, card_range, nsmul_eq_mul, div_eq_mul_one_div]
    _ ≤ _ := sum_le_sum (fun j hj => one_div_le_one_div_of_le
        (abs_pos.2 (hθ j (mem_range.1 hj))) (hM _))

/-- Floor bounds: for `x ≥ 1`, `x/2 ≤ ⌊x⌋₊ ≤ x` and `⌊x⌋₊ ≥ 1`. -/
lemma floor_bounds {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have h2 := Nat.lt_floor_add_one x
  have h3 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
  exact ⟨h1, by linarith, Nat.floor_le (by linarith)⟩

/-- **Theorem 5.2, (5.7) (`cgeneral`).** For `v, b` bounded and Lipschitz, with countably
many zeros of `b`, there is `C` such that for all `α, β` with `|α - β| ≤ 1` and every
`E ∈ σ(M_{v,b,α})`, `dist(E, σ(M_{v,b,β})) ≤ C |α - β|^{1/2}`. -/
theorem cgeneral {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α β : ℝ, |α - β| ≤ 1 → ∀ E ∈ sigmaM v b α,
      Metric.infDist E (sigmaM v b β) ≤ C * √|α - β| := by
  obtain ⟨Mb, hMb⟩ := hb
  set M := max Mb 1
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM : ∀ x, |b x| ≤ M := fun x => (hMb x).trans (le_max_left _ _)
  have hb' : BddFun b := ⟨Mb, hMb⟩
  refine ⟨(2 * Kb + Kv) + 8 * √2 * M, by positivity, fun α β hδ1 E hE => ?_⟩
  set δ := |α - β|
  rcases (abs_nonneg (α - β)).lt_or_eq with hδ0 | hδ0
  · set s := √δ
    have hs0 : 0 < s := Real.sqrt_pos.2 hδ0
    have hs1 : s ≤ 1 := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hδ1
    have hss : s * s = δ := Real.mul_self_sqrt hδ0.le
    obtain ⟨hL1, hL2, hL3⟩ := floor_bounds (x := 1 / s) (by rw [le_div_iff₀ hs0]; linarith)
    set L := ⌊1 / s⌋₊
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
    have h := infDist_sigmaM_le hv hb' hKb hKv hLb hLv hZ hL1 (S := L / M) (by positivity)
      (Splus_ge_trivial hM0 hM α L) hE β
    refine h.trans ?_
    have t1 : (2 * Kb + Kv) * L * δ ≤ (2 * Kb + Kv) * s := by
      rw [← hss]
      have : (L : ℝ) * s ≤ 1 := by rwa [le_div_iff₀ hs0] at hL3
      have hK0 : 0 ≤ 2 * Kb + Kv := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hK0 hs0.le)]
    have t2 : 4 * √2 / (L / M) ≤ 8 * √2 * M * s := by
      rw [div_div_eq_mul_div, div_le_iff₀ hLpos]
      have : 1 ≤ 2 * s * L := by
        have := hL2; rw [div_div, div_le_iff₀ (by positivity)] at this; linarith
      have h2 : 0 ≤ 4 * √2 * M := by positivity
      nlinarith
    linarith
  · have hαβ : α = β := by
      have : |α - β| = 0 := hδ0.symm
      linarith [abs_eq_zero.1 this]
    rw [← hαβ, Metric.infDist_zero_of_mem hE]
    positivity

/-- The convergents `p_n/q_n` (`CAH.p`, `CAH.q`) are the Mathlib convergents. -/
lemma convs_eq (α : ℝ) (n : ℕ) : (GenContFract.of α).convs n = p α n / q α n := rfl

/-- `|α - p_n/q_n| ≤ 1/q_n² ≤ 1` for irrational `α`. -/
lemma abs_sub_pq_le {α : ℝ} (hα : Irrational α) (n : ℕ) :
    |α - p α n / q α n| ≤ 1 / (q α n) ^ 2 := by
  have h := SGD.abs_sub_convs_le' hα n
  rw [convs_eq] at h
  have hq := SGD.cfGrowth hα
  have h1 := hq.pos n
  have h2 : q α n ≤ q α (n + 1) := GenContFract.of_den_mono
  refine h.trans (one_div_le_one_div_of_le (pow_pos h1 2) ?_)
  rw [sq]
  exact mul_le_mul_of_nonneg_left h2 h1.le

lemma abs_sub_pq_le_one {α : ℝ} (hα : Irrational α) (n : ℕ) : |α - p α n / q α n| ≤ 1 := by
  refine (abs_sub_pq_le hα n).trans ?_
  have := (SGD.cfGrowth hα).one_le n
  rw [div_le_one (pow_pos (by linarith) 2)]
  nlinarith

/-- **(5.7) for the canonical approximants.** For irrational `α` and every
`E ∈ σ(M_{v,b,α})` there is `E' ∈ σ(M_{v,b,p_n/q_n})` with
`|E - E'| ≤ C |α - p_n/q_n|^{1/2}`, `n = 1, 2, …`. -/
theorem cgeneral_convergents {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable) {α : ℝ}
    (hα : Irrational α) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ E ∈ sigmaM v b α, ∃ E' ∈ sigmaM v b (p α n / q α n),
      |E - E'| ≤ C * √|α - p α n / q α n| := by
  obtain ⟨C, -, hC⟩ := cgeneral hv hb hKb hKv hLb hLv hZ
  exact ⟨C, fun n E hE => exists_mem_sigmaM_of_infDist_le hv hb
    (hC α _ (abs_sub_pq_le_one hα n) E hE)⟩

/-- Shift of the zero to the origin: `b̃(x) = b(x + x₀)`. -/
lemma superlinear_of_zero {b : ℝ → ℝ} (hper : Function.Periodic b 1) {x₀ : ℝ} (h0 : b x₀ = 0)
    {K : ℝ} (hK : ∀ x y, |b x - b y| ≤ K * |x - y|) {α : ℝ} (hα : Irrational α) (A : ℝ) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ θ : ℝ, (∀ j < L, b (θ + j * α) ≠ 0) →
      A * L ≤ ∑ j ∈ range L, 1 / |b (θ + j * α)| := by
  have hper' : Function.Periodic (fun x => b (x + x₀)) 1 := fun x => by
    show b (x + 1 + x₀) = b (x + x₀)
    rw [show x + 1 + x₀ = (x + x₀) + 1 by ring]; exact hper _
  have hK' : ∀ x y, |b (x + x₀) - b (y + x₀)| ≤ K * |x - y| := fun x y => by
    have := hK (x + x₀) (y + x₀); rwa [show x + x₀ - (y + x₀) = x - y by ring] at this
  obtain ⟨L₀, hL₀⟩ := superlinear hper' (by simpa using h0) hK' hα A
  refine ⟨L₀, fun L hL θ hθ => ?_⟩
  have := hL₀ L hL (θ - x₀) (fun j hj => by
    show b (θ - x₀ + j * α + x₀) ≠ 0
    rw [show θ - x₀ + j * α + x₀ = θ + j * α by ring]; exact hθ j hj)
  refine this.trans (le_of_eq (sum_congr rfl fun j _ => ?_))
  show 1 / |b (θ - x₀ + j * α + x₀)| = _
  rw [show θ - x₀ + j * α + x₀ = θ + j * α by ring]

/-- **Theorem 5.2, (5.9) (`csingular`), quantitative form.** If `b` is `1`-periodic with a
zero, Lipschitz, with countably many zeros, `v` bounded Lipschitz, and `α` irrational,
then for every `η > 0` there is `δ₀ > 0` such that `|α - β| < δ₀` implies
`dist(E, σ(M_{v,b,β})) ≤ η |α - β|^{1/2}` for all `E ∈ σ(M_{v,b,α})`. -/
theorem csingular {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable)
    (hper : Function.Periodic b 1) (hzero : ∃ x₀, b x₀ = 0) {α : ℝ} (hα : Irrational α) :
    ∀ η > 0, ∃ δ₀ > 0, ∀ β : ℝ, |α - β| < δ₀ → ∀ E ∈ sigmaM v b α,
      Metric.infDist E (sigmaM v b β) ≤ η * √|α - β| := by
  intro η hη
  obtain ⟨x₀, hx₀⟩ := hzero
  set K := 2 * Kb + Kv
  have hK0 : 0 ≤ K := by positivity
  have hK8 : 0 < K + 8 * √2 := by have := Real.sqrt_nonneg 2; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (K + 8 * √2) / η := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact div_pos hK8 hη
  obtain ⟨L₀, hL₀⟩ := superlinear_of_zero hper hx₀ hLb hα (t ^ 2)
  refine ⟨1 / (t ^ 2 * ((L₀ : ℝ) + 1) ^ 2), by positivity, fun β hδ E hE => ?_⟩
  set δ := |α - β|
  rcases (abs_nonneg (α - β)).lt_or_eq with hδ0 | hδ0
  · set s := √δ
    have hs0 : 0 < s := Real.sqrt_pos.2 hδ0
    have hss : s * s = δ := Real.mul_self_sqrt hδ0.le
    -- `x = 1/(t s) > L₀ + 1`
    have hx : (L₀ : ℝ) + 1 < 1 / (t * s) := by
      rw [lt_div_iff₀ (by positivity)]
      have h1 : δ * (t ^ 2 * ((L₀ : ℝ) + 1) ^ 2) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hδ
      have h2 : (((L₀ : ℝ) + 1) * (t * s)) ^ 2 < 1 := by
        rw [← hss] at h1
        have e : (((L₀ : ℝ) + 1) * (t * s)) ^ 2 = s * s * (t ^ 2 * ((L₀ : ℝ) + 1) ^ 2) := by
          ring
        linarith
      nlinarith [sq_nonneg (((L₀ : ℝ) + 1) * (t * s)), show 0 ≤ ((L₀ : ℝ) + 1) * (t * s) by
        positivity]
    obtain ⟨hL1, hL2, hL3⟩ := floor_bounds (x := 1 / (t * s))
      (by linarith [Nat.cast_nonneg (α := ℝ) L₀])
    set L := ⌊1 / (t * s)⌋₊
    have hLL₀ : L₀ ≤ L := by
      have : (L₀ : ℝ) ≤ L := by
        have := Nat.lt_floor_add_one (1 / (t * s)); linarith
      exact_mod_cast this
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
    have h := infDist_sigmaM_le hv hb hKb hKv hLb hLv hZ hL1 (S := t ^ 2 * L) (by positivity)
      (Splus_ge_of_orbit (fun θ hθ => hL₀ L hLL₀ θ hθ)) hE β
    refine h.trans ?_
    have hLts : (L : ℝ) * (t * s) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hL3
    have hLts2 : 1 ≤ 2 * (L : ℝ) * (t * s) := by
      have := hL2; rw [div_div, div_le_iff₀ (by positivity)] at this; linarith
    have t1 : K * L * δ ≤ K * s / t := by
      rw [← hss, le_div_iff₀ ht0]
      nlinarith [mul_le_mul_of_nonneg_left hLts (mul_nonneg hK0 hs0.le)]
    have t2 : 4 * √2 / (t ^ 2 * L) ≤ 8 * √2 * s / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]
      have h3 := mul_le_mul_of_nonneg_left hLts2 (show 0 ≤ 4 * √2 * t by positivity)
      nlinarith [h3]
    have e : K * s / t + 8 * √2 * s / t = η * s := by
      rw [ht]; first | (field_simp; ring) | field_simp
    linarith
  · have hαβ : α = β := by
      have : |α - β| = 0 := hδ0.symm
      linarith [abs_eq_zero.1 this]
    rw [← hαβ, Metric.infDist_zero_of_mem hE]
    positivity

/-- `|α - p_n/q_n| → 0`. -/
lemma tendsto_abs_sub_pq {α : ℝ} (hα : Irrational α) :
    Tendsto (fun n => |α - p α n / q α n|) atTop (𝓝 0) := by
  have hq := (SGD.cfGrowth hα).tendsto_atTop
  have h2 : Tendsto (fun n => (q α n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hq
  refine squeeze_zero (fun n => abs_nonneg _) (fun n => (abs_sub_pq_le hα n).trans ?_) h2
  have h1 := (SGD.cfGrowth hα).one_le n
  rw [one_div]
  exact inv_anti₀ (by linarith) (by nlinarith)

/-- **(5.9) (`csingular`) for the canonical approximants:**
`r_n = sup_{E ∈ σ(M_α)} dist(E, σ(M_{p_n/q_n})) = o(|α - p_n/q_n|^{1/2})`, i.e. for every
`η > 0`, eventually `dist(E, σ(M_{p_n/q_n})) ≤ η |α - p_n/q_n|^{1/2}` for all
`E ∈ σ(M_α)`. -/
theorem csingular_convergents {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable)
    (hper : Function.Periodic b 1) (hzero : ∃ x₀, b x₀ = 0) {α : ℝ} (hα : Irrational α) :
    ∀ η > 0, ∀ᶠ n in atTop, ∀ E ∈ sigmaM v b α,
      Metric.infDist E (sigmaM v b (p α n / q α n)) ≤ η * √|α - p α n / q α n| := by
  intro η hη
  obtain ⟨δ₀, hδ₀, h⟩ := csingular hv hb hKb hKv hLb hLv hZ hper hzero hα η hη
  filter_upwards [(tendsto_abs_sub_pq hα).eventually (gt_mem_nhds hδ₀)] with n hn
  exact h _ hn

/-- **Theorem 5.2, (5.8) (`cbounded`).** If moreover `α` is of bounded type, there are
`C, δ₀ > 0` with
`dist(E, σ(M_{v,b,β})) ≤ C |α-β|^{1/2} |ln|α-β||^{-1/2}` whenever `0 < |α - β| < δ₀`. -/
theorem cbounded {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable)
    (hper : Function.Periodic b 1) (hzero : ∃ x₀, b x₀ = 0) {α : ℝ} (hα : BoundedType α) :
    ∃ C > 0, ∃ δ₀ > 0, ∀ β : ℝ, 0 < |α - β| → |α - β| < δ₀ → ∀ E ∈ sigmaM v b α,
      Metric.infDist E (sigmaM v b β) ≤ C * √|α - β| / √(abs (Real.log |α - β|)) := by
  obtain ⟨x₀, hx₀⟩ := hzero
  -- Lemma 5.1 for `b(· + x₀)`
  have hper' : Function.Periodic (fun x => b (x + x₀)) 1 := fun x => by
    show b (x + 1 + x₀) = b (x + x₀)
    rw [show x + 1 + x₀ = (x + x₀) + 1 by ring]; exact hper _
  have hK' : ∀ x y, |b (x + x₀) - b (y + x₀)| ≤ Kb * |x - y| := fun x y => by
    have := hLb (x + x₀) (y + x₀); rwa [show x + x₀ - (y + x₀) = x - y by ring] at this
  obtain ⟨C₁, hC₁, hS⟩ := lemma_S hper' (by simpa using hx₀) hK' hα
  have hS' : ∀ θ : ℝ, ∀ L : ℕ, 2 ≤ L → (∀ k < L, b (θ + k * α) ≠ 0) →
      C₁ * L * Real.log L ≤ ∑ k ∈ range L, 1 / |b (θ + k * α)| := by
    intro θ L hL hθ
    have := hS (θ - x₀) L hL (fun k hk => by
      show b (θ - x₀ + k * α + x₀) ≠ 0
      rw [show θ - x₀ + k * α + x₀ = θ + k * α by ring]; exact hθ k hk)
    refine this.trans (le_of_eq (sum_congr rfl fun j _ => ?_))
    show 1 / |b (θ - x₀ + j * α + x₀)| = _
    rw [show θ - x₀ + j * α + x₀ = θ + j * α by ring]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * Kb + Kv := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨K + 32 * √2 / C₁ + 1, by positivity, Real.exp (-64), Real.exp_pos _,
    fun β hδ0 hδ E hE => ?_⟩
  set δ := |α - β|
  set u := -Real.log δ
  have hlogδ : Real.log δ < -64 := by
    rw [← Real.log_exp (-64)]; exact Real.log_lt_log hδ0 hδ
  have hu64 : 64 < u := by simp only [u]; linarith
  have hu0 : 0 < u := by linarith
  have habs : |Real.log δ| = u := abs_of_neg (by linarith)
  rw [habs]
  set s := √δ
  set w := √u
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ0
  have hw0 : 0 < w := Real.sqrt_pos.2 hu0
  have hss : s * s = δ := Real.mul_self_sqrt hδ0.le
  have hww : w * w = u := Real.mul_self_sqrt hu0.le
  have hw8 : 8 < w := by
    rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hu64
  -- `log u ≤ 2 w`
  have hlogu : Real.log u ≤ 2 * w := by
    rw [← hww, Real.log_mul hw0.ne' hw0.ne']
    have := Real.log_le_sub_one_of_pos hw0
    linarith
  -- `u ≤ 2/s`, i.e. `-log δ ≤ 2/√δ`
  have hus : u * s ≤ 2 := by
    have h1 : Real.log δ = 2 * Real.log s := by
      rw [← hss, Real.log_mul hs0.ne' hs0.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hs0)
    rw [Real.log_inv] at h2
    have h3 : u = 2 * (-Real.log s) := by simp only [u]; rw [h1]; ring
    rw [h3]
    have h4 : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0.ne'
    have hs1 : s ≤ 1 := by
      have : δ ≤ 1 := le_trans hδ.le (by rw [Real.exp_le_one_iff]; norm_num)
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt this
    nlinarith
  -- `x = 1/(s w)`
  set x := 1 / (s * w)
  have hsw : 0 < s * w := by positivity
  have hx4 : 4 ≤ x := by
    rw [le_div_iff₀ hsw]
    -- `s w ≤ 1/4`: `(s w)² = δ u ≤ 2 s ≤ ...`
    have h1 : (s * w) ^ 2 ≤ 2 * s := by
      have : (s * w) ^ 2 = s * (u * s) := by rw [mul_pow, sq, sq, hww]; ring
      rw [this]; nlinarith
    have hs_small : s ≤ 1 / 32 := by
      have : 8 * (u * s) ≤ u * s * w := by nlinarith
      nlinarith
    nlinarith [sq_nonneg (s * w)]
  obtain ⟨hL1, hL2, hL3⟩ := floor_bounds (x := x) (by linarith)
  set L := ⌊x⌋₊
  have hL2' : 2 ≤ L := by
    have : (2 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hLpos : (0 : ℝ) < L := by positivity
  -- `log L ≥ u/4`
  have hlogL : u / 4 ≤ Real.log L := by
    have h1 : Real.log (x / 2) ≤ Real.log L := Real.log_le_log (by positivity) hL2
    have h2 : Real.log (x / 2) = u / 2 - Real.log u / 2 - Real.log 2 := by
      simp only [x]
      rw [Real.log_div (by positivity) (by norm_num), Real.log_div (by norm_num) hsw.ne',
        Real.log_one, Real.log_mul hs0.ne' hw0.ne']
      have e1 : Real.log s = -u / 2 := by
        have : Real.log δ = 2 * Real.log s := by
          rw [← hss, Real.log_mul hs0.ne' hs0.ne']; ring
        simp only [u]; linarith
      have e2 : Real.log w = Real.log u / 2 := by
        have : Real.log u = 2 * Real.log w := by
          rw [← hww, Real.log_mul hw0.ne' hw0.ne']; ring
        linarith
      rw [e1, e2]; ring
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    nlinarith
  have hlogLpos : 0 < Real.log L := by linarith
  have hSpos : 0 < C₁ * L * Real.log L := by positivity
  have h := infDist_sigmaM_le hv hb hKb hKv hLb hLv hZ (by omega : 1 ≤ L)
    (S := C₁ * L * Real.log L) hSpos
    (Splus_ge_of_orbit (fun θ hθ => hS' θ L hL2' hθ)) hE β
  rw [← hK] at h
  refine h.trans ?_
  have hLx : (L : ℝ) * (s * w) ≤ 1 := by rwa [le_div_iff₀ hsw] at hL3
  have hLx2 : 1 ≤ 2 * (L : ℝ) * (s * w) := by
    have := hL2; simp only [x] at this
    rw [div_div, div_le_iff₀ (by positivity)] at this; linarith
  have t1 : K * L * δ ≤ K * s / w := by
    rw [← hss, le_div_iff₀ hw0]
    nlinarith [mul_le_mul_of_nonneg_left hLx (mul_nonneg hK0 hs0.le)]
  have t2 : 4 * √2 / (C₁ * L * Real.log L) ≤ 32 * √2 / C₁ * s / w := by
    rw [div_le_div_iff₀ hSpos hw0]
    have h2 : 0 ≤ 4 * √2 := by positivity
    have hC : 32 * √2 / C₁ * s * (C₁ * L * Real.log L) = 32 * √2 * (L * s * Real.log L) := by
      first | (field_simp; ring) | field_simp
    rw [hC]
    -- `L s log L ≥ L s u/4 ≥ w/8`
    have h3 : (L : ℝ) * s * (u / 4) ≤ L * s * Real.log L :=
      mul_le_mul_of_nonneg_left hlogL (by positivity)
    have h4 : w / 8 ≤ (L : ℝ) * s * (u / 4) := by
      rw [← hww]; nlinarith
    nlinarith
  have e : K * s / w + 32 * √2 / C₁ * s / w ≤ (K + 32 * √2 / C₁ + 1) * s / w := by
    have h0 : 0 ≤ s / w := by positivity
    have e' : (K + 32 * √2 / C₁ + 1) * s / w = K * s / w + 32 * √2 / C₁ * s / w + s / w := by
      ring
    linarith
  linarith

end CAH
