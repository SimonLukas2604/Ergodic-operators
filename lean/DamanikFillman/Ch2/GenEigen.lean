/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.4  Spectrum and generalized eigenfunctions  (book pp. 159–165)

## Main definitions and results
* **Definition 2.4.1**: `DF.IsGenEigenfun`, `DF.genEigSet V δ` (`G_δ`), `DF.genEigAll V` (`G`).
* **Theorem 2.4.2 (a)** (Sch'nol): `DF.genEig_mem_spectrum` — every generalized eigenvalue
  belongs to `σ(H)`; `DF.genEigAll_subset_spectrum`, `DF.closure_genEigAll_subset_spectrum`.

## Proof
The proof follows the book: the cut-offs `u_L = P_{[-L,L]} u` satisfy
`‖(H - E) u_L‖² ≲ ‖u_{L+1}‖² - ‖u_{L-1}‖²` (2.4.4).  Instead of extracting a Weyl sequence we
argue by contradiction directly with the resolvent: if `E ∈ ρ(H)`, then
`‖u_L‖ ≤ ‖(H - E)⁻¹‖ ‖(H - E) u_L‖` forces `‖u_{L+1}‖² ≥ (1 + c) ‖u_{L-1}‖²`, i.e.
exponential growth, contradicting the polynomial bound (2.4.3).
-/
import DamanikFillman.Ch2.Green

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open L2 Filter Topology Metric

namespace DF

variable {V : ℤ → ℝ}

/-- **Definition 2.4.1**: `u` is a generalized eigenfunction of `H` at energy `z` with
exponent `δ`: a nontrivial solution of (2.2.2) with `|u(n)| ≤ C (1 + |n|)^δ` (2.4.1). -/
def IsGenEigenfun (V : ℤ → ℝ) (z : ℂ) (δ : ℝ) (u : ℤ → ℂ) : Prop :=
  u ≠ 0 ∧ IsSolution V z u ∧ ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|) ^ δ

/-- `G_δ`: energies admitting a generalized eigenfunction with exponent `δ`. -/
def genEigSet (V : ℤ → ℝ) (δ : ℝ) : Set ℂ := {z | ∃ u, IsGenEigenfun V z δ u}

/-- `G = ⋃_{δ > 0} G_δ`: the generalized eigenvalues. -/
def genEigAll (V : ℤ → ℝ) : Set ℂ := ⋃ δ ∈ Set.Ioi (0 : ℝ), genEigSet V δ

/-- The cut-off `P_{[-L, L]} u` as a function. -/
def cutoff (u : ℤ → ℂ) (L : ℕ) (m : ℤ) : ℂ := if -(L : ℤ) ≤ m ∧ m ≤ L then u m else 0

lemma memℓp_cutoff (u : ℤ → ℂ) (L : ℕ) : Memℓp (cutoff u L) 2 := by
  apply memℓp_of_sqSum
  · have : ∀ n, (L : ℤ) + 1 ≤ n → cutoff u L n = (fun _ => (0 : ℂ)) n := by
      intro n hn; simp only [cutoff]; rw [if_neg (by omega)]
    rw [sqSumTop_iff_of_eventually this]; simp [SqSumTop]
  · have : ∀ n, n ≤ -(L : ℤ) - 1 → cutoff u L n = (fun _ => (0 : ℂ)) n := by
      intro n hn; simp only [cutoff]; rw [if_neg (by omega)]
    rw [sqSumBot_iff_of_eventually this]; simp [SqSumBot]

/-- `u_L` as a vector in `ℓ²(ℤ)`. -/
def cutL (u : ℤ → ℂ) (L : ℕ) : L2 ℤ := ⟨cutoff u L, memℓp_cutoff u L⟩

lemma cutL_apply (u : ℤ → ℂ) (L : ℕ) (m : ℤ) : cutL u L m = cutoff u L m := rfl

/-- The action of `H - z` on the cut-off (computation behind (2.4.4)). -/
lemma cutoff_eq {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) {L : ℕ} (hL : 1 ≤ L) (m : ℤ) :
    cutoff u L (m + 1) + cutoff u L (m - 1) + (V m : ℂ) * cutoff u L m - z * cutoff u L m =
      (if m = L + 1 then u L else 0) - (if m = L then u (L + 1) else 0) -
        (if m = -L then u (-L - 1) else 0) + (if m = -L - 1 then u (-L) else 0) := by
  have h := hu m
  simp only [cutoff]
  rcases (show m ≤ -L - 2 ∨ m = -L - 1 ∨ m = -L ∨ (-(L : ℤ) < m ∧ m < L) ∨ m = L ∨
      m = L + 1 ∨ (L : ℤ) + 2 ≤ m by omega) with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
  · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos h1]
    rw [h1]; ring_nf
  · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_pos h1, if_neg (by omega)]
    subst h1
    rw [show -(L : ℤ) + 1 = -L + 1 by ring] at *
    linear_combination h
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    linear_combination h
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
      if_pos h1, if_neg (by omega), if_neg (by omega)]
    subst h1
    linear_combination h
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos h1,
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    subst h1; ring_nf
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring

lemma algebraMap_apply_L2'' (z : ℂ) (ψ : L2 ℤ) : (algebraMap ℂ Op z) ψ = z • ψ := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- (2.4.4)-type bound: `‖(H - z) u_L‖ ≤ |u(L)| + |u(L+1)| + |u(-L)| + |u(-L-1)|`. -/
lemma norm_sub_cutL_le (hV : BddPot V) {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) {L : ℕ}
    (hL : 1 ≤ L) :
    ‖(schr V - algebraMap ℂ Op z) (cutL u L)‖ ≤
      ‖u L‖ + ‖u (L + 1)‖ + ‖u (-L)‖ + ‖u (-L - 1)‖ := by
  have heq : (schr V - algebraMap ℂ Op z) (cutL u L) =
      u L • dlt (L + 1) - u (L + 1) • dlt L - u (-L - 1) • dlt (-L) + u (-L) • dlt (-L - 1) := by
    ext m
    simp only [ContinuousLinearMap.sub_apply, algebraMap_apply_L2'', lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, schr_apply hV, cutL_apply, lp.coeFn_add,
      Pi.add_apply, dlt_apply]
    simp only [mul_ite, mul_one, mul_zero]
    exact cutoff_eq hu hL m
  have key : ∀ a b c d : L2 ℤ, ‖a - b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have h1 := norm_add_le (a - b - c) d
    have h2 := norm_sub_le (a - b) c
    have h3 := norm_sub_le a b
    linarith
  rw [heq]
  refine (key _ _ _ _).trans ?_
  simp only [norm_smul, norm_dlt, mul_one]
  linarith

/-- `s(L) = ‖u_L‖²`. -/
def cutNorm (u : ℤ → ℂ) (L : ℕ) : ℝ := ‖cutL u L‖ ^ 2

lemma cutNorm_eq (u : ℤ → ℂ) (L : ℕ) : cutNorm u L = ∑' m, ‖cutoff u L m‖ ^ 2 := by
  rw [cutNorm, norm_sq_eq_tsum]; rfl

lemma summable_cutoff (u : ℤ → ℂ) (L : ℕ) : Summable fun m => ‖cutoff u L m‖ ^ 2 :=
  summable_norm_sq (cutL u L)

lemma cutNorm_mono (u : ℤ → ℂ) {L L' : ℕ} (h : L ≤ L') : cutNorm u L ≤ cutNorm u L' := by
  rw [cutNorm_eq, cutNorm_eq]
  refine (summable_cutoff u L).tsum_le_tsum (fun m => ?_) (summable_cutoff u L')
  simp only [cutoff]
  split_ifs with h1 h2 <;> first | exact le_rfl | (exfalso; omega) | simp

lemma cutNorm_diff (u : ℤ → ℂ) {L : ℕ} (hL : 1 ≤ L) :
    cutNorm u (L + 1) - cutNorm u (L - 1) =
      ‖u L‖ ^ 2 + ‖u (L + 1)‖ ^ 2 + ‖u (-L)‖ ^ 2 + ‖u (-L - 1)‖ ^ 2 := by
  rw [cutNorm_eq, cutNorm_eq, ← (summable_cutoff u (L + 1)).tsum_sub (summable_cutoff u (L - 1))]
  have hpt : ∀ m : ℤ, ‖cutoff u (L + 1) m‖ ^ 2 - ‖cutoff u (L - 1) m‖ ^ 2 =
      (if m = L then ‖u L‖ ^ 2 else 0) + (if m = L + 1 then ‖u (L + 1)‖ ^ 2 else 0) +
        (if m = -L then ‖u (-L)‖ ^ 2 else 0) + (if m = -L - 1 then ‖u (-L - 1)‖ ^ 2 else 0) := by
    intro m
    simp only [cutoff]
    push_cast
    rw [Nat.cast_sub hL]
    push_cast
    rcases (show m ≤ -L - 2 ∨ m = -L - 1 ∨ m = -L ∨ (-(L : ℤ) < m ∧ m < L) ∨ m = L ∨
      m = L + 1 ∨ (L : ℤ) + 2 ≤ m by omega) with h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]; simp
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos h1, h1]; simp
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos h1, if_neg (by omega), h1]; simp
    · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]; simp
    · rw [if_pos (by omega), if_neg (by omega), if_pos h1, if_neg (by omega),
        if_neg (by omega), if_neg (by omega), h1]; simp
    · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos h1,
        if_neg (by omega), if_neg (by omega), h1]; simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]; simp
  simp only [hpt]
  have s1 := (hasSum_ite_eq (L : ℤ) (‖u L‖ ^ 2))
  have s2 := (hasSum_ite_eq ((L : ℤ) + 1) (‖u (L + 1)‖ ^ 2))
  have s3 := (hasSum_ite_eq (-(L : ℤ)) (‖u (-L)‖ ^ 2))
  have s4 := (hasSum_ite_eq (-(L : ℤ) - 1) (‖u (-L - 1)‖ ^ 2))
  exact (((s1.add s2).add s3).add s4).tsum_eq

/-- The polynomial bound (2.4.3). -/
lemma cutNorm_le {u : ℤ → ℂ} {C δ : ℝ} (hδ : 0 ≤ δ) (hC : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|) ^ δ)
    (L : ℕ) : cutNorm u L ≤ C ^ 2 * (1 + L) ^ (2 * δ) * (2 * L + 1) := by
  rw [cutNorm_eq]
  set B := C ^ 2 * (1 + (L : ℝ)) ^ (2 * δ)
  have hpt : ∀ m : ℤ, ‖cutoff u L m‖ ^ 2 ≤ if m ∈ Finset.Icc (-(L : ℤ)) L then B else 0 := by
    intro m
    simp only [cutoff, Finset.mem_Icc]
    split_ifs with h
    · have h1 := hC m
      have h0 : 0 ≤ C * (1 + |(m : ℝ)|) ^ δ := (norm_nonneg _).trans h1
      have habs : |(m : ℝ)| ≤ L := by
        have : |m| ≤ L := abs_le.mpr ⟨h.1, h.2⟩
        exact_mod_cast this
      calc ‖u m‖ ^ 2 ≤ (C * (1 + |(m : ℝ)|) ^ δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = C ^ 2 * (1 + |(m : ℝ)|) ^ (2 * δ) := by
            rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), mul_comm δ]; norm_num
        _ ≤ B := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith)
            (by linarith)) (sq_nonneg C)
    · simp
  have hsum : HasSum (fun m : ℤ => if m ∈ Finset.Icc (-(L : ℤ)) L then B else 0)
      (∑ m ∈ Finset.Icc (-(L : ℤ)) L, if m ∈ Finset.Icc (-(L : ℤ)) L then B else 0) :=
    hasSum_sum_of_ne_finset_zero (fun m hm => if_neg hm)
  calc ∑' m, ‖cutoff u L m‖ ^ 2
      ≤ ∑' m : ℤ, (if m ∈ Finset.Icc (-(L : ℤ)) L then B else 0) :=
        (summable_cutoff u L).tsum_le_tsum hpt hsum.summable
    _ = ∑ m ∈ Finset.Icc (-(L : ℤ)) L, B := by
        rw [hsum.tsum_eq]; exact Finset.sum_congr rfl fun m hm => if_pos hm
    _ = B * (2 * L + 1) := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul,
          show ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 by omega]
        push_cast; ring

/-- **Theorem 2.4.2 (a)** (Sch'nol): every generalized eigenvalue of `H` lies in `σ(H)`. -/
theorem genEig_mem_spectrum (hV : BddPot V) {z : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) {u : ℤ → ℂ}
    (hu : IsGenEigenfun V z δ u) : z ∈ spectrum ℂ (schr V) := by
  obtain ⟨hne, hsol, C, hC⟩ := hu
  by_contra hzs
  have hz : z ∈ resolventSet ℂ (schr V) := mem_resolventSet_iff_notMem.mpr hzs
  set R := res (schr V) z
  set K := 4 * ‖R‖ ^ 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  -- (2.4.4) combined with the resolvent bound
  have hkey : ∀ L : ℕ, 1 ≤ L → cutNorm u L ≤ K * (cutNorm u (L + 1) - cutNorm u (L - 1)) := by
    intro L hL
    have h1 : ‖cutL u L‖ ≤ ‖R‖ * ‖(schr V - algebraMap ℂ Op z) (cutL u L)‖ := by
      calc ‖cutL u L‖ = ‖R ((schr V - algebraMap ℂ Op z) (cutL u L))‖ := by
            rw [← ContinuousLinearMap.mul_apply, res_mul_sub hz, ContinuousLinearMap.one_apply]
        _ ≤ _ := R.le_opNorm _
    have h2 := norm_sub_cutL_le hV hsol hL
    have hd := cutNorm_diff u hL
    have h3 : ‖cutL u L‖ ≤ ‖R‖ * (‖u L‖ + ‖u (L + 1)‖ + ‖u (-L)‖ + ‖u (-L - 1)‖) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    have h4 : cutNorm u L ≤ ‖R‖ ^ 2 * (‖u L‖ + ‖u (L + 1)‖ + ‖u (-L)‖ + ‖u (-L - 1)‖) ^ 2 := by
      rw [cutNorm, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h3 2
    have h5 : (‖u L‖ + ‖u (L + 1)‖ + ‖u (-L)‖ + ‖u (-L - 1)‖) ^ 2 ≤
        4 * (‖u L‖ ^ 2 + ‖u (L + 1)‖ ^ 2 + ‖u (-L)‖ ^ 2 + ‖u (-L - 1)‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u L‖ - ‖u (L + 1)‖), sq_nonneg (‖u L‖ - ‖u (-L)‖),
        sq_nonneg (‖u L‖ - ‖u (-L - 1)‖), sq_nonneg (‖u (L + 1)‖ - ‖u (-L)‖),
        sq_nonneg (‖u (L + 1)‖ - ‖u (-L - 1)‖), sq_nonneg (‖u (-L)‖ - ‖u (-L - 1)‖)]
    rw [hd]
    have hD : 0 ≤ ‖u L‖ ^ 2 + ‖u (L + 1)‖ ^ 2 + ‖u (-L)‖ ^ 2 + ‖u (-L - 1)‖ ^ 2 := by positivity
    calc cutNorm u L ≤ ‖R‖ ^ 2 * (4 * (‖u L‖ ^ 2 + ‖u (L + 1)‖ ^ 2 + ‖u (-L)‖ ^ 2 +
          ‖u (-L - 1)‖ ^ 2)) := h4.trans (mul_le_mul_of_nonneg_left h5 (by positivity))
      _ ≤ K * _ := by rw [hK]; nlinarith
  set r := 1 + 1 / K with hr
  have hr1 : 1 < r := by rw [hr]; have : 0 < 1 / K := by positivity
                         linarith
  have hstep : ∀ L : ℕ, 1 ≤ L → r * cutNorm u (L - 1) ≤ cutNorm u (L + 1) := by
    intro L hL
    have h1 := hkey L hL
    have h2 := cutNorm_mono u (show L - 1 ≤ L by omega)
    have h3 : cutNorm u (L - 1) ≤ K * (cutNorm u (L + 1) - cutNorm u (L - 1)) := h2.trans h1
    have h4 : 1 / K * cutNorm u (L - 1) ≤ cutNorm u (L + 1) - cutNorm u (L - 1) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hKpos]; linarith
    rw [hr, add_mul, one_mul]; linarith
  -- a site where `u` does not vanish
  obtain ⟨n0, hn0⟩ : ∃ n0, u n0 ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  set Lb := n0.natAbs
  have hsLb : 0 < cutNorm u Lb := by
    have hle := (summable_cutoff u Lb).le_tsum n0 (fun _ _ => by positivity)
    rw [← cutNorm_eq] at hle
    have : cutoff u Lb n0 = u n0 := by
      simp only [cutoff]; rw [if_pos]; constructor <;> omega
    rw [this] at hle
    exact lt_of_lt_of_le (by positivity) hle
  -- exponential growth
  have hgrowth : ∀ k : ℕ, r ^ k * cutNorm u Lb ≤ cutNorm u (Lb + 2 * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep (Lb + 2 * k + 1) (by omega)
      rw [show Lb + 2 * k + 1 - 1 = Lb + 2 * k by omega,
        show Lb + 2 * k + 1 + 1 = Lb + 2 * (k + 1) by ring] at this
      calc r ^ (k + 1) * cutNorm u Lb = r * (r ^ k * cutNorm u Lb) := by ring
        _ ≤ r * cutNorm u (Lb + 2 * k) := by gcongr
        _ ≤ _ := this
  -- polynomial upper bound
  set p := ⌈2 * δ⌉₊ + 1
  set A : ℝ := Lb + 3
  have hpoly : ∀ k : ℕ, cutNorm u (Lb + 2 * k) ≤ 2 * C ^ 2 * A ^ p * ((k : ℝ) + 1) ^ p := by
    intro k
    set L := Lb + 2 * k
    have h1 := cutNorm_le hδ hC L
    have hx : (1 : ℝ) ≤ 1 + L := by have := Nat.cast_nonneg (α := ℝ) L; linarith
    have h2 : (1 + (L : ℝ)) ^ (2 * δ) ≤ (1 + (L : ℝ)) ^ (⌈2 * δ⌉₊ : ℕ) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil _)
    have h3 : 2 * (L : ℝ) + 1 ≤ 2 * (1 + L) := by linarith
    have h4 : 1 + (L : ℝ) ≤ A * ((k : ℝ) + 1) := by
      simp only [L, A]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) Lb, Nat.cast_nonneg (α := ℝ) k]
    calc cutNorm u L ≤ C ^ 2 * (1 + L) ^ (2 * δ) * (2 * L + 1) := h1
      _ ≤ C ^ 2 * (1 + (L : ℝ)) ^ (⌈2 * δ⌉₊ : ℕ) * (2 * (1 + L)) := by gcongr
      _ = 2 * C ^ 2 * (1 + (L : ℝ)) ^ p := by rw [pow_succ]; ring
      _ ≤ 2 * C ^ 2 * (A * ((k : ℝ) + 1)) ^ p := by gcongr
      _ = 2 * C ^ 2 * A ^ p * ((k : ℝ) + 1) ^ p := by rw [mul_pow]; ring
  set M := 2 * C ^ 2 * A ^ p
  have hMpos : 0 < M := by
    have := (hgrowth 0).trans (hpoly 0)
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, one_pow, mul_one] at this
    linarith
  -- contradiction with `nᵖ / rⁿ → 0`
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt p hr1
  have hc0 : 0 < cutNorm u Lb / (M * r) := by positivity
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hc0)).exists_forall_of_atTop
  have h1 := hN (N + 1) (by omega)
  have h2 := (hgrowth N).trans (hpoly N)
  have hrpos : 0 < r := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h1
  push_cast at h1
  have h3 : r ^ (N + 1) * cutNorm u Lb ≤ ((N : ℝ) + 1) ^ p * (M * r) := by
    calc r ^ (N + 1) * cutNorm u Lb = r * (r ^ N * cutNorm u Lb) := by ring
      _ ≤ r * (M * ((N : ℝ) + 1) ^ p) := mul_le_mul_of_nonneg_left h2 hrpos.le
      _ = _ := by ring
  linarith

/-- Theorem 2.4.2 (a): `G ⊆ σ(H)`. -/
theorem genEigAll_subset_spectrum (hV : BddPot V) : genEigAll V ⊆ spectrum ℂ (schr V) := by
  intro z hz
  simp only [genEigAll, Set.mem_iUnion, Set.mem_Ioi] at hz
  obtain ⟨δ, hδ, u, hu⟩ := hz
  exact genEig_mem_spectrum hV hδ.le hu

/-- Proof of Theorem 2.4.2 (c), first inclusion (2.4.14): `closure G ⊆ σ(H)`. -/
theorem closure_genEigAll_subset_spectrum (hV : BddPot V) :
    closure (genEigAll V) ⊆ spectrum ℂ (schr V) :=
  closure_minimal (genEigAll_subset_spectrum hV) (spectrum.isClosed _)

end DF
