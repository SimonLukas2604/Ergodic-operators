/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# The explicit Lax pair for the truncated chiral block  (paper §5, l.1412–1669)

* `BN α N x`: the `N × N` Jacobi block (BN) (l.1427), zero diagonal and
  `B_{j,j+1} = B_{j+1,j} = 2 sin π(x+(j+1)α)`; complex version `BNc`;
* `cr α r`: the coefficients `c_r = (-1)^{r-1} π / (2 sin(π α r))` (l.1442);
* `LN N = ⌊(N-1)/2⌋` (l.1437);
* `KN α N`: the real skew-symmetric Toeplitz matrix (defKL) (l.1450);
* `Eeven α N x`, `Eedge α N x`: the error matrices (Eeven), (Eedge1), (Eedge2) (l.1470–1484);
* `lemma_commut`: Lemma `lemma-commut` (commutK1) (l.1462), entrywise as `HasDerivAt`, and
  `lemma_commut_matrix` for the matrix-valued map, `lemma_commut_complex` for `BNc`;
* `PN N`: the boundary projection of (bp) (l.1271), `Epm`: the matrices (Epm) (l.1546);
* `lemma_commut2`: Lemma `lemma-commut2` (commutK2) and `rank_Epm_le`: `rk 𝓔^± ≤ 4`
  (l.1540–1570), via the general `rank_le_of_interior_eq_zero`;
* `Eeven_hs`, `Eedge_hs`, `commKP_hs`: the Hilbert–Schmidt bounds (Enorms) (l.1601–1610) in
  the proof of Prop. `prop-phase-variation`; the Hilbert–Schmidt norm squared is written as the
  explicit sum of squares of the entries `hs2 E = ∑ i, ∑ k, E i k ^ 2`;
* `sum_inv_sin_sq_le`: the arithmetic step (l.1612–1636) in the abstract form: if the points
  `rα`, `1 ≤ r ≤ L`, are `δ`-separated on `𝕋` and `δ`-far from `0`, then
  `∑_{r=1}^L 1/sin²(παr) ≤ 1/δ²`, hence `∑_{r=1}^L c_r² ≤ π²/(4δ²)`.

## Conventions and remarks

* Indices are `Fin N` (`0 ≤ j ≤ N-1` as in the paper).  Internally entries are computed on
  `ℤ`-indices with `b_j = 2 sin π(αj+x)` (`bf`) and the odd extension `crZ` of `c_r`
  to `r ∈ ℤ` (`crZ 0 = 0`).
* The nonvanishing of the denominators `sin(παr)` is taken as the hypothesis
  `∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0`; `sin_ne_zero_of_irrational` derives it from
  irrationality of `α`.
* The formulas (Eeven), (Eedge1), (Eedge2) of the paper were checked numerically (for
  `N = 3, …, 10`) and found to be correct as stated; the formalized statement is exactly the
  paper's.  In `Eedge` the entries `(0, 2r+1)` are parametrized by the column index
  `k = 2r+1` (so `c_{r+1} = c_{(k+1)/2}`), and the entries `(N-2r-2, N-1)` by `N - i = 2r+2`.

No `sorry`s.
-/
import Mathlib

noncomputable section

open Real Finset

namespace CAH

namespace LaxPair

/-! ## Definitions -/

/-- `b_j = 2 sin π(αj + x)` for `j ∈ ℤ` (proof of Lemma `lemma-commut`, l.1488). -/
def bf (α x : ℝ) (j : ℤ) : ℝ := 2 * sin (π * (α * j + x))

/-- `L = ⌊(N-1)/2⌋` (l.1437). -/
def LN (N : ℕ) : ℕ := (N - 1) / 2

/-- The coefficients `c_r = (-1)^{r-1} π / (2 sin(π α r))` (l.1442). -/
def cr (α : ℝ) (r : ℕ) : ℝ := (-1) ^ (r - 1) * π / (2 * sin (π * α * r))

/-- The odd extension of `c_r` to `r ∈ ℤ` (with `crZ α 0 = 0`). -/
def crZ (α : ℝ) (r : ℤ) : ℝ := (-1) ^ (r.natAbs + 1) * π / (2 * sin (π * α * r))

/-- The Toeplitz symbol of `K_N`: `kap α d = c_{d/2}` for `d` even (odd extension), else `0`. -/
def kap (α : ℝ) (d : ℤ) : ℝ := if Even d then crZ α (d / 2) else 0

/-- The Jacobi block (BN) (l.1427): zero diagonal and
`B_{j,j+1} = B_{j+1,j} = 2 sin π(x + (j+1)α)`. -/
def BN (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun j k =>
  if (k : ℕ) = (j : ℕ) + 1 then 2 * sin (π * (x + ((j : ℕ) + 1 : ℝ) * α))
  else if (j : ℕ) = (k : ℕ) + 1 then 2 * sin (π * (x + ((k : ℕ) + 1 : ℝ) * α)) else 0

/-- The complex (Hermitian) version of `BN`. -/
def BNc (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℂ := (BN α N x).map (↑)

/-- The real skew-symmetric Toeplitz matrix `K_N` of (defKL) (l.1450). -/
def KN (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := fun j k =>
  if (j : ℕ) < k ∧ Even ((k : ℕ) - j) then cr α (((k : ℕ) - j) / 2)
  else if (k : ℕ) < j ∧ Even ((j : ℕ) - k) then -cr α (((j : ℕ) - k) / 2) else 0

/-- The complex version of `KN`. -/
def KNc (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := (KN α N).map (↑)

/-- The matrix `𝓔_even(x)` of (Eeven) (l.1472): only the two corners
`(0, N-1)`, `(N-1, 0)` are nonzero, equal to `2π(-1)^{N/2-1} cos(π(αN/2+x))`, and only when
`N` is even. -/
def Eeven (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i k =>
  if Even N ∧ (((i : ℕ) = 0 ∧ (k : ℕ) = N - 1) ∨ ((i : ℕ) = N - 1 ∧ (k : ℕ) = 0)) then
    2 * π * (-1) ^ (N / 2 - 1) * cos (π * (α * N / 2 + x))
  else 0

/-- The entries `(𝓔_edge)_{0,2r+1} = -c_{r+1} 2 sin(πx)`, `0 ≤ r ≤ L-1`, of (Eedge1), with
`k = 2r+1`. -/
def EedgeR0 (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i k =>
  if (i : ℕ) = 0 ∧ Odd (k : ℕ) ∧ (k : ℕ) < 2 * LN N then
    -cr α (((k : ℕ) + 1) / 2) * (2 * sin (π * x)) else 0

/-- The entries `(𝓔_edge)_{2r+1,0} = -c_{r+1} 2 sin(πx)`, `0 ≤ r ≤ L-1`, of (Eedge1). -/
def EedgeC0 (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i k =>
  if (k : ℕ) = 0 ∧ Odd (i : ℕ) ∧ (i : ℕ) < 2 * LN N then
    -cr α (((i : ℕ) + 1) / 2) * (2 * sin (π * x)) else 0

/-- The entries `(𝓔_edge)_{N-2r-2,N-1} = c_{r+1} 2 sin(π(x+Nα))`, `0 ≤ r ≤ L-1`, of (Eedge2),
with `N - i = 2r+2`. -/
def EedgeCN (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i k =>
  if (k : ℕ) = N - 1 ∧ Even (N - i) ∧ 2 ≤ N - i ∧ N - i ≤ 2 * LN N then
    cr α ((N - i) / 2) * (2 * sin (π * (x + N * α))) else 0

/-- The entries `(𝓔_edge)_{N-1,N-2r-2} = c_{r+1} 2 sin(π(x+Nα))`, `0 ≤ r ≤ L-1`, of (Eedge2). -/
def EedgeRN (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i k =>
  if (i : ℕ) = N - 1 ∧ Even (N - k) ∧ 2 ≤ N - k ∧ N - k ≤ 2 * LN N then
    cr α ((N - k) / 2) * (2 * sin (π * (x + N * α))) else 0

/-- The matrix `𝓔_edge(x)` of (Eedge1), (Eedge2) (l.1478–1484): for `0 ≤ r ≤ L-1`,
`(𝓔_edge)_{0,2r+1} = (𝓔_edge)_{2r+1,0} = -c_{r+1} 2 sin(πx)` and
`(𝓔_edge)_{N-2r-2,N-1} = (𝓔_edge)_{N-1,N-2r-2} = c_{r+1} 2 sin(π(x+Nα))`, all other entries
zero.  (The four families have pairwise disjoint supports, see `Eedge_sq`.) -/
def Eedge (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  EedgeR0 α N x + EedgeC0 α N x + EedgeCN α N x + EedgeRN α N x

/-! ## Elementary facts about `c_r` -/

lemma crZ_natCast (α : ℝ) (r : ℕ) : crZ α r = cr α r := by
  rcases r with _ | n
  · simp [crZ, cr]
  · simp only [crZ, cr, Int.natAbs_natCast, Int.cast_natCast]
    rw [show n + 1 + 1 = n + 2 by ring, show n + 1 - 1 = n by omega, pow_add]
    norm_num

lemma crZ_neg (α : ℝ) (r : ℤ) : crZ α (-r) = -crZ α r := by
  simp only [crZ, Int.natAbs_neg, Int.cast_neg, mul_neg, Real.sin_neg, div_neg]

lemma crZ_zero (α : ℝ) : crZ α 0 = 0 := by simp [crZ]

/-- The sign `(-1)^{|r|+1}` for `r ≠ 0`, `0` for `r = 0`. -/
def sgnZ (r : ℤ) : ℝ := if r = 0 then 0 else (-1) ^ (r.natAbs + 1)

lemma crZ_mul_sin (α : ℝ) (r : ℤ) (h : r ≠ 0 → sin (π * α * r) ≠ 0) :
    crZ α r * (2 * sin (π * α * r)) = sgnZ r * π := by
  by_cases hr : r = 0
  · subst hr; simp [crZ, sgnZ]
  · have := h hr
    simp only [crZ, sgnZ, ite_eq_right hr]
    field_simp

lemma sgnZ_add (s : ℤ) : sgnZ s + sgnZ (s + 1) = if s = 0 ∨ s = -1 then 1 else 0 := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · by_cases h1 : s = -1
    · subst h1; norm_num [sgnZ]
    · have e : s.natAbs = (s + 1).natAbs + 1 := by omega
      simp only [sgnZ, ite_eq_right hs.ne, ite_eq_right (show s + 1 ≠ 0 by omega),
        ite_eq_right (show ¬ (s = 0 ∨ s = -1) by omega), e, pow_succ]
      ring
  · subst hs; norm_num [sgnZ]
  · have e : (s + 1).natAbs = s.natAbs + 1 := by omega
    simp only [sgnZ, ite_eq_right hs.ne', ite_eq_right (show s + 1 ≠ 0 by omega),
      ite_eq_right (show ¬ (s = 0 ∨ s = -1) by omega), e, pow_succ]
    ring

/-- `sin(παr) ≠ 0` for `r ≠ 0` when `α` is irrational. -/
lemma sin_ne_zero_of_irrational {α : ℝ} (hα : Irrational α) {r : ℤ} (hr : r ≠ 0) :
    sin (π * α * r) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hπ := Real.pi_pos.ne'
  have : α = (n : ℝ) / r := by
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    field_simp
    have := hn.symm
    apply mul_left_cancel₀ hπ
    linarith [this]
  exact hα ⟨n / r, by rw [this]; push_cast; rfl⟩

lemma sin_hyp_of_irrational {α : ℝ} (hα : Irrational α) (N : ℕ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0 := fun r hr _ => by
  have := sin_ne_zero_of_irrational hα (r := (r : ℤ)) (by omega)
  simpa using this

/-- Passing from the `ℕ`-hypothesis to `ℤ`. -/
lemma sin_hyp_int {α : ℝ} {N : ℕ} (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0)
    (r : ℤ) (hr : r ≠ 0) (hrN : r.natAbs ≤ N) : sin (π * α * r) ≠ 0 := by
  rcases Int.natAbs_eq r with h | h
  · rw [h]; simpa using hsin r.natAbs (by omega) hrN
  · rw [h, Int.cast_neg, Int.cast_natCast, mul_neg, Real.sin_neg, neg_ne_zero]
    exact hsin r.natAbs (by omega) hrN

/-! ## The core trigonometric identity on `ℤ` -/

/-- The derivative of the (doubly infinite) Jacobi matrix with `b_j = 2 sin π(αj+x)`. -/
def dBz (α x : ℝ) (i k : ℤ) : ℝ :=
  (if k = i + 1 then 2 * π * cos (π * (α * k + x)) else 0) +
  (if i = k + 1 then 2 * π * cos (π * (α * i + x)) else 0)

lemma bf_sub_bf (α x : ℝ) (a c : ℤ) :
    bf α x (a + 2 * c) - bf α x a =
      2 * sin (π * α * (c : ℝ)) * (2 * cos (π * (α * ((a + c : ℤ) : ℝ) + x))) := by
  simp only [bf]
  rw [← mul_sub, Real.sin_sub_sin]
  rw [show (π * (α * ((a + 2 * c : ℤ) : ℝ) + x) - π * (α * (a : ℝ) + x)) / 2 = π * α * (c : ℝ) by
      push_cast; ring,
    show (π * (α * ((a + 2 * c : ℤ) : ℝ) + x) + π * (α * (a : ℝ) + x)) / 2 =
      π * (α * ((a + c : ℤ) : ℝ) + x) by push_cast; ring]
  ring

lemma kap_of_not_even (α : ℝ) {d : ℤ} (h : ¬ Even d) : kap α d = 0 := by
  simp [kap, h]

lemma kap_two_mul (α : ℝ) {d s : ℤ} (h : d = 2 * s) : kap α d = crZ α s := by
  subst h
  rw [kap, ite_eq_left (even_two_mul s)]
  congr 1
  omega

/-- The core identity: on `ℤ`, `[K_∞, B_∞] = B_∞'` entrywise.  For `k - i = 2s+1` this is
`c_s (b_k - b_{i+1}) + c_{s+1} (b_{k+1} - b_i) = δ_{s,0} b_k' + δ_{s,-1} b_i'`, which contains
both identities `c_{(ℓ+1)/2}(b_{j+ℓ+1}-b_j) + c_{(ℓ-1)/2}(b_{j+ℓ}-b_{j+1}) = 0` (`ℓ ≥ 3`) and
`c_1 (b_{j+2} - b_j) = b_{j+1}'` of the proof of Lemma `lemma-commut` (l.1513). -/
lemma core {α x : ℝ} {N : ℕ} (hsin : ∀ r : ℤ, r ≠ 0 → r.natAbs ≤ N → sin (π * α * r) ≠ 0)
    (i k : ℤ) (hik : (k - i).natAbs < N) :
    kap α (k - 1 - i) * bf α x k + kap α (k + 1 - i) * bf α x (k + 1)
      - bf α x (i + 1) * kap α (k - (i + 1)) - bf α x i * kap α (k - (i - 1)) =
      dBz α x i k := by
  rcases Int.even_or_odd (k - i) with he | ⟨s, hs⟩
  · rw [Int.even_iff] at he
    rw [kap_of_not_even α (d := k - 1 - i) (by rw [Int.even_iff]; omega),
      kap_of_not_even α (d := k + 1 - i) (by rw [Int.even_iff]; omega),
      kap_of_not_even α (d := k - (i + 1)) (by rw [Int.even_iff]; omega),
      kap_of_not_even α (d := k - (i - 1)) (by rw [Int.even_iff]; omega)]
    simp only [dBz, ite_eq_right (show k ≠ i + 1 by omega), ite_eq_right (show i ≠ k + 1 by omega)]
    ring
  · rw [kap_two_mul α (s := s) (by omega), kap_two_mul α (d := k - (i + 1)) (s := s) (by omega),
      kap_two_mul α (d := k + 1 - i) (s := s + 1) (by omega),
      kap_two_mul α (d := k - (i - 1)) (s := s + 1) (by omega)]
    have b1 := bf_sub_bf α x (i + 1) s
    have b2 := bf_sub_bf α x i (s + 1)
    rw [show i + 1 + 2 * s = k by omega] at b1
    rw [show i + 2 * (s + 1) = k + 1 by omega, show i + (s + 1) = i + 1 + s by ring] at b2
    have hs0 := crZ_mul_sin α s (fun h => hsin s h (by omega))
    have hs1 := crZ_mul_sin α (s + 1) (fun h => hsin (s + 1) h (by omega))
    have key : crZ α s * bf α x k + crZ α (s + 1) * bf α x (k + 1)
        - bf α x (i + 1) * crZ α s - bf α x i * crZ α (s + 1) =
        (crZ α s * (2 * sin (π * α * (s : ℝ))) +
          crZ α (s + 1) * (2 * sin (π * α * ((s + 1 : ℤ) : ℝ)))) *
          (2 * cos (π * (α * ((i + 1 + s : ℤ) : ℝ) + x))) := by
      linear_combination (crZ α s) * b1 + crZ α (s + 1) * b2
    rw [key, hs0, hs1, ← add_mul, sgnZ_add]
    by_cases h0 : s = 0
    · subst h0
      obtain rfl : k = i + 1 := by omega
      simp only [dBz, ite_true, true_or, ite_eq_right (show i ≠ i + 1 + 1 by omega)]
      push_cast; ring_nf
    · by_cases h1 : s = -1
      · subst h1
        obtain rfl : k = i - 1 := by omega
        simp only [dBz, ite_eq_right (show i - 1 ≠ i + 1 by omega), ite_eq_left (show i = i - 1 + 1 by ring),
          or_true, ite_true]
        push_cast; ring_nf
      · simp only [dBz, ite_eq_right (show ¬ (s = 0 ∨ s = -1) by omega),
          ite_eq_right (show k ≠ i + 1 by omega), ite_eq_right (show i ≠ k + 1 by omega)]
        ring

/-! ## Entries of `B_N`, `K_N` on `ℤ`-indices and the commutator -/

variable {N : ℕ}

lemma BN_col (α x : ℝ) (m k : Fin N) :
    BN α N x m k = (if ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) - 1 then bf α x (k : ℕ) else 0) +
      (if ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 then bf α x (m : ℕ) else 0) := by
  unfold BN bf
  by_cases h1 : (k : ℕ) = (m : ℕ) + 1
  · rw [ite_eq_left h1, ite_eq_left (show ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) - 1 by omega),
      ite_eq_right (show ¬ ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 by omega)]
    have : ((k : ℕ) : ℝ) = (m : ℕ) + 1 := by exact_mod_cast h1
    push_cast [this]; ring_nf
  · rw [ite_eq_right h1, ite_eq_right (show ¬ ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) - 1 by omega)]
    by_cases h2 : (m : ℕ) = (k : ℕ) + 1
    · rw [ite_eq_left h2, ite_eq_left (show ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 by omega)]
      have : ((m : ℕ) : ℝ) = (k : ℕ) + 1 := by exact_mod_cast h2
      push_cast [this]; ring_nf
    · rw [ite_eq_right h2, ite_eq_right (show ¬ ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 by omega)]; ring

lemma BN_row (α x : ℝ) (j m : Fin N) :
    BN α N x j m = (if ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 then bf α x (m : ℕ) else 0) +
      (if ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 then bf α x (j : ℕ) else 0) := by
  unfold BN bf
  by_cases h1 : (m : ℕ) = (j : ℕ) + 1
  · rw [ite_eq_left h1, ite_eq_left (show ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 by omega),
      ite_eq_right (show ¬ ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 by omega)]
    have : ((m : ℕ) : ℝ) = (j : ℕ) + 1 := by exact_mod_cast h1
    push_cast [this]; ring_nf
  · rw [ite_eq_right h1, ite_eq_right (show ¬ ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 by omega)]
    by_cases h2 : (j : ℕ) = (m : ℕ) + 1
    · rw [ite_eq_left h2, ite_eq_left (show ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 by omega)]
      have : ((j : ℕ) : ℝ) = (m : ℕ) + 1 := by exact_mod_cast h2
      push_cast [this]; ring_nf
    · rw [ite_eq_right h2, ite_eq_right (show ¬ ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 by omega)]; ring

lemma KN_eq (α : ℝ) (j k : Fin N) : KN α N j k = kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := by
  unfold KN kap
  by_cases h1 : (j : ℕ) < k ∧ Even ((k : ℕ) - j)
  · rw [ite_eq_left h1, ite_eq_left (by obtain ⟨_, h⟩ := h1; rw [Nat.even_iff] at h; rw [Int.even_iff]; omega),
      ← crZ_natCast]
    congr 1; obtain ⟨_, h⟩ := h1; rw [Nat.even_iff] at h; omega
  · rw [ite_eq_right h1]
    by_cases h2 : (k : ℕ) < j ∧ Even ((j : ℕ) - k)
    · rw [ite_eq_left h2, ite_eq_left (by obtain ⟨_, h⟩ := h2; rw [Nat.even_iff] at h; rw [Int.even_iff]; omega),
        ← crZ_natCast, ← crZ_neg]
      congr 1; obtain ⟨_, h⟩ := h2; rw [Nat.even_iff] at h; omega
    · rw [ite_eq_right h2]
      split_ifs with h3
      · rw [Nat.even_iff] at h1 h2; rw [Int.even_iff] at h3
        rw [show (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) / 2 = 0 by omega, crZ_zero]
      · rfl

lemma sum_fin_ite (t : ℤ) (f : Fin N → ℝ) :
    ∑ m : Fin N, (if ((m : ℕ) : ℤ) = t then f m else 0) =
      if h : 0 ≤ t ∧ t < N then f ⟨t.toNat, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨t.toNat, by omega⟩ : Fin N)]
    · rw [ite_eq_left (by simp; omega)]
    · intro b _ hb
      rw [ite_eq_right]
      intro h'; apply hb; ext; simp; omega
    · simp
  · apply Finset.sum_eq_zero
    intro m _
    rw [ite_eq_right]
    have := m.isLt
    omega

/-- Entries of the commutator `[K_N, B_N(x)]`: at most four nonzero terms. -/
lemma comm_apply (α x : ℝ) (j k : Fin N) :
    (KN α N * BN α N x - BN α N x * KN α N) j k =
      (if 0 ≤ ((k : ℕ) : ℤ) - 1 ∧ ((k : ℕ) : ℤ) - 1 < N then
          kap α (((k : ℕ) : ℤ) - 1 - (j : ℕ)) * bf α x (k : ℕ) else 0) +
      (if 0 ≤ ((k : ℕ) : ℤ) + 1 ∧ ((k : ℕ) : ℤ) + 1 < N then
          kap α (((k : ℕ) : ℤ) + 1 - (j : ℕ)) * bf α x (((k : ℕ) : ℤ) + 1) else 0) -
      ((if 0 ≤ ((j : ℕ) : ℤ) + 1 ∧ ((j : ℕ) : ℤ) + 1 < N then
          bf α x (((j : ℕ) : ℤ) + 1) * kap α ((k : ℕ) - (((j : ℕ) : ℤ) + 1)) else 0) +
      (if 0 ≤ ((j : ℕ) : ℤ) - 1 ∧ ((j : ℕ) : ℤ) - 1 < N then
          bf α x (j : ℕ) * kap α ((k : ℕ) - (((j : ℕ) : ℤ) - 1)) else 0)) := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [KN_eq, BN_row α x j]
  simp only [BN_col α x _ k]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
    sum_fin_ite]
  congr 1 <;> congr 1 <;> split_ifs with h <;> first | rfl | simp only [Int.toNat_of_nonneg h.1]

/-- The boundary error `B_N' - [K_N, B_N]`, in raw form (terms cut off at indices `-1`, `N`). -/
def Ebdry (α : ℝ) (N : ℕ) (x : ℝ) (j k : ℤ) : ℝ :=
  (if k = 0 then kap α (k - 1 - j) * bf α x k else 0) +
  (if k = N - 1 then kap α (k + 1 - j) * bf α x (k + 1) else 0) -
  (if j = N - 1 then bf α x (j + 1) * kap α (k - (j + 1)) else 0) -
  (if j = 0 then bf α x j * kap α (k - (j - 1)) else 0)

lemma dBz_sub_comm {α : ℝ} (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0)
    (x : ℝ) (j k : Fin N) :
    dBz α x (j : ℕ) (k : ℕ) - (KN α N * BN α N x - BN α N x * KN α N) j k =
      Ebdry α N x (j : ℕ) (k : ℕ) := by
  have hc := core (x := x) (sin_hyp_int hsin) ((j : ℕ) : ℤ) ((k : ℕ) : ℤ)
    (by have := j.isLt; have := k.isLt; omega)
  have := j.isLt; have := k.isLt
  rw [comm_apply, Ebdry]
  split_ifs <;> first | linarith | (exfalso; omega)

/-- The entries of `B_N(x)` are differentiable with derivative `dBz`. -/
lemma hasDerivAt_BN_entry (α : ℝ) (x : ℝ) (j k : Fin N) :
    HasDerivAt (fun y => BN α N y j k) (dBz α x (j : ℕ) (k : ℕ)) x := by
  by_cases h1 : (k : ℕ) = (j : ℕ) + 1
  · have e : (fun y => BN α N y j k) = fun y => 2 * sin (π * (y + ((j : ℕ) + 1 : ℝ) * α)) := by
      funext y; simp only [BN, ite_eq_left h1]
    rw [e]
    refine (((((hasDerivAt_id' x).add_const (((j : ℕ) + 1 : ℝ) * α)).const_mul π).sin).const_mul
      2).congr_deriv ?_
    simp only [dBz, ite_eq_left (show ((k : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 by omega),
      ite_eq_right (show ((j : ℕ) : ℤ) ≠ ((k : ℕ) : ℤ) + 1 by omega)]
    have : ((k : ℕ) : ℝ) = (j : ℕ) + 1 := by exact_mod_cast h1
    push_cast [this]; ring_nf
  · by_cases h2 : (j : ℕ) = (k : ℕ) + 1
    · have e : (fun y => BN α N y j k) =
          fun y => 2 * sin (π * (y + ((k : ℕ) + 1 : ℝ) * α)) := by
        funext y; simp only [BN, ite_eq_right h1, ite_eq_left h2]
      rw [e]
      refine (((((hasDerivAt_id' x).add_const (((k : ℕ) + 1 : ℝ) * α)).const_mul π).sin).const_mul
        2).congr_deriv ?_
      simp only [dBz, ite_eq_right (show ((k : ℕ) : ℤ) ≠ ((j : ℕ) : ℤ) + 1 by omega),
        ite_eq_left (show ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 by omega)]
      have : ((j : ℕ) : ℝ) = (k : ℕ) + 1 := by exact_mod_cast h2
      push_cast [this]; ring_nf
    · have e : (fun y => BN α N y j k) = fun _ => 0 := by
        funext y; simp only [BN, ite_eq_right h1, ite_eq_right h2]
      rw [e]
      refine (hasDerivAt_const x (0 : ℝ)).congr_deriv ?_
      simp only [dBz, ite_eq_right (show ((k : ℕ) : ℤ) ≠ ((j : ℕ) : ℤ) + 1 by omega),
        ite_eq_right (show ((j : ℕ) : ℤ) ≠ ((k : ℕ) : ℤ) + 1 by omega)]
      ring

/-! ## Identification of the boundary error with `𝓔_even + 𝓔_edge` -/

lemma bf_zero (α x : ℝ) : bf α x 0 = 2 * sin (π * x) := by simp [bf]

lemma bf_N (α x : ℝ) (N : ℕ) : bf α x (N : ℤ) = 2 * sin (π * (x + N * α)) := by
  simp only [bf, Int.cast_natCast]; ring_nf

/-- The corner value: `c_{N/2}(b_N - b_0) = 2π(-1)^{N/2-1} cos(π(αN/2+x))` for even `N`. -/
lemma corner {α : ℝ} (x : ℝ) (hN : 3 ≤ N) (he : N % 2 = 0)
    (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0) :
    cr α (N / 2) * (bf α x N - bf α x 0) =
      2 * π * (-1) ^ (N / 2 - 1) * cos (π * (α * N / 2 + x)) := by
  obtain ⟨t, rfl⟩ : ∃ t, N = 2 * t := ⟨N / 2, by omega⟩
  rw [show 2 * t / 2 = t by omega]
  have b := bf_sub_bf α x 0 t
  rw [show (0 : ℤ) + 2 * t = ((2 * t : ℕ) : ℤ) by push_cast; ring, zero_add] at b
  have hs := crZ_mul_sin α (t : ℤ) (fun h => sin_hyp_int hsin _ h (by simp; omega))
  rw [crZ_natCast] at hs
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [sgnZ, ite_eq_right (show ((s + 1 : ℕ) : ℤ) ≠ 0 by omega), Int.natAbs_natCast] at hs
  rw [b, show s + 1 - 1 = s by omega]
  have hcos : cos (π * (α * (((s + 1 : ℕ) : ℤ) : ℝ) + x)) =
      cos (π * (α * ((2 * (s + 1) : ℕ) : ℝ) / 2 + x)) := by
    congr 1; push_cast; ring
  rw [← hcos]
  linear_combination (2 * cos (π * (α * (((s + 1 : ℕ) : ℤ) : ℝ) + x))) * hs

lemma T1_eq (α x : ℝ) {j k : ℕ} (hj : j < N) :
    (if (k : ℤ) = 0 then kap α ((k : ℤ) - 1 - j) * bf α x k else 0) =
      (if k = 0 ∧ Odd j ∧ j < 2 * LN N then -cr α ((j + 1) / 2) * (2 * sin (π * x)) else 0) +
      (if N % 2 = 0 ∧ j = N - 1 ∧ k = 0 then -cr α (N / 2) * bf α x 0 else 0) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.cast_zero, ite_true, true_and, and_true]
    rcases Nat.even_or_odd j with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [kap_of_not_even α (by rw [Int.even_iff]; push_cast; omega),
        ite_eq_right (by rw [Nat.odd_iff]; omega), ite_eq_right (by omega)]
      ring
    · rw [kap_two_mul α (s := -((t + 1 : ℕ) : ℤ)) (by push_cast; ring), crZ_neg, crZ_natCast,
        show (2 * t + 1 + 1) / 2 = t + 1 by omega, bf_zero]
      by_cases hlt : 2 * t + 1 < 2 * LN N
      · rw [ite_eq_left ⟨⟨t, rfl⟩, hlt⟩, ite_eq_right (by unfold LN at hlt; omega)]; ring
      · rw [ite_eq_right (fun h => hlt h.2), ite_eq_left (by unfold LN at hlt; omega),
          show N / 2 = t + 1 by unfold LN at hlt; omega]
        ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; ring

lemma U2_eq (α x : ℝ) {j k : ℕ} (hk : k < N) :
    (if (j : ℤ) = 0 then bf α x j * kap α ((k : ℤ) - ((j : ℤ) - 1)) else 0) =
      -(if j = 0 ∧ Odd k ∧ k < 2 * LN N then -cr α ((k + 1) / 2) * (2 * sin (π * x)) else 0) +
      (if N % 2 = 0 ∧ j = 0 ∧ k = N - 1 then cr α (N / 2) * bf α x 0 else 0) := by
  by_cases hj0 : j = 0
  · subst hj0
    simp only [Nat.cast_zero, ite_true, true_and, zero_sub, sub_neg_eq_add]
    rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [kap_of_not_even α (by rw [Int.even_iff]; push_cast; omega),
        ite_eq_right (by rw [Nat.odd_iff]; omega), ite_eq_right (by omega)]
      ring
    · rw [kap_two_mul α (s := ((t + 1 : ℕ) : ℤ)) (by push_cast; ring), crZ_natCast,
        show (2 * t + 1 + 1) / 2 = t + 1 by omega, bf_zero]
      by_cases hlt : 2 * t + 1 < 2 * LN N
      · rw [ite_eq_left ⟨⟨t, rfl⟩, hlt⟩, ite_eq_right (by unfold LN at hlt; omega)]; ring
      · rw [ite_eq_right (fun h => hlt h.2), ite_eq_left (by unfold LN at hlt; omega),
          show N / 2 = t + 1 by unfold LN at hlt; omega]
        ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; ring

lemma T3_eq (α x : ℝ) {j k : ℕ} (hj : j < N) (hk : k < N) :
    (if (k : ℤ) = N - 1 then kap α ((k : ℤ) + 1 - j) * bf α x ((k : ℤ) + 1) else 0) =
      (if k = N - 1 ∧ Even (N - j) ∧ 2 ≤ N - j ∧ N - j ≤ 2 * LN N then
          cr α ((N - j) / 2) * (2 * sin (π * (x + N * α))) else 0) +
      (if N % 2 = 0 ∧ j = 0 ∧ k = N - 1 then cr α (N / 2) * bf α x N else 0) := by
  by_cases hk1 : k = N - 1
  · rw [ite_eq_left (by omega), show (k : ℤ) + 1 = N by omega, bf_N]
    rcases Nat.even_or_odd (N - j) with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [kap_two_mul α (s := (t : ℤ)) (by omega), crZ_natCast]
      by_cases hle : N - j ≤ 2 * LN N
      · rw [ite_eq_left ⟨hk1, ⟨t, ht⟩, by omega, hle⟩, ite_eq_right (by unfold LN at hle; omega),
          show (N - j) / 2 = t by omega]
        ring
      · rw [ite_eq_right (fun h => hle h.2.2.2), ite_eq_left (by unfold LN at hle; omega),
          show N / 2 = t by unfold LN at hle; omega]
        ring
    · rw [kap_of_not_even α (by rw [Int.even_iff]; omega),
        ite_eq_right (by rw [Nat.even_iff]; omega), ite_eq_right (by omega)]
      ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; ring

lemma U4_eq (α x : ℝ) {j k : ℕ} (hj : j < N) (hk : k < N) :
    (if (j : ℤ) = N - 1 then bf α x ((j : ℤ) + 1) * kap α ((k : ℤ) - ((j : ℤ) + 1)) else 0) =
      -(if j = N - 1 ∧ Even (N - k) ∧ 2 ≤ N - k ∧ N - k ≤ 2 * LN N then
          cr α ((N - k) / 2) * (2 * sin (π * (x + N * α))) else 0) +
      (if N % 2 = 0 ∧ j = N - 1 ∧ k = 0 then -cr α (N / 2) * bf α x N else 0) := by
  by_cases hj1 : j = N - 1
  · rw [ite_eq_left (by omega), show (j : ℤ) + 1 = N by omega, bf_N]
    rcases Nat.even_or_odd (N - k) with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [kap_two_mul α (s := -(t : ℤ)) (by omega), crZ_neg, crZ_natCast]
      by_cases hle : N - k ≤ 2 * LN N
      · rw [ite_eq_left ⟨hj1, ⟨t, ht⟩, by omega, hle⟩, ite_eq_right (by unfold LN at hle; omega),
          show (N - k) / 2 = t by omega]
        ring
      · rw [ite_eq_right (fun h => hle h.2.2.2), ite_eq_left (by unfold LN at hle; omega),
          show N / 2 = t by unfold LN at hle; omega]
        ring
    · rw [kap_of_not_even α (by rw [Int.even_iff]; omega),
        ite_eq_right (by rw [Nat.even_iff]; omega), ite_eq_right (by omega)]
      ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; ring

lemma Ebdry_eq {α : ℝ} (hN : 3 ≤ N) (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0)
    (x : ℝ) (j k : Fin N) :
    Ebdry α N x (j : ℕ) (k : ℕ) = Eeven α N x j k + Eedge α N x j k := by
  have hj := j.isLt; have hk := k.isLt
  rw [Ebdry, T1_eq α x hj, T3_eq α x hj hk, U4_eq α x hj hk, U2_eq α x hk]
  simp only [Eeven, Eedge, Matrix.add_apply, EedgeR0, EedgeC0, EedgeCN, EedgeRN,
    Nat.even_iff, Nat.odd_iff]
  split_ifs <;> first
    | ring1
    | (exfalso; omega)
    | linear_combination (corner (N := N) x hN (by omega) hsin)

/-! ## Lemma `lemma-commut` -/

/-- **Lemma `lemma-commut`** (commutK1) (l.1462), entrywise: for `N ≥ 3`,
`d/dx B_N(x) = [K_N, B_N(x)] + 𝓔_even(x) + 𝓔_edge(x)`. -/
theorem lemma_commut {α : ℝ} (hN : 3 ≤ N)
    (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0) (x : ℝ) (j k : Fin N) :
    HasDerivAt (fun y => BN α N y j k)
      ((KN α N * BN α N x - BN α N x * KN α N + Eeven α N x + Eedge α N x) j k) x := by
  convert hasDerivAt_BN_entry α x j k using 1
  rw [Matrix.add_apply, Matrix.add_apply, add_assoc, ← Ebdry_eq hN hsin, ← dBz_sub_comm hsin]
  ring

/-- **Lemma `lemma-commut`** for irrational `α`. -/
theorem lemma_commut_irrational {α : ℝ} (hα : Irrational α) (hN : 3 ≤ N) (x : ℝ)
    (j k : Fin N) :
    HasDerivAt (fun y => BN α N y j k)
      ((KN α N * BN α N x - BN α N x * KN α N + Eeven α N x + Eedge α N x) j k) x :=
  lemma_commut hN (sin_hyp_of_irrational hα N) x j k

/-- **Lemma `lemma-commut`** (commutK1) for the matrix-valued map `x ↦ B_N(x)`, with respect to
the product topology on matrices (equivalently, any matrix norm): `B_N'(x) = [K_N, B_N(x)] + 𝓔_even(x) + 𝓔_edge(x)`. -/
theorem lemma_commut_matrix {α : ℝ} (hN : 3 ≤ N)
    (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => BN α N y)
      (KN α N * BN α N x - BN α N x * KN α N + Eeven α N x + Eedge α N x) x := by
  exact (hasDerivAt_pi (φ := fun y => BN α N y)).2 fun j =>
    (hasDerivAt_pi (φ := fun y => BN α N y j)).2 fun k => lemma_commut hN hsin x j k

/-! ## The complex (Hermitian) version -/

lemma Eeven_symm (α : ℝ) (N : ℕ) (x : ℝ) (i k : Fin N) : Eeven α N x i k = Eeven α N x k i := by
  unfold Eeven
  congr 1
  apply propext; constructor <;> rintro ⟨h1, h2 | h2⟩ <;> tauto

lemma Eedge_symm (α : ℝ) (N : ℕ) (x : ℝ) (i k : Fin N) : Eedge α N x i k = Eedge α N x k i := by
  simp only [Eedge, Matrix.add_apply, EedgeR0, EedgeC0, EedgeCN, EedgeRN]
  ring

/-- **Lemma `lemma-commut`** for the complex Hermitian matrices `BNc`, `KNc`. -/
theorem lemma_commut_complex {α : ℝ} (hN : 3 ≤ N)
    (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0) (x : ℝ) (j k : Fin N) :
    HasDerivAt (fun y => BNc α N y j k)
      ((KNc α N * BNc α N x - BNc α N x * KNc α N + (Eeven α N x).map (fun r : ℝ => (r : ℂ)) +
        (Eedge α N x).map (fun r : ℝ => (r : ℂ))) j k) x := by
  refine (lemma_commut hN hsin x j k).ofReal_comp.congr_deriv ?_
  simp only [BNc, KNc, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul]

/-! ## Lemma `lemma-commut2` -/

/-- The boundary projection `P_N = Γ̂_N^* Γ̂_N` of (bp) (l.1271): the orthogonal projection onto
`span{e_0, e_{N-1}}`. -/
def PN (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => if (i : ℕ) = 0 ∨ (i : ℕ) = N - 1 then 1 else 0

/-- The paths `H_N^±(x) = B_N(x) ± C₀|J_n| P_N` of Lemma `lemma-commut2`, with the real
parameter `c = ±C₀|J_n|`. -/
def HN (α : ℝ) (N : ℕ) (c x : ℝ) : Matrix (Fin N) (Fin N) ℝ := BN α N x + c • PN N

/-- The error matrices (Epm) (l.1546): `𝓔^± = 𝓔_even + 𝓔_edge ∓ C₀|J_n| [K_N, P_N]`, with
`c = ±C₀|J_n|`. -/
def Epm (α : ℝ) (N : ℕ) (c x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Eeven α N x + Eedge α N x - c • (KN α N * PN N - PN N * KN α N)

/-- **Lemma `lemma-commut2`**, (commutK2) (l.1550): `d/dx H^± = [K_N, H^±] + 𝓔^±`. -/
theorem lemma_commut2 {α : ℝ} (hN : 3 ≤ N)
    (hsin : ∀ r : ℕ, 1 ≤ r → r ≤ N → sin (π * α * r) ≠ 0) (c x : ℝ) (j k : Fin N) :
    HasDerivAt (fun y => HN α N c y j k)
      ((KN α N * HN α N c x - HN α N c x * KN α N + Epm α N c x) j k) x := by
  have h := (lemma_commut hN hsin x j k).add_const (c * PN N j k)
  have e : KN α N * HN α N c x - HN α N c x * KN α N + Epm α N c x =
      KN α N * BN α N x - BN α N x * KN α N + Eeven α N x + Eedge α N x := by
    simp only [HN, Epm, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    abel
  rw [e]
  convert h using 1
  funext y
  simp only [HN, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- A square matrix whose entries vanish whenever both indices lie outside a finset `S` has rank
at most `2 |S|`. -/
theorem rank_le_of_interior_eq_zero {m R : Type*} [Fintype m] [DecidableEq m] [Field R]
    (M : Matrix m m R) (S : Finset m) (h : ∀ i k, i ∉ S → k ∉ S → M i k = 0) :
    M.rank ≤ 2 * S.card := by
  let A : Matrix m (S ⊕ S) R := Matrix.of fun i =>
    Sum.elim (fun s => if i = s then 1 else 0) (fun s => if i ∈ S then 0 else M i s)
  let B : Matrix (S ⊕ S) m R :=
    Matrix.of (Sum.elim (fun s k => M s k) (fun s k => if k = s then 1 else 0))
  have hAB : A * B = M := by
    ext i k
    simp only [A, B, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr]
    rw [Finset.sum_coe_sort S (fun s => (if i = s then (1 : R) else 0) * M s k),
      Finset.sum_coe_sort S (fun s => (if i ∈ S then 0 else M i s) * if k = s then 1 else 0)]
    by_cases hi : i ∈ S <;> by_cases hk : k ∈ S <;> simp [hi, hk, h i k]
  calc M.rank = (A * B).rank := by rw [hAB]
    _ ≤ B.rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card (S ⊕ S) := Matrix.rank_le_card_height _
    _ = 2 * S.card := by simp [Fintype.card_sum]; ring

/-- **Lemma `lemma-commut2`**, rank bound: `rk 𝓔^±(x) ≤ 4`. -/
theorem rank_Epm_le (α : ℝ) (hN : 3 ≤ N) (c x : ℝ) : (Epm α N c x).rank ≤ 4 := by
  let S : Finset (Fin N) := {⟨0, by omega⟩, ⟨N - 1, by omega⟩}
  have hS : S.card ≤ 2 := Finset.card_le_two
  refine (rank_le_of_interior_eq_zero _ S ?_).trans (by omega)
  intro i k hi hk
  have hi0 : (i : ℕ) ≠ 0 := fun h => hi (by simp [S, Fin.ext_iff, h])
  have hi1 : (i : ℕ) ≠ N - 1 := fun h => hi (by simp [S, Fin.ext_iff, h])
  have hk0 : (k : ℕ) ≠ 0 := fun h => hk (by simp [S, Fin.ext_iff, h])
  have hk1 : (k : ℕ) ≠ N - 1 := fun h => hk (by simp [S, Fin.ext_iff, h])
  simp [Epm, Eeven, Eedge, EedgeR0, EedgeC0, EedgeCN, EedgeRN, PN, Matrix.mul_diagonal,
    Matrix.diagonal_mul, hi0, hi1, hk0, hk1]

/-! ## The Hilbert–Schmidt estimates (Enorms) -/

/-- The squared Hilbert–Schmidt norm `‖E‖_{S_2}^2 = ∑_{i,k} E_{ik}^2` of a real matrix. -/
def hs2 (E : Matrix (Fin N) (Fin N) ℝ) : ℝ := ∑ i, ∑ k, E i k ^ 2

/-- Reindexing bound for double sums of squares of `if`-entries. -/
lemma dsum_ite_sq_le (C : Fin N → Fin N → Prop) [∀ i k, Decidable (C i k)]
    (v : Fin N → Fin N → ℝ) (t : Finset ℕ) (g : ℕ → ℝ) (φ : Fin N → Fin N → ℕ)
    (hg : ∀ b ∈ t, 0 ≤ g b) (hmap : ∀ i k, C i k → φ i k ∈ t ∧ v i k ^ 2 ≤ g (φ i k))
    (hinj : ∀ i k i' k', C i k → C i' k' → φ i k = φ i' k' → i = i' ∧ k = k') :
    ∑ i, ∑ k, (if C i k then v i k else 0) ^ 2 ≤ ∑ b ∈ t, g b := by
  classical
  rw [← Fintype.sum_prod_type']
  have e : ∀ p : Fin N × Fin N, (if C p.1 p.2 then v p.1 p.2 else 0) ^ 2 =
      if C p.1 p.2 then v p.1 p.2 ^ 2 else 0 := fun p => by split_ifs <;> simp
  simp only [e]
  rw [← Finset.sum_filter]
  set s := Finset.univ.filter (fun p : Fin N × Fin N => C p.1 p.2)
  have hs : ∀ p ∈ s, C p.1 p.2 := fun p hp => (Finset.mem_filter.1 hp).2
  calc ∑ p ∈ s, v p.1 p.2 ^ 2 ≤ ∑ p ∈ s, g (φ p.1 p.2) :=
        Finset.sum_le_sum fun p hp => (hmap _ _ (hs p hp)).2
    _ = ∑ b ∈ s.image (fun p => φ p.1 p.2), g b := by
        rw [Finset.sum_image]
        intro p hp p' hp' hpp
        obtain ⟨h1, h2⟩ := hinj _ _ _ _ (hs p hp) (hs p' hp') hpp
        exact Prod.ext h1 h2
    _ ≤ ∑ b ∈ t, g b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
          exact (hmap _ _ (hs p hp)).1
        · intro b hb _; exact hg b hb

lemma neg_one_pow_sq (m : ℕ) : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

/-- (Enorms), first line: `‖𝓔_even(x)‖_{S_2}^2 ≤ 2(2π)^2 = 8π^2`. -/
theorem Eeven_hs (α : ℝ) (hN : 3 ≤ N) (x : ℝ) : hs2 (Eeven α N x) ≤ 8 * π ^ 2 := by
  have := (show ∑ b ∈ Finset.range 2, (4 * π ^ 2) = 8 * π ^ 2 by simp; ring)
  rw [← this]
  apply dsum_ite_sq_le _ _ _ _ (fun i _ => if (i : ℕ) = 0 then 0 else 1)
  · intro b _; positivity
  · intro i k hc
    refine ⟨by split_ifs <;> simp, ?_⟩
    rw [mul_pow, mul_pow, neg_one_pow_sq]
    nlinarith [cos_sq_le_one (π * (α * N / 2 + x)), sq_nonneg π]
  · intro i k i' k' h h' he
    obtain ⟨_, h⟩ := h
    obtain ⟨_, h'⟩ := h'
    split_ifs at he <;> exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

lemma Eedge_sq (α : ℝ) (x : ℝ) (i k : Fin N) :
    Eedge α N x i k ^ 2 = EedgeR0 α N x i k ^ 2 + EedgeC0 α N x i k ^ 2 +
      EedgeCN α N x i k ^ 2 + EedgeRN α N x i k ^ 2 := by
  have := i.isLt; have := k.isLt
  simp only [Eedge, Matrix.add_apply, EedgeR0, EedgeC0, EedgeCN, EedgeRN]
  split_ifs <;> simp only [Nat.odd_iff, Nat.even_iff, LN] at * <;>
    first | ring1 | (exfalso; omega)

/-- (Enorms), second line:
`‖𝓔_edge(x)‖_{S_2}^2 ≤ 2(|2 sin πx|^2 + |2 sin π(x+Nα)|^2) ∑_{r=1}^L |c_r|^2`. -/
theorem Eedge_hs (α : ℝ) (x : ℝ) :
    hs2 (Eedge α N x) ≤ 2 * ((2 * sin (π * x)) ^ 2 + (2 * sin (π * (x + N * α))) ^ 2) *
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 := by
  have hsplit : hs2 (Eedge α N x) = hs2 (EedgeR0 α N x) + hs2 (EedgeC0 α N x) +
      hs2 (EedgeCN α N x) + hs2 (EedgeRN α N x) := by
    simp only [hs2, Eedge_sq, Finset.sum_add_distrib]
  have e : 2 * ((2 * sin (π * x)) ^ 2 + (2 * sin (π * (x + N * α))) ^ 2) *
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 =
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 * (2 * sin (π * x)) ^ 2 +
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 * (2 * sin (π * x)) ^ 2 +
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 * (2 * sin (π * (x + N * α))) ^ 2 +
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 * (2 * sin (π * (x + N * α))) ^ 2 := by
    simp only [← Finset.sum_mul]; ring
  rw [hsplit, e]
  have hg : ∀ (s : ℝ), ∀ b ∈ Finset.Icc 1 (LN N), 0 ≤ cr α b ^ 2 * s ^ 2 :=
    fun s b _ => by positivity
  gcongr
  · apply dsum_ite_sq_le _ _ _ _ (fun _ k => ((k : ℕ) + 1) / 2) (hg _)
    · rintro i k ⟨_, ⟨t, ht⟩, hlt⟩
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by rw [neg_mul, neg_sq, mul_pow]⟩
    · rintro i k i' k' ⟨h1, ⟨t, ht⟩, _⟩ ⟨h1', ⟨t', ht'⟩, _⟩ he
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · apply dsum_ite_sq_le _ _ _ _ (fun i _ => ((i : ℕ) + 1) / 2) (hg _)
    · rintro i k ⟨_, ⟨t, ht⟩, hlt⟩
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by rw [neg_mul, neg_sq, mul_pow]⟩
    · rintro i k i' k' ⟨h1, ⟨t, ht⟩, _⟩ ⟨h1', ⟨t', ht'⟩, _⟩ he
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · apply dsum_ite_sq_le _ _ _ _ (fun i _ => (N - (i : ℕ)) / 2) (hg _)
    · rintro i k ⟨_, ⟨t, ht⟩, h2, hle⟩
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by rw [mul_pow]⟩
    · rintro i k i' k' ⟨h1, ⟨t, ht⟩, _⟩ ⟨h1', ⟨t', ht'⟩, _⟩ he
      have := i.isLt; have := i'.isLt
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · apply dsum_ite_sq_le _ _ _ _ (fun _ k => (N - (k : ℕ)) / 2) (hg _)
    · rintro i k ⟨_, ⟨t, ht⟩, h2, hle⟩
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by rw [mul_pow]⟩
    · rintro i k i' k' ⟨h1, ⟨t, ht⟩, _⟩ ⟨h1', ⟨t', ht'⟩, _⟩ he
      have := k.isLt; have := k'.isLt
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

lemma KN_of_odd (α : ℝ) (i k : Fin N) (h : ((k : ℕ) + (i : ℕ)) % 2 = 1) : KN α N i k = 0 := by
  unfold KN
  rw [ite_eq_right (by rw [Nat.even_iff]; omega), ite_eq_right (by rw [Nat.even_iff]; omega)]

lemma commKP_apply (α : ℝ) (i k : Fin N) :
    (KN α N * PN N - PN N * KN α N) i k =
      KN α N i k * ((if (k : ℕ) = 0 ∨ (k : ℕ) = N - 1 then 1 else 0) -
        (if (i : ℕ) = 0 ∨ (i : ℕ) = N - 1 then 1 else 0)) := by
  simp only [PN, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- (Enorms), third line: `‖[K_N, P_N]‖_{S_2}^2 ≤ 4 ∑_{r=1}^L |c_r|^2`. -/
theorem commKP_hs (α : ℝ) (hN : 3 ≤ N) :
    hs2 (KN α N * PN N - PN N * KN α N) ≤ 4 * ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 := by
  -- the four families: row `0`, row `N-1`, column `0`, column `N-1` (outside the corners)
  have hsq : ∀ i k : Fin N, (KN α N * PN N - PN N * KN α N) i k ^ 2 =
      (if (i : ℕ) = 0 ∧ (k : ℕ) ≠ 0 ∧ (k : ℕ) ≠ N - 1 ∧ (k : ℕ) % 2 = 0 then
        KN α N i k else 0) ^ 2 +
      (if (i : ℕ) = N - 1 ∧ (k : ℕ) ≠ 0 ∧ (k : ℕ) ≠ N - 1 ∧ (N - 1 - k) % 2 = 0 then
        KN α N i k else 0) ^ 2 +
      (if (k : ℕ) = 0 ∧ (i : ℕ) ≠ 0 ∧ (i : ℕ) ≠ N - 1 ∧ (i : ℕ) % 2 = 0 then
        KN α N i k else 0) ^ 2 +
      (if (k : ℕ) = N - 1 ∧ (i : ℕ) ≠ 0 ∧ (i : ℕ) ≠ N - 1 ∧ (N - 1 - i) % 2 = 0 then
        KN α N i k else 0) ^ 2 := by
    intro i k
    have := i.isLt; have := k.isLt
    rw [commKP_apply]
    split_ifs <;> first | ring1 | (exfalso; omega) | (rw [KN_of_odd α i k (by omega)]; ring)
  have h4 : 4 * ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 =
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 + ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 +
      ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 + ∑ r ∈ Finset.Icc 1 (LN N), cr α r ^ 2 := by ring
  rw [hs2]
  simp only [hsq, Finset.sum_add_distrib]
  rw [h4]
  have hg : ∀ b ∈ Finset.Icc 1 (LN N), 0 ≤ cr α b ^ 2 := fun b _ => sq_nonneg _
  gcongr
  · apply dsum_ite_sq_le _ _ _ _ (fun _ k => (k : ℕ) / 2) hg
    · rintro i k ⟨h0, hk0, hk1, he⟩
      have := k.isLt
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by unfold LN; omega⟩, le_of_eq ?_⟩
      unfold KN; rw [ite_eq_left ⟨by omega, by rw [Nat.even_iff]; omega⟩]
      congr 3; omega
    · rintro i k i' k' ⟨h0, -, -, he⟩ ⟨h0', -, -, he'⟩ hh
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · apply dsum_ite_sq_le _ _ _ _ (fun _ k => (N - 1 - (k : ℕ)) / 2) hg
    · rintro i k ⟨h0, hk0, hk1, he⟩
      have := k.isLt
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by unfold LN; omega⟩, le_of_eq ?_⟩
      unfold KN
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by rw [Nat.even_iff]; omega⟩, neg_sq]
      congr 3; omega
    · rintro i k i' k' ⟨h0, -, -, he⟩ ⟨h0', -, -, he'⟩ hh
      have := k.isLt; have := k'.isLt
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · apply dsum_ite_sq_le _ _ _ _ (fun i _ => (i : ℕ) / 2) hg
    · rintro i k ⟨h0, hk0, hk1, he⟩
      have := i.isLt
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by unfold LN; omega⟩, le_of_eq ?_⟩
      unfold KN
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by rw [Nat.even_iff]; omega⟩, neg_sq]
      congr 3; omega
    · rintro i k i' k' ⟨h0, -, -, he⟩ ⟨h0', -, -, he'⟩ hh
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · apply dsum_ite_sq_le _ _ _ _ (fun i _ => (N - 1 - (i : ℕ)) / 2) hg
    · rintro i k ⟨h0, hk0, hk1, he⟩
      have := i.isLt
      refine ⟨Finset.mem_Icc.2 ⟨by omega, by unfold LN; omega⟩, le_of_eq ?_⟩
      unfold KN; rw [ite_eq_left ⟨by omega, by rw [Nat.even_iff]; omega⟩]
      congr 3; omega
    · rintro i k i' k' ⟨h0, -, -, he⟩ ⟨h0', -, -, he'⟩ hh
      have := i.isLt; have := i'.isLt
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-! ## The arithmetic estimate for `∑ |c_r|^2` (l.1612–1636) -/

/-- The distance `‖t‖_𝕋` from `t` to the nearest integer. -/
def distZ (t : ℝ) : ℝ := |t - round t|

lemma distZ_le (t : ℝ) (n : ℤ) : distZ t ≤ |t - n| := round_le t n

/-- `|sin πt| ≥ 2 ‖t‖_𝕋`. -/
lemma two_distZ_le_abs_sin (t : ℝ) : 2 * distZ t ≤ |sin (π * t)| := by
  set s := t - round t with hs
  have hs2 : |s| ≤ 1 / 2 := abs_sub_round t
  have hsin : |sin (π * t)| = |sin (π * s)| := by
    rw [show π * t = π * s + (round t : ℤ) * π by rw [hs]; ring, Real.sin_add_int_mul_pi,
      abs_mul]
    simp
  have habs : |sin (π * s)| = sin (π * |s|) := by
    have hnn : 0 ≤ sin (π * |s|) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos, abs_nonneg s])
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h] at hnn ⊢; exact abs_of_nonneg hnn
    · rw [abs_of_nonpos h] at hnn ⊢
      rw [mul_neg, Real.sin_neg] at hnn ⊢
      rw [abs_of_nonpos (by linarith)]
  rw [hsin, habs, distZ]
  have hj := Real.mul_le_sin (x := π * |s|) (by positivity) (by nlinarith [Real.pi_pos])
  have hπ := Real.pi_pos
  calc 2 * |s| = 2 / π * (π * |s|) := by field_simp
    _ ≤ _ := hj

lemma sum_range_inv_sq_le (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((m : ℝ) + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h : 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / (((m + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_range_inv_sq_le_two (m : ℕ) :
    ∑ k ∈ Finset.range m, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  rcases m with _ | m
  · simp
  · have := sum_range_inv_sq_le m
    have : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith

/-- `δ`-separated points in `[δ, ∞)`: the largest one is `≥ |T| δ`, and
`∑_{y ∈ T} y^{-2} ≤ δ^{-2} ∑_{k=1}^{|T|} k^{-2}`. -/
lemma sep_points_aux {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) :
    (∀ y ∈ T, δ ≤ y) → (∀ y ∈ T, ∀ z ∈ T, y ≠ z → δ ≤ |y - z|) →
      (∀ y ∈ T, (∀ z ∈ T, z ≤ y) → T.card * δ ≤ y) ∧
      ∑ y ∈ T, 1 / y ^ 2 ≤ (∑ k ∈ Finset.range T.card, 1 / ((k : ℝ) + 1) ^ 2) / δ ^ 2 := by
  induction T using Finset.induction_on_max with
  | empty => intro _ _; simp
  | insert a s hlt ih =>
    intro hpos hsep
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    obtain ⟨ih1, ih2⟩ := ih (fun y hy => hpos y (Finset.mem_insert_of_mem hy))
      (fun y hy z hz => hsep y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz))
    have ha : (s.card + 1 : ℝ) * δ ≤ a := by
      rcases s.eq_empty_or_nonempty with he | hne
      · subst he; simpa using hpos a (Finset.mem_insert_self a ∅)
      · have hm := ih1 (s.max' hne) (s.max'_mem hne) (fun z hz => s.le_max' z hz)
        have hlt' := hlt _ (s.max'_mem hne)
        have hd := hsep a (Finset.mem_insert_self a s) (s.max' hne)
          (Finset.mem_insert_of_mem (s.max'_mem hne)) hlt'.ne'
        rw [abs_of_pos (by linarith)] at hd
        linarith
    rw [Finset.card_insert_of_notMem has]
    refine ⟨?_, ?_⟩
    · intro y hy hmax
      rcases Finset.mem_insert.1 hy with rfl | hy
      · push_cast; exact ha
      · exact absurd (hmax a (Finset.mem_insert_self a s)) (not_le.2 (hlt y hy))
    · rw [Finset.sum_insert has, Finset.sum_range_succ, add_div]
      have hpos' : 0 < (s.card + 1 : ℝ) * δ := by positivity
      have h1 : 1 / a ^ 2 ≤ 1 / ((s.card : ℝ) + 1) ^ 2 / δ ^ 2 :=
        calc 1 / a ^ 2 ≤ 1 / ((s.card + 1 : ℝ) * δ) ^ 2 :=
              one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos'.le ha 2)
          _ = 1 / ((s.card : ℝ) + 1) ^ 2 / δ ^ 2 := by field_simp
      linarith

lemma sep_points {δ : ℝ} (hδ : 0 < δ) (T : Finset ℝ) (hpos : ∀ y ∈ T, δ ≤ y)
    (hsep : ∀ y ∈ T, ∀ z ∈ T, y ≠ z → δ ≤ |y - z|) : ∑ y ∈ T, 1 / y ^ 2 ≤ 2 / δ ^ 2 :=
  (sep_points_aux hδ T hpos hsep).2.trans
    (div_le_div_of_nonneg_right (sum_range_inv_sq_le_two _) (by positivity))

/-- One "side" of the circle: the points `rα` whose representative `rα - round(rα)` has a fixed
sign. -/
lemma side_bound {α δ : ℝ} (hδ : 0 < δ) (A : Finset ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hside : ∀ r ∈ A, distZ (r * α) = σ * (r * α - round (r * α)))
    (h0 : ∀ r ∈ A, δ ≤ distZ (r * α))
    (hsep : ∀ r ∈ A, ∀ r' ∈ A, r ≠ r' → δ ≤ distZ (r * α - r' * α)) :
    ∑ r ∈ A, 1 / distZ (r * α) ^ 2 ≤ 2 / δ ^ 2 := by
  have hd : ∀ r ∈ A, ∀ r' ∈ A, r ≠ r' → δ ≤ |distZ (r * α) - distZ (r' * α)| := by
    intro r hr r' hr' hne
    rw [hside r hr, hside r' hr']
    have := (hsep r hr r' hr' hne).trans
      (distZ_le _ (round ((r : ℝ) * α) - round ((r' : ℝ) * α)))
    rcases hσ with rfl | rfl
    · convert this using 2; push_cast; ring
    · rw [show -1 * ((r : ℝ) * α - round ((r : ℝ) * α)) - -1 * (r' * α - round (r' * α)) =
        -((r * α - r' * α) - ((round ((r : ℝ) * α) - round ((r' : ℝ) * α) : ℤ) : ℝ)) by
          push_cast; ring, abs_neg]
      exact this
  rw [← Finset.sum_image (f := fun y : ℝ => 1 / y ^ 2) (g := fun r : ℕ => distZ (r * α))]
  · apply sep_points hδ
    · intro y hy
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      exact h0 r hr
    · intro y hy z hz hyz
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hz
      exact hd r hr r' hr' (fun h => hyz (by rw [h]))
  · intro r hr r' hr' he
    by_contra hne
    have := hd r hr r' hr' hne
    simp only at he
    rw [he, sub_self, abs_zero] at this
    linarith

/-- The arithmetic estimate of the proof of Prop. `prop-phase-variation` (l.1612–1636), in
abstract form: if the points `rα`, `1 ≤ r ≤ L`, are at distance `≥ δ` from `0` and pairwise at
distance `≥ δ` on `𝕋`, then `∑_{r=1}^L 1/sin²(παr) ≤ 1/δ²`.  (For `L ≤ q_n/2` the paper uses
`δ = 1/(2q_n)`, giving `∑ ≤ 4 q_n²`.) -/
theorem sum_inv_sin_sq_le {α δ : ℝ} (hδ : 0 < δ) (L : ℕ)
    (h0 : ∀ r ∈ Finset.Icc 1 L, δ ≤ distZ (r * α))
    (hsep : ∀ r ∈ Finset.Icc 1 L, ∀ r' ∈ Finset.Icc 1 L, r ≠ r' →
      δ ≤ distZ (r * α - r' * α)) :
    ∑ r ∈ Finset.Icc 1 L, 1 / sin (π * α * r) ^ 2 ≤ 1 / δ ^ 2 := by
  set I := Finset.Icc 1 L
  have hterm : ∀ r ∈ I, 1 / sin (π * α * r) ^ 2 ≤ 1 / 4 * (1 / distZ (r * α) ^ 2) := by
    intro r hr
    have hdpos : 0 < distZ (r * α) := hδ.trans_le (h0 r hr)
    have h2 := two_distZ_le_abs_sin (r * α)
    rw [show π * (r * α) = π * α * r by ring] at h2
    have : (2 * distZ (r * α)) ^ 2 ≤ sin (π * α * r) ^ 2 := by
      rw [← sq_abs (sin _)]; exact pow_le_pow_left₀ (by positivity) h2 2
    calc 1 / sin (π * α * r) ^ 2 ≤ 1 / (2 * distZ (r * α)) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) this
      _ = _ := by field_simp; ring
  calc ∑ r ∈ I, 1 / sin (π * α * r) ^ 2 ≤ ∑ r ∈ I, 1 / 4 * (1 / distZ (r * α) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = 1 / 4 * (∑ r ∈ I.filter (fun r : ℕ => 0 ≤ (r : ℝ) * α - round ((r : ℝ) * α)),
          1 / distZ (r * α) ^ 2 +
        ∑ r ∈ I.filter (fun r : ℕ => ¬ 0 ≤ (r : ℝ) * α - round ((r : ℝ) * α)),
          1 / distZ (r * α) ^ 2) := by
        rw [Finset.sum_filter_add_sum_filter_not, Finset.mul_sum]
    _ ≤ 1 / 4 * (2 / δ ^ 2 + 2 / δ ^ 2) := by
        gcongr
        · apply side_bound hδ _ 1 (Or.inl rfl)
          · intro r hr
            rw [distZ, one_mul, abs_of_nonneg (Finset.mem_filter.1 hr).2]
          · exact fun r hr => h0 r (Finset.mem_filter.1 hr).1
          · exact fun r hr r' hr' => hsep r (Finset.mem_filter.1 hr).1 r'
              (Finset.mem_filter.1 hr').1
        · apply side_bound hδ _ (-1) (Or.inr rfl)
          · intro r hr
            rw [distZ, abs_of_neg (not_le.1 (Finset.mem_filter.1 hr).2)]; ring
          · exact fun r hr => h0 r (Finset.mem_filter.1 hr).1
          · exact fun r hr r' hr' => hsep r (Finset.mem_filter.1 hr).1 r'
              (Finset.mem_filter.1 hr').1
    _ = 1 / δ ^ 2 := by ring

lemma cr_sq (α : ℝ) (r : ℕ) : cr α r ^ 2 = π ^ 2 / 4 * (1 / sin (π * α * r) ^ 2) := by
  rw [cr, div_pow, mul_pow, neg_one_pow_sq, mul_pow]
  ring

/-- Consequently `∑_{r=1}^L |c_r|^2 ≤ π² / (4δ²)` under the same separation hypotheses. -/
theorem sum_cr_sq_le {α δ : ℝ} (hδ : 0 < δ) (L : ℕ)
    (h0 : ∀ r ∈ Finset.Icc 1 L, δ ≤ distZ (r * α))
    (hsep : ∀ r ∈ Finset.Icc 1 L, ∀ r' ∈ Finset.Icc 1 L, r ≠ r' →
      δ ≤ distZ (r * α - r' * α)) :
    ∑ r ∈ Finset.Icc 1 L, cr α r ^ 2 ≤ π ^ 2 / (4 * δ ^ 2) := by
  simp only [cr_sq, ← Finset.mul_sum]
  calc π ^ 2 / 4 * ∑ r ∈ Finset.Icc 1 L, 1 / sin (π * α * r) ^ 2 ≤ π ^ 2 / 4 * (1 / δ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_inv_sin_sq_le hδ L h0 hsep) (by positivity)
    _ = _ := by field_simp

end LaxPair

end CAH
