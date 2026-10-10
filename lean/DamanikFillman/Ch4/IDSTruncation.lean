/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.3: the integrated density of states via Dirichlet truncations

The density of states measure is the almost sure weak limit of the normalized eigenvalue
counting measures of the Dirichlet truncations `H_{ω,N} = H_ω|_{[1,N]}` (cf. Theorem 4.3.8).

## Main definitions
* `DF.hz V f n = f(n+1) + f(n-1) + V(n) f(n)` — the Schrödinger difference expression acting on
  arbitrary functions `ℤ → ℂ`;
* `DF.eigMeasure hA = N⁻¹ ∑ᵢ δ_{λᵢ}` — the normalized eigenvalue counting measure of a Hermitian
  `N × N` matrix;
* `E.dkT ω N` — the eigenvalue counting measure of the Dirichlet truncation `H_{ω,N}`.

## Main results
* `DF.truncMat_isHermitian`, `DF.abs_eigenvalues_truncMat_le` — `H_Λ` is Hermitian with
  eigenvalues in `[-(2 + M), 2 + M]` if `|V| ≤ M`;
* `DF.trace_pow_eq_sum_eigenvalues`, `DF.det_sub_eq_prod_eigenvalues` — trace of powers and
  characteristic polynomial of a Hermitian matrix in terms of its eigenvalues;
* `DF.truncMat_pow_diag` — locality: `(H_N^k)_{ii} = ⟨δ_{i+1}, H^k δ_{i+1}⟩` away from the
  boundary; `DF.norm_trace_pow_sub_le` — the resulting trace comparison
  `|Tr H_N^k - ∑_{n=1}^N ⟨δₙ, H^k δₙ⟩| ≤ 4k(2 + M)^k`;
* `E.ae_tendsto_dkT` — **Theorem 4.3.8**: almost surely, `dk^T_{ω,N} → dk` weakly;
* `E.integral_log_dkT` — `∫ log |z - x| dk^T_{ω,N}(x) = N⁻¹ log |det(z - H_{ω,N})|`.

## Deviation
The book's numbering of this result is not checked against the text; the statement is the
standard one (e.g. Damanik, *A survey of Kotani theory*, §1).
-/
import DamanikFillman.Ch4.IDS
import DamanikFillman.Ch2.Truncation

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter L2 Matrix

namespace DF

/-! ### The difference expression on functions -/

/-- `hz V f n = f(n+1) + f(n-1) + V(n) f(n)`. -/
def hz (V : ℤ → ℝ) (f : ℤ → ℂ) (n : ℤ) : ℂ := f (n + 1) + f (n - 1) + (V n : ℂ) * f n

/-- The function `δₙ : ℤ → ℂ`. -/
def dltF (n : ℤ) (m : ℤ) : ℂ := if m = n then 1 else 0

lemma coe_dlt (n : ℤ) : ⇑(dlt n) = dltF n := funext fun m => dlt_apply n m

lemma schr_pow_apply {V : ℤ → ℝ} (hV : BddPot V) (k : ℕ) (φ : L2 ℤ) (n : ℤ) :
    ((schr V ^ k) φ) n = (hz V)^[k] (⇑φ) n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, schr_apply hV, Function.iterate_succ_apply']
    simp only [hz, ih]

lemma inner_dlt_schr_pow {V : ℤ → ℝ} (hV : BddPot V) (k : ℕ) (n : ℤ) :
    ⟪dlt n, (schr V ^ k) (dlt n)⟫_ℂ = (hz V)^[k] (dltF n) n := by
  rw [inner_dlt, schr_pow_apply hV, coe_dlt]

lemma norm_hz_le {V : ℤ → ℝ} {M : ℝ} (hM : ∀ n, |V n| ≤ M) {f : ℤ → ℂ} {B : ℝ}
    (hB : ∀ n, ‖f n‖ ≤ B) (n : ℤ) : ‖hz V f n‖ ≤ (2 + M) * B := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hV : ‖(V n : ℂ)‖ ≤ M := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM n
  have h1 := hB (n + 1)
  have h2 := hB (n - 1)
  have h3 := hB n
  have h4 : ‖(V n : ℂ)‖ * ‖f n‖ ≤ M * B := mul_le_mul hV h3 (norm_nonneg _) hM0
  unfold hz
  calc ‖f (n + 1) + f (n - 1) + (V n : ℂ) * f n‖
      ≤ ‖f (n + 1)‖ + ‖f (n - 1)‖ + ‖(V n : ℂ)‖ * ‖f n‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
        linarith [norm_add_le (f (n + 1)) (f (n - 1))]
    _ ≤ (2 + M) * B := by linarith

lemma norm_iterate_hz_le {V : ℤ → ℝ} {M : ℝ} (hM : ∀ n, |V n| ≤ M) {f : ℤ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (k : ℕ) (n : ℤ) : ‖(hz V)^[k] f n‖ ≤ (2 + M) ^ k := by
  induction k generalizing n with
  | zero => simpa using hf n
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    exact norm_hz_le hM ih n

lemma norm_dltF_le (n m : ℤ) : ‖dltF n m‖ ≤ 1 := by
  unfold dltF; split_ifs <;> simp

/-- `(hz V)^[j] δₙ` is supported in `[n - j, n + j]`. -/
lemma iterate_hz_dltF_eq_zero (V : ℤ → ℝ) (n : ℤ) (j : ℕ) (m : ℤ)
    (hm : m < n - j ∨ n + j < m) : (hz V)^[j] (dltF n) m = 0 := by
  induction j generalizing m with
  | zero =>
    simp only [Function.iterate_zero, id, dltF]
    rw [if_neg]; push_cast at hm; omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    show (hz V)^[j] (dltF n) (m + 1) + (hz V)^[j] (dltF n) (m - 1) +
      (V m : ℂ) * (hz V)^[j] (dltF n) m = 0
    push_cast at hm
    rw [ih (m + 1) (by omega), ih (m - 1) (by omega), ih m (by omega)]
    ring

/-! ### Dirichlet truncations -/

/-- Extension of `v : Fin N → ℂ` to the sites `[1, N]` (index `i` ↔ site `i + 1`). -/
def iext {N : ℕ} (v : Fin N → ℂ) (n : ℤ) : ℂ := vext v (n - 1)

lemma iext_truncMat_mulVec (V : ℤ → ℝ) {N : ℕ} (v : Fin N → ℂ) (n : ℤ) :
    iext (truncMat V 0 N *ᵥ v) n = if 1 ≤ n ∧ n ≤ N then hz V (iext v) n else 0 := by
  unfold iext
  split_ifs with h
  · have hi : 0 ≤ n - 1 ∧ n - 1 < N := by omega
    rw [vext, dif_pos hi]
    set i : Fin N := ⟨(n - 1).toNat, by omega⟩ with hidef
    have hi' : ((i : ℕ) : ℤ) = n - 1 := by simp only [hidef]; omega
    rw [truncMat_mulVec V 0 v i, ← vext_coe v i, hi']
    simp only [hz]
    rw [show (0 : ℤ) + 1 + (n - 1) = n by ring, show n - 1 + 1 = n by ring,
      show n + 1 - 1 = n by ring]
    ring
  · by_cases h1 : n - 1 < 0
    · exact vext_of_neg _ h1
    · exact vext_of_ge _ (by omega)

lemma norm_iext_le {N : ℕ} {v : Fin N → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i, ‖v i‖ ≤ B)
    (n : ℤ) : ‖iext v n‖ ≤ B := by
  unfold iext vext
  split_ifs
  · exact hB _
  · simpa using hB0

lemma iext_single {N : ℕ} (i : Fin N) (n : ℤ) (hi : ((i : ℕ) : ℤ) = n - 1) :
    iext (Pi.single i (1 : ℂ)) = dltF n := by
  funext m
  unfold iext dltF vext
  split_ifs with h1 h2 h2
  · rw [Pi.single_apply, if_pos]
    ext
    simp only
    omega
  · rw [Pi.single_apply, if_neg]
    intro h
    apply h2
    have := congrArg Fin.val h
    simp only at this
    omega
  · exfalso
    apply h1
    omega
  · rfl

/-- **Locality**: away from the boundary, powers of the truncation agree with powers of `H`. -/
theorem iext_truncMat_pow_single (V : ℤ → ℝ) {N : ℕ} (i : Fin N) (n : ℤ)
    (hi : ((i : ℕ) : ℤ) = n - 1) (k : ℕ) (hk1 : 1 ≤ n - k) (hk2 : n + k ≤ N) :
    iext ((truncMat V 0 N ^ k) *ᵥ Pi.single i 1) = (hz V)^[k] (dltF n) := by
  have key : ∀ j : ℕ, j ≤ k →
      iext ((truncMat V 0 N ^ j) *ᵥ Pi.single i 1) = (hz V)^[j] (dltF n) := by
    intro j hj
    induction j with
    | zero => simp only [pow_zero, one_mulVec, Function.iterate_zero, id]; exact iext_single i n hi
    | succ j ih =>
      funext m
      rw [pow_succ', ← mulVec_mulVec, iext_truncMat_mulVec, ih (by omega),
        Function.iterate_succ_apply']
      split_ifs with h
      · rfl
      · rw [← Function.iterate_succ_apply' (hz V)]
        exact (iterate_hz_dltF_eq_zero V n (j + 1) m (by push_cast; omega)).symm
  exact key k le_rfl

lemma mulVec_single_apply_self {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    (A *ᵥ Pi.single i 1) i = A i i := by
  simp [mulVec, dotProduct, Pi.single_apply]

lemma iext_coe_succ {N : ℕ} (v : Fin N → ℂ) (i : Fin N) : iext v ((i : ℤ) + 1) = v i := by
  unfold iext
  rw [show ((i : ℤ) + 1 - 1) = (i : ℤ) by ring, vext_coe]

/-- **Locality**, diagonal entries: `(H_N^k)_{ii} = ⟨δ_{i+1}, H^k δ_{i+1}⟩` if `i` has distance
at least `k` from the boundary. -/
theorem truncMat_pow_diag (V : ℤ → ℝ) {N : ℕ} (i : Fin N) (k : ℕ) (hk1 : k ≤ (i : ℕ))
    (hk2 : (i : ℕ) + k + 1 ≤ N) :
    (truncMat V 0 N ^ k) i i = (hz V)^[k] (dltF ((i : ℤ) + 1)) ((i : ℤ) + 1) := by
  rw [← mulVec_single_apply_self (truncMat V 0 N ^ k) i, ← iext_coe_succ,
    iext_truncMat_pow_single V i ((i : ℤ) + 1) (by ring) k (by omega) (by omega)]

lemma norm_iext_truncMat_pow_single_le {V : ℤ → ℝ} {M : ℝ} (hM : ∀ n, |V n| ≤ M) {N : ℕ}
    (i : Fin N) (k : ℕ) (m : ℤ) :
    ‖iext ((truncMat V 0 N ^ k) *ᵥ Pi.single i 1) m‖ ≤ (2 + M) ^ k := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  induction k generalizing m with
  | zero =>
    simp only [pow_zero, one_mulVec]
    refine norm_iext_le zero_le_one (fun j => ?_) m
    rw [Pi.single_apply]; split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec, iext_truncMat_mulVec]
    split_ifs
    · rw [pow_succ']; exact norm_hz_le hM ih m
    · rw [norm_zero]; positivity

lemma norm_truncMat_pow_diag_le {V : ℤ → ℝ} {M : ℝ} (hM : ∀ n, |V n| ≤ M) {N : ℕ}
    (i : Fin N) (k : ℕ) : ‖(truncMat V 0 N ^ k) i i‖ ≤ (2 + M) ^ k := by
  rw [← mulVec_single_apply_self (truncMat V 0 N ^ k) i, ← iext_coe_succ]
  exact norm_iext_truncMat_pow_single_le hM i k _

/-- Trace comparison: `|Tr H_N^k - ∑_{n=1}^N ⟨δₙ, H^k δₙ⟩| ≤ 4k(2 + M)^k`. -/
theorem norm_trace_pow_sub_le {V : ℤ → ℝ} {M : ℝ} (hM : ∀ n, |V n| ≤ M) (N k : ℕ) :
    ‖(truncMat V 0 N ^ k).trace -
        ∑ j ∈ Finset.range N, (hz V)^[k] (dltF ((j : ℤ) + 1)) ((j : ℤ) + 1)‖ ≤
      4 * k * (2 + M) ^ k := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set C : ℝ := (2 + M) ^ k with hC
  have hC0 : 0 ≤ C := by positivity
  set f : ℕ → ℂ := fun j => if h : j < N then (truncMat V 0 N ^ k) ⟨j, h⟩ ⟨j, h⟩ else 0
  set g : ℕ → ℂ := fun j => (hz V)^[k] (dltF ((j : ℤ) + 1)) ((j : ℤ) + 1)
  have htr : (truncMat V 0 N ^ k).trace = ∑ j ∈ Finset.range N, f j := by
    rw [Matrix.trace, ← Fin.sum_univ_eq_sum_range f N]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, dif_pos i.2, Matrix.diag_apply]
  rw [htr, ← Finset.sum_sub_distrib]
  have hpt : ∀ j ∈ Finset.range N, ‖f j - g j‖ ≤
      if j < k ∨ N < j + k + 1 then 2 * C else 0 := by
    intro j hj
    have hjN : j < N := Finset.mem_range.1 hj
    split_ifs with hb
    · have h1 : ‖f j‖ ≤ C := by
        simp only [f, dif_pos hjN]; exact norm_truncMat_pow_diag_le hM _ k
      have h2 : ‖g j‖ ≤ C := norm_iterate_hz_le hM (norm_dltF_le _) k _
      calc ‖f j - g j‖ ≤ ‖f j‖ + ‖g j‖ := norm_sub_le _ _
        _ ≤ 2 * C := by linarith
    · push_neg at hb
      have : f j = g j := by
        simp only [f, g, dif_pos hjN]
        exact truncMat_pow_diag V ⟨j, hjN⟩ k hb.1 (by simp only; omega)
      rw [this, sub_self, norm_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range N).filter (fun j => j < k ∨ N < j + k + 1)).card ≤ 2 * k := by
    have hsub : (Finset.range N).filter (fun j => j < k ∨ N < j + k + 1) ⊆
        Finset.range k ∪ Finset.Ico (N - k) N := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_range, Nat.card_Ico]
    omega
  have hcard' : (((Finset.range N).filter (fun j => j < k ∨ N < j + k + 1)).card : ℝ) ≤
      2 * k := by exact_mod_cast hcard
  nlinarith

/-! ### Hermitian matrices -/

lemma truncMat_isHermitian (V : ℤ → ℝ) (a : ℤ) (N : ℕ) : (truncMat V a N).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [truncMat_apply, truncMat_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]
    by_cases h2 : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · rw [if_pos h2.symm, if_pos h2, star_one]
    · rw [if_neg (fun h3 => h2 h3.symm), if_neg h2, star_zero]

section Hermitian

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}

lemma trace_pow_eq_sum_eigenvalues (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ k := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, diagonal_pow, trace_diagonal]
  first
  | rfl
  | simp [Pi.pow_apply]

lemma det_sub_eq_prod_eigenvalues (hA : A.IsHermitian) (z : ℂ) :
    (z • (1 : Matrix (Fin N) (Fin N) ℂ) - A).det = ∏ i, (z - (hA.eigenvalues i : ℂ)) := by
  rw [smul_one_eq_diagonal, ← Matrix.scalar_apply, ← Matrix.eval_charpoly, hA.charpoly_eq,
    Polynomial.eval_prod]
  simp

end Hermitian

/-! ### Eigenvalues of the truncations -/

lemma abs_eigenvalues_truncMat_le {V : ℤ → ℝ} {M : ℝ} (hM : ∀ n, |V n| ≤ M) {N : ℕ}
    (i : Fin N) : |(truncMat_isHermitian V 0 N).eigenvalues i| ≤ 2 + M := by
  set hA := truncMat_isHermitian V 0 N
  have hAv := hA.mulVec_eigenvectorBasis i
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j => ‖(hA.eigenvectorBasis i) j‖)
  have hvj : 0 < ‖(hA.eigenvectorBasis i) j‖ := by
    by_contra h0
    push_neg at h0
    have hall : ∀ j', ‖(hA.eigenvectorBasis i) j'‖ = 0 := fun j' =>
      le_antisymm ((hj j').trans h0) (norm_nonneg _)
    have h1 : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
    rw [EuclideanSpace.norm_eq] at h1
    simp [hall] at h1
  have key : ‖(truncMat V 0 N *ᵥ ⇑(hA.eigenvectorBasis i)) j‖ ≤
      (2 + M) * ‖(hA.eigenvectorBasis i) j‖ := by
    rw [← iext_coe_succ, iext_truncMat_mulVec, if_pos (by have := j.isLt; omega)]
    exact norm_hz_le hM (norm_iext_le (norm_nonneg _) hj) _
  rw [hAv, Pi.smul_apply, norm_smul, Real.norm_eq_abs] at key
  exact le_of_mul_le_mul_right key hvj

/-- The normalized eigenvalue counting measure `N⁻¹ ∑ᵢ δ_{λᵢ}` of a Hermitian matrix. -/
def eigMeasure {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) : Measure ℝ :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (hA.eigenvalues i)

section EigMeasure

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)

lemma eigMeasure_univ_le : eigMeasure hA univ ≤ 1 := by
  unfold eigMeasure
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

instance : IsFiniteMeasure (eigMeasure hA) :=
  ⟨lt_of_le_of_lt (eigMeasure_univ_le hA) ENNReal.one_lt_top⟩

lemma integral_eigMeasure (g : ℝ → ℝ) :
    ∫ x, g x ∂(eigMeasure hA) = (N : ℝ)⁻¹ * ∑ i, g (hA.eigenvalues i) := by
  rw [eigMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac enorm_lt_top)]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma eigMeasure_real_univ_le : (eigMeasure hA).real univ ≤ 1 := by
  have h := eigMeasure_univ_le hA
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

lemma ae_eigMeasure {p : ℝ → Prop} (hp : ∀ i, p (hA.eigenvalues i)) :
    ∀ᵐ x ∂(eigMeasure hA), p x := by
  rw [ae_iff]
  unfold eigMeasure
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    Finset.sum_eq_zero (fun i _ => ?_), smul_zero]
  rw [Measure.dirac_apply, Set.indicator_of_notMem]
  exact fun h => h (hp i)

end EigMeasure

/-! ### The ergodic setting: Theorem 4.3.8 -/

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

/-- The eigenvalue counting measure `dk^T_{ω,N}` of the Dirichlet truncation `H_{ω,N}` of `H_ω`
to `[1, N]`. -/
def dkT (ω : Ω) (N : ℕ) : Measure ℝ := eigMeasure (truncMat_isHermitian (E.V ω) 0 N)

instance (ω : Ω) (N : ℕ) : IsFiniteMeasure (E.dkT ω N) := by
  unfold dkT; infer_instance

lemma integral_pow_spec (ω : Ω) (n : ℤ) (k : ℕ) :
    ∫ x, x ^ k ∂(E.spec ω (dlt n)) = ((hz (E.V ω))^[k] (dltF n) n).re := by
  have h := integral_eval_spectralMeasure (E.H ω) (E.isSelfAdjoint_H ω) (dlt n)
    (Polynomial.X ^ k)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, map_pow, Polynomial.aeval_X] at h
  show ∫ x, x ^ k ∂(spectralMeasure (E.H ω) (E.isSelfAdjoint_H ω) (dlt n)) = _
  rw [h, RCLike.re_to_complex, show E.H ω = schr (E.V ω) from rfl,
    inner_dlt_schr_pow (E.bddPot ω)]

lemma integral_pow_dkN (ω : Ω) (N k : ℕ) :
    ∫ x, x ^ k ∂(E.dkN ω N) = (N : ℝ)⁻¹ *
      ∑ j ∈ Finset.range N, ((hz (E.V ω))^[k] (dltF ((j : ℤ) + 1)) ((j : ℤ) + 1)).re := by
  rw [dkN, integral_smul_measure, integral_finsetSum_measure
    (fun j _ => integrable_cont_of_supp (E.ae_mem_Icc_spec ω _) (continuous_pow k))]
  simp only [E.integral_pow_spec, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma integral_pow_dkT (ω : Ω) (N k : ℕ) :
    ∫ x, x ^ k ∂(E.dkT ω N) = (N : ℝ)⁻¹ * ((truncMat (E.V ω) 0 N ^ k).trace).re := by
  rw [dkT, integral_eigMeasure, trace_pow_eq_sum_eigenvalues (truncMat_isHermitian _ 0 N),
    Complex.re_sum]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

lemma abs_moment_sub_le (ω : Ω) (N k : ℕ) :
    |∫ x, x ^ k ∂(E.dkT ω N) - ∫ x, x ^ k ∂(E.dkN ω N)| ≤
      (N : ℝ)⁻¹ * (4 * k * (2 + E.fBound) ^ k) := by
  rw [E.integral_pow_dkT, E.integral_pow_dkN, ← mul_sub, abs_mul, abs_inv, Nat.abs_cast]
  gcongr
  rw [← Complex.re_sum, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (norm_trace_pow_sub_le (E.abs_V_le ω) N k)

/-- **Theorem 4.3.8**: almost surely, the eigenvalue counting measures of the Dirichlet
truncations converge weakly to the density of states measure. -/
theorem ae_tendsto_dkT :
    ∀ᵐ ω ∂E.μ, ∀ g : ℝ → ℝ, Continuous g →
      Tendsto (fun N : ℕ => ∫ x, g x ∂(E.dkT ω N)) atTop (𝓝 (∫ x, g x ∂E.dosm)) := by
  filter_upwards [E.ae_tendsto_dkN] with ω hω g hg
  refine tendsto_integral_of_moments (ν := E.dkT ω) (R := 2 + E.fBound) (fun N => ?_) E.ae_mem_Icc_dosm
    (fun N => eigMeasure_real_univ_le _) (by simp) (fun k => ?_) hg
  · exact ae_eigMeasure _ fun i => abs_le.1 (abs_eigenvalues_truncMat_le (E.abs_V_le ω) i)
  · have h1 := hω (fun x => x ^ k) (continuous_pow k)
    have hb : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (4 * k * (2 + E.fBound) ^ k)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (4 * k * (2 + E.fBound) ^ k)
    have h2 : Tendsto (fun N : ℕ => ∫ x, x ^ k ∂(E.dkT ω N) - ∫ x, x ^ k ∂(E.dkN ω N))
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact E.abs_moment_sub_le ω N k) hb
    simpa using h2.add h1

/-- `∫ log |z - x| dk^T_{ω,N}(x) = N⁻¹ log |det(z - H_{ω,N})|` for `z ∉ ℝ`. -/
theorem integral_log_dkT (ω : Ω) (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    ∫ x, Real.log ‖z - x‖ ∂(E.dkT ω N) = (N : ℝ)⁻¹ *
      Real.log ‖(z • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat (E.V ω) 0 N).det‖ := by
  rw [dkT, integral_eigMeasure, det_sub_eq_prod_eigenvalues (truncMat_isHermitian _ 0 N),
    norm_prod, Real.log_prod]
  intro i _
  rw [norm_ne_zero_iff, sub_ne_zero]
  intro h
  apply hz
  rw [h, Complex.ofReal_im]

end ErgodicFamily

end DF
