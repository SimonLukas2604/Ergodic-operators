/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Finite-dimensional algebra of rational frequencies
(paper §2.3 "Rational band geometry", ll. 1115–1300, and §5.1 "An exact twisted
representation and its trace", ll. 5911–5980)

* `clock`, `shift`: the rational clock–shift matrices of l. 5922, with
  `A B = e^{2πip/q} B A`, `A^q = B^q = I` (`clock_mul_shift`, `clock_pow_q`, `shift_pow_q`);
* `trace_zpow_weyl_eq_zero`: the trace filter behind eq. `(dim:rat:trace-filter)` (l. 1182):
  for a Weyl pair `U V = e^{2πip/q} V U` of invertible `q × q` matrices,
  `tr (V^s U^r) = 0` unless `q ∣ r` and `q ∣ s`;
* `trace_clock_zpow_mul_shift_zpow`, `trace_clock_pow_mul_shift_pow`: the clock–shift trace
  filter `tr (A^m B^n) = q·[q ∣ m ∧ q ∣ n]`;
* `twistU_twistV`: the rotation relation of the twisted representation (ll. 5927–5933);
* `det_cycMat`, `det_cycMat_transfer`: Chambers' cycle formula `(dim:rat:cycle)` (l. 1206)
  with explicit `z`-independent part, and its transfer-matrix form (l. 1236);
* `norm_le_of_chambers`: the spectral-containment step at the end of the proof of
  Proposition `dim:prop:chambers` (l. 1293).
-/
import Mathlib

noncomputable section

open Matrix Complex

namespace SGD

namespace RationalBloch

/-! ## The rational phase -/

/-- The rational phase `ω = e^{2πi p/q}` (paper l. 5922). -/
def phase (p : ℤ) (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((p : ℂ) / q))

lemma phase_ne_zero (p : ℤ) (q : ℕ) : phase p q ≠ 0 := Complex.exp_ne_zero _

/-- For reduced `p/q`, `ω = e^{2πip/q}` is a primitive `q`-th root of unity:
`ω^m = 1 ↔ q ∣ m` (used in the trace filter, l. 1182). -/
lemma phase_zpow_eq_one_iff {p : ℤ} {q : ℕ} (hq : 0 < q) (hpq : Int.gcd p q = 1) (m : ℤ) :
    phase p q ^ m = 1 ↔ (q : ℤ) ∣ m := by
  have hζ := Complex.isPrimitiveRoot_exp q hq.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have h : phase p q = Complex.exp (2 * Real.pi * Complex.I / q) ^ p := by
    rw [← Complex.exp_int_mul]; unfold phase; congr 1; field_simp
  rw [h, ← _root_.zpow_mul, hζ.zpow_eq_one_iff_dvd]
  constructor
  · intro hd
    exact Int.dvd_of_dvd_mul_right_of_gcd_one hd (by rw [Int.gcd_comm]; exact_mod_cast hpq)
  · intro hd; exact hd.mul_left _

lemma phase_pow_q {p : ℤ} {q : ℕ} : phase p q ^ q = 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold phase
  rw [← Complex.exp_nat_mul]
  have : (q : ℂ) * (2 * Real.pi * Complex.I * ((p : ℂ) / q)) = p * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma phase_pow_mod {p : ℤ} {q : ℕ} (n : ℕ) : phase p q ^ (n % q) = phase p q ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, phase_pow_q, one_pow, one_mul]

/-! ## Clock and shift matrices -/

/-- **Clock matrix** (paper l. 5922): `A = diag(ω^j)_{j ∈ Fin q}`, `ω = e^{2πip/q}`. -/
def clock (p : ℤ) (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.diagonal fun j => phase p q ^ (j : ℕ)

/-- **Shift matrix** (paper l. 5922): `(B v)_i = v_{i-1 mod q}`, i.e. `B_{ij} = 1` iff
`i ≡ j + 1 (mod q)`.  With this orientation the paper's relation `AB = e^{2πip/q} BA`
holds exactly (the opposite shift `(Bv)_i = v_{i+1}` would give `BA = e^{2πip/q}AB`). -/
def shift (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.of fun i j => if ((j : ℕ) + 1) % q = i then 1 else 0

/-- **Clock–shift relation** (paper l. 5922): `A B = e^{2πip/q} B A`. -/
theorem clock_mul_shift (p : ℤ) (q : ℕ) :
    clock p q * shift q = phase p q • (shift q * clock p q) := by
  ext i j
  simp only [clock, shift, diagonal_mul, mul_diagonal, Matrix.smul_apply, of_apply, smul_eq_mul]
  split_ifs with h
  · rw [← h, phase_pow_mod, pow_succ]; ring
  · simp

/-- **`A^q = I`** (paper l. 5922). -/
theorem clock_pow_q (p : ℤ) (q : ℕ) : clock p q ^ q = 1 := by
  rw [clock, diagonal_pow, ← diagonal_one]
  congr 1; funext j
  simp only [Pi.pow_apply]
  rw [← pow_mul, mul_comm, pow_mul, phase_pow_q, one_pow]

lemma shift_pow (q : ℕ) (n : ℕ) :
    shift q ^ n = Matrix.of fun i j : Fin q => if ((j : ℕ) + n) % q = i then (1 : ℂ) else 0 := by
  induction n with
  | zero =>
    ext i j
    simp only [pow_zero, one_apply, of_apply, add_zero, Nat.mod_eq_of_lt j.isLt, Fin.ext_iff,
      eq_comm]
  | succ n ih =>
    ext i j
    have hq : 0 < q := Fin.pos i
    rw [pow_succ', mul_apply, ih]
    rw [Finset.sum_eq_single (⟨((j : ℕ) + n) % q, Nat.mod_lt _ hq⟩ : Fin q)]
    · simp only [shift, of_apply, if_true, mul_one, Nat.mod_add_mod, add_assoc]
    · intro k _ hk
      simp only [of_apply]
      rw [if_neg, mul_zero]
      intro h; exact hk (Fin.ext h.symm)
    · simp

/-- **`B^q = I`** (paper l. 5922). -/
theorem shift_pow_q (q : ℕ) : shift q ^ q = 1 := by
  rw [shift_pow]
  ext i j
  simp only [of_apply, one_apply, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt, Fin.ext_iff,
    eq_comm]

/-! ## Trace filter for Weyl pairs -/

lemma trace_units_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : (Matrix n n ℂ)ˣ) (X : Matrix n n ℂ) :
    trace ((U : Matrix n n ℂ) * X * (↑U⁻¹ : Matrix n n ℂ)) = trace X := by
  rw [trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

/-- **Trace filter for a Weyl pair** (paper eq. `(dim:rat:trace-filter)`, l. 1182, and the
display `tr W_{r,s} = 0` for `(r,s) ∉ qℤ²` below it).  Let `ω = e^{2πip/q}` with
`gcd(p,q) = 1`, and let `U, V` be invertible `q × q` complex matrices with `U V = ω V U`.
Then `tr (V^s U^r) = 0` unless `q ∣ r` and `q ∣ s`.  Proof: conjugation by `U` (resp. `V`)
multiplies `V^s U^r` by `ω^s` (resp. `ω^r`), and the trace is conjugation invariant. -/
theorem trace_zpow_weyl_eq_zero {q : ℕ} (hq : 0 < q) {p : ℤ} (hpq : Int.gcd p q = 1)
    (U V : (Matrix (Fin q) (Fin q) ℂ)ˣ)
    (hUV : (U : Matrix (Fin q) (Fin q) ℂ) * V = phase p q • ((V : Matrix (Fin q) (Fin q) ℂ) * U))
    (r s : ℤ) (hrs : ¬ ((q : ℤ) ∣ r ∧ (q : ℤ) ∣ s)) :
    trace ((V ^ s * U ^ r : (Matrix (Fin q) (Fin q) ℂ)ˣ) : Matrix (Fin q) (Fin q) ℂ) = 0 := by
  set ω := phase p q with hωdef
  have hω : ω ≠ 0 := phase_ne_zero p q
  let c : (Matrix (Fin q) (Fin q) ℂ)ˣ :=
    Units.map (algebraMap ℂ (Matrix (Fin q) (Fin q) ℂ)).toMonoidHom (Units.mk0 ω hω)
  have hc : ∀ n : ℤ, ((c ^ n : (Matrix (Fin q) (Fin q) ℂ)ˣ) : Matrix (Fin q) (Fin q) ℂ)
      = ω ^ n • (1 : Matrix (Fin q) (Fin q) ℂ) := by
    intro n
    simp only [c, ← map_zpow, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, Algebra.algebraMap_eq_smul_one, RingHom.toMonoidHom_eq_coe]
  have hc1 : (c : Matrix (Fin q) (Fin q) ℂ) = ω • 1 := by simpa using hc 1
  have hcomm : ∀ x : (Matrix (Fin q) (Fin q) ℂ)ˣ, Commute c x := by
    intro x; apply Units.ext
    show (c : Matrix (Fin q) (Fin q) ℂ) * x = x * c
    rw [hc1, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hUV' : U * V = c * V * U := by
    apply Units.ext
    simp only [Units.val_mul, hUV, hc1, Matrix.smul_mul, one_mul, mul_assoc]
  -- conjugation by `U`
  have hconjU : U * V * U⁻¹ = c * V := by rw [hUV', mul_inv_cancel_right]
  have hconjUs : U * V ^ s * U⁻¹ = c ^ s * V ^ s := by
    have := map_zpow (MulAut.conj U) V s
    simp only [MulAut.conj_apply, hconjU] at this
    rw [this, (hcomm V).mul_zpow]
  -- conjugation by `V⁻¹`
  have hconjV : V⁻¹ * U * V = c * U := by
    calc V⁻¹ * U * V = V⁻¹ * (U * V) := mul_assoc _ _ _
      _ = (V⁻¹ * c) * V * U := by rw [hUV']; simp only [mul_assoc]
      _ = c * U := by rw [← (hcomm V⁻¹).eq, mul_assoc c V⁻¹ V, inv_mul_cancel, mul_one]
  have hconjVr : V⁻¹ * U ^ r * V = c ^ r * U ^ r := by
    have := map_zpow (MulAut.conj V⁻¹) U r
    simp only [MulAut.conj_apply, inv_inv, hconjV] at this
    rw [this, (hcomm U).mul_zpow]
  set t := trace ((V ^ s * U ^ r : (Matrix (Fin q) (Fin q) ℂ)ˣ) : Matrix (Fin q) (Fin q) ℂ)
  have hts : ω ^ s * t = t := by
    have h1 : U * (V ^ s * U ^ r) * U⁻¹ = c ^ s * (V ^ s * U ^ r) := by
      rw [← mul_assoc (c ^ s), ← hconjUs]; group
    have h2 := congrArg (fun x : (Matrix (Fin q) (Fin q) ℂ)ˣ => Matrix.trace x.1) h1
    simp only [Units.val_mul] at h2
    rw [trace_units_conj, hc, Matrix.smul_mul, one_mul, trace_smul, smul_eq_mul] at h2
    simpa [t] using h2.symm
  have htr : ω ^ r * t = t := by
    have h1 : V⁻¹ * (V ^ s * U ^ r) * V = c ^ r * (V ^ s * U ^ r) := by
      have e : V⁻¹ * (V ^ s * U ^ r) * V = V ^ s * (V⁻¹ * U ^ r * V) := by group
      rw [e, hconjVr, ← mul_assoc, ← ((hcomm (V ^ s)).zpow_left r).eq, mul_assoc]
    have h2 := congrArg (fun x : (Matrix (Fin q) (Fin q) ℂ)ˣ => Matrix.trace x.1) h1
    simp only [Units.val_mul] at h2
    have h3 := trace_units_conj V⁻¹ ((V ^ s * U ^ r : (Matrix (Fin q) (Fin q) ℂ)ˣ) :
      Matrix (Fin q) (Fin q) ℂ)
    simp only [inv_inv, Units.val_mul] at h3
    rw [h3, hc, Matrix.smul_mul, one_mul, trace_smul, smul_eq_mul] at h2
    simpa [t] using h2.symm
  by_contra ht
  apply hrs
  constructor
  · rw [← phase_zpow_eq_one_iff hq hpq]
    exact mul_left_eq_self₀.mp htr |>.resolve_right ht
  · rw [← phase_zpow_eq_one_iff hq hpq]
    exact mul_left_eq_self₀.mp hts |>.resolve_right ht

/-! ## The clock–shift trace filter -/

/-- The clock matrix as a unit (`A^q = I`). -/
def clockUnit (p : ℤ) (q : ℕ) (hq : 0 < q) : (Matrix (Fin q) (Fin q) ℂ)ˣ :=
  Units.ofPowEqOne _ q (clock_pow_q p q) hq.ne'

/-- The shift matrix as a unit (`B^q = I`). -/
def shiftUnit (q : ℕ) (hq : 0 < q) : (Matrix (Fin q) (Fin q) ℂ)ˣ :=
  Units.ofPowEqOne _ q (shift_pow_q q) hq.ne'

lemma unit_zpow_eq_one_of_dvd {q : ℕ} {u : (Matrix (Fin q) (Fin q) ℂ)ˣ}
    (hu : (u : Matrix (Fin q) (Fin q) ℂ) ^ q = 1) {m : ℤ} (hm : (q : ℤ) ∣ m) : u ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have : u ^ q = 1 := Units.ext (by simpa using hu)
  rw [_root_.zpow_mul, zpow_natCast, this, _root_.one_zpow]

/-- **Clock–shift trace filter** (paper l. 1182, `tr W_{r,s} = 0` unless `(r,s) ∈ qℤ²`, for
the rational clock–shift matrices of l. 5922), integer exponents:
for reduced `p/q`, `tr (A^m B^n) = q` if `q ∣ m` and `q ∣ n`, and `0` otherwise. -/
theorem trace_clock_zpow_mul_shift_zpow {q : ℕ} (hq : 0 < q) {p : ℤ} (hpq : Int.gcd p q = 1)
    (m n : ℤ) :
    trace ((clockUnit p q hq ^ m * shiftUnit q hq ^ n : (Matrix (Fin q) (Fin q) ℂ)ˣ) :
        Matrix (Fin q) (Fin q) ℂ) = if (q : ℤ) ∣ m ∧ (q : ℤ) ∣ n then (q : ℂ) else 0 := by
  split_ifs with h
  · rw [unit_zpow_eq_one_of_dvd (clock_pow_q p q) h.1,
      unit_zpow_eq_one_of_dvd (shift_pow_q q) h.2]
    simp
  · rw [Units.val_mul, trace_mul_comm, ← Units.val_mul]
    refine trace_zpow_weyl_eq_zero hq hpq _ _ (clock_mul_shift p q) m n ?_
    exact h

/-- **Clock–shift trace filter**, natural exponents (paper l. 1182 / l. 5922):
for reduced `p/q`, `tr (A^m B^n) = q` if `q ∣ m` and `q ∣ n`, and `0` otherwise. -/
theorem trace_clock_pow_mul_shift_pow {q : ℕ} (hq : 0 < q) {p : ℤ} (hpq : Int.gcd p q = 1)
    (m n : ℕ) :
    trace (clock p q ^ m * shift q ^ n) = if q ∣ m ∧ q ∣ n then (q : ℂ) else 0 := by
  have := trace_clock_zpow_mul_shift_zpow hq hpq (m : ℤ) (n : ℤ)
  simp only [zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, Int.natCast_dvd_natCast]
    at this
  exact this

/-! ## The twisted representation (§5.1) -/

/-- The twisted clock `Ũ = A e^{ix}` acting on `f : ℝ → ℂ^q` (paper l. 5927). -/
def twistU {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (f : ℝ → Fin q → ℂ) : ℝ → Fin q → ℂ :=
  fun x => Complex.exp (x * Complex.I) • (A *ᵥ f x)

/-- The twisted shift `Ṽ = B e^{-ishD_x}`, i.e. `(Ṽ f)(x) = B f(x - 2πδ)` with `sh = 2πδ`
(paper l. 5928, `h = 2π|δ|`, `s = sgn δ`). -/
def twistV {q : ℕ} (B : Matrix (Fin q) (Fin q) ℂ) (δ : ℝ) (f : ℝ → Fin q → ℂ) :
    ℝ → Fin q → ℂ :=
  fun x => B *ᵥ f (x - 2 * Real.pi * δ)

/-- Rotation relation of the twisted representation for any pair `AB = ωBA`:
`Ũ Ṽ = ω e^{2πiδ} Ṽ Ũ`. -/
theorem twistU_twistV_of {q : ℕ} {A B : Matrix (Fin q) (Fin q) ℂ} {ω : ℂ}
    (hAB : A * B = ω • (B * A)) (δ : ℝ) (f : ℝ → Fin q → ℂ) :
    twistU A (twistV B δ f) =
      (ω * Complex.exp (2 * Real.pi * Complex.I * δ)) • twistV B δ (twistU A f) := by
  funext x
  simp only [twistU, twistV, Pi.smul_apply, mulVec_mulVec, mulVec_smul, hAB,
    Matrix.smul_mulVec, smul_smul]
  have key : Complex.exp (2 * Real.pi * Complex.I * δ) *
      Complex.exp (((x - 2 * Real.pi * δ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  congr 1
  rw [← key]; ring

/-- **Exact rotation relation of the twisted representation** (paper ll. 5922–5933):
with `Ũ f(x) = e^{ix} A f(x)` and `Ṽ f(x) = B f(x - 2πδ)`, where `A, B` are the clock and
shift matrices (`AB = e^{2πip/q}BA`), one has `Ũ Ṽ = e^{2πi(p/q+δ)} Ṽ Ũ`, i.e. the rotation
relation has exactly frequency `a = p/q + δ`. -/
theorem twistU_twistV (p : ℤ) (q : ℕ) (δ : ℝ) (f : ℝ → Fin q → ℂ) :
    twistU (clock p q) (twistV (shift q) δ f) =
      Complex.exp (2 * Real.pi * Complex.I * ((p : ℂ) / q + δ)) •
        twistV (shift q) δ (twistU (clock p q) f) := by
  rw [twistU_twistV_of (clock_mul_shift p q), phase, ← Complex.exp_add]
  congr 2; ring

/-! ## Spectral containment -/

/-- **Spectral containment step** (end of the proof of Proposition `dim:prop:chambers`,
l. 1293): if `Δ/(s t) = z + z⁻¹ + w + w⁻¹ - D + R` with `|z| = |w| = 1`, `|R| ≤ ε` and
`Δ = 0`, then `|D| ≤ 4 + ε`. -/
theorem norm_le_of_chambers {Δ s t z w D Rm : ℂ} {ε : ℝ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hR : ‖Rm‖ ≤ ε) (_hst : s * t ≠ 0)
    (h : Δ / (s * t) = z + z⁻¹ + w + w⁻¹ - D + Rm) (hΔ : Δ = 0) : ‖D‖ ≤ 4 + ε := by
  rw [hΔ, zero_div] at h
  have hD : D = z + z⁻¹ + w + w⁻¹ + Rm := by linear_combination h
  rw [hD]
  have h1 := norm_add_le (z + z⁻¹ + w + w⁻¹) Rm
  have h2 := norm_add_le (z + z⁻¹ + w) w⁻¹
  have h3 := norm_add_le (z + z⁻¹) w
  have h4 := norm_add_le z z⁻¹
  rw [norm_inv, hz] at h4
  rw [norm_inv, hw] at h2
  rw [hw] at h3
  norm_num at h4
  linarith

/-! ## Chambers' cycle formula -/

lemma val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  rcases lt_or_ge (i : ℕ) p with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), if_pos h]; rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h), if_neg (by omega)]
    simp

lemma val_succAbove_zero {n : ℕ} (i : Fin n) :
    (((0 : Fin (n + 1)).succAbove i : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := by
  rw [val_succAbove]; simp

lemma val_succAbove_last {n : ℕ} (i : Fin n) :
    (((Fin.last n).succAbove i : Fin (n + 1)) : ℕ) = (i : ℕ) := by
  rw [val_succAbove]; simp

/-- The open-chain (Jacobi) block of the cyclic matrix of `(dim:rat:cycle)`: the `k × k`
tridiagonal matrix with diagonal `d_{s+i}`, superdiagonal `c_{s+i}` (entry `(i,i+1)`) and
subdiagonal `c^♯_{s+i}` (entry `(i+1,i)`). -/
def tri (d c cs : ℕ → ℂ) (s k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then d (s + i) else if (j : ℕ) = i + 1 then c (s + i)
    else if (i : ℕ) = j + 1 then cs (s + j) else 0

/-- Three-term recurrence for the open-chain determinants:
`D_{k+2} = d_{k+1} D_{k+1} - c_k c^♯_k D_k`. -/
lemma det_tri_succ_succ (d c cs : ℕ → ℂ) (s k : ℕ) :
    (tri d c cs s (k + 2)).det = d (s + (k + 1)) * (tri d c cs s (k + 1)).det
      - c (s + k) * cs (s + k) * (tri d c cs s k).det := by
  have h0 : ∀ j : Fin k, tri d c cs s (k + 2) (Fin.last (k + 1)) j.castSucc.castSucc = 0 := by
    intro j; have := j.isLt
    simp only [tri, of_apply, Fin.val_castSucc, Fin.val_last]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have t1 : tri d c cs s (k + 2) (Fin.last (k + 1)) (Fin.last (k + 1)) = d (s + (k + 1)) := by
    simp [tri]
  have t2 : tri d c cs s (k + 2) (Fin.last (k + 1)) (Fin.last k).castSucc = cs (s + k) := by
    simp only [tri, of_apply, Fin.val_last, Fin.val_castSucc]
    split_ifs <;> first | omega | contradiction | rfl
  have e1 : (tri d c cs s (k + 2)).submatrix (Fin.last (k + 1)).succAbove
      (Fin.last (k + 1)).succAbove = tri d c cs s (k + 1) := by
    ext i j; simp [tri]
  have e2 : ((tri d c cs s (k + 2)).submatrix (Fin.last (k + 1)).succAbove
      (Fin.last k).castSucc.succAbove).det = c (s + k) * (tri d c cs s k).det := by
    rw [det_succ_column _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
    · have hN : ((tri d c cs s (k + 2)).submatrix (Fin.last (k + 1)).succAbove
          (Fin.last k).castSucc.succAbove) (Fin.last k) (Fin.last k) = c (s + k) := by
        simp [tri]
      have hM : ((tri d c cs s (k + 2)).submatrix (Fin.last (k + 1)).succAbove
          (Fin.last k).castSucc.succAbove).submatrix (Fin.last k).succAbove
          (Fin.last k).succAbove = tri d c cs s k := by
        ext i j
        have hj := j.isLt
        simp [tri]
      rw [hN, hM, ← two_mul, pow_mul]; simp
    · intro i _ hi
      have hi' : (i : ℕ) < k :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) (fun h => hi (Fin.ext h))
      have : ((tri d c cs s (k + 2)).submatrix (Fin.last (k + 1)).succAbove
          (Fin.last k).castSucc.succAbove) i (Fin.last k) = 0 := by
        simp only [submatrix_apply, Fin.succAbove_last, tri, of_apply, Fin.val_castSucc,
          val_succAbove, Fin.val_last]
        have hlk : ((Fin.last k : Fin (k + 1)) : ℕ) = k := Fin.val_last k
        split_ifs <;> first | omega | contradiction | rfl
      rw [this, mul_zero, zero_mul]
    · simp
  rw [det_succ_row _ (Fin.last (k + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, t1, t2, e1, e2,
    Fin.val_last, Fin.val_castSucc]
  have hs1 : (-1 : ℂ) ^ (k + 1 + k) = -1 := by
    rw [show k + 1 + k = 2 * k + 1 by ring, pow_succ, pow_mul]; norm_num
  have hs2 : (-1 : ℂ) ^ (k + 1 + (k + 1)) = 1 := by
    rw [show k + 1 + (k + 1) = 2 * (k + 1) by ring, pow_mul]; norm_num
  rw [hs1, hs2]; ring

/-- **Cyclic Jacobi (Bloch) matrix** of `(dim:rat:cycle)` (paper l. 1206): the `q × q` matrix
with `M_{nn} = d_n`, `M_{n,n+1} = c_n`, `M_{n+1,n} = c^♯_n` (`n < q-1`), and the two corner
entries `M_{q-1,0} = z c_{q-1}`, `M_{0,q-1} = z⁻¹ c^♯_{q-1}` carrying the central character `z`.
(Only the values `d_n, c_n, c^♯_n` with `n < q` enter.) -/
def cycMat (q : ℕ) (d c cs : ℕ → ℂ) (z : ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.of fun i j =>
    if (i : ℕ) = q - 1 ∧ (j : ℕ) = 0 then z * c (q - 1)
    else if (i : ℕ) = 0 ∧ (j : ℕ) = q - 1 then z⁻¹ * cs (q - 1)
    else tri d c cs 0 q i j

/-- **Chambers' cycle formula** (paper eq. `(dim:rat:cycle)`, l. 1206): for `q ≥ 3` and
`z ≠ 0`,
`det M(z) = A⁰ + s_q (z ∏ c_n + z⁻¹ ∏ c^♯_n)`, `s_q = (-1)^{q-1}`,
where the `z`-independent part is explicitly
`A⁰ = det(open chain 0..q-1) - c_{q-1} c^♯_{q-1} det(open chain 1..q-2)`.
The two directed full cycles are the only terms with nonzero winding in `z`. -/
theorem det_cycMat {q : ℕ} (hq : 3 ≤ q) (d c cs : ℕ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    (cycMat q d c cs z).det =
      ((tri d c cs 0 q).det - c (q - 1) * cs (q - 1) * (tri d c cs 1 (q - 2)).det)
      + (-1) ^ (q - 1) *
          (z * ∏ n ∈ Finset.range q, c n + z⁻¹ * ∏ n ∈ Finset.range q, cs n) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 + 1 := ⟨q - 3, by omega⟩
  have h1 : m + 2 + 1 - 1 = m + 2 := by omega
  have h2 : m + 2 + 1 - 2 = m + 1 := by omega
  rw [h1, h2]
  obtain ⟨M0, hM0⟩ : ∃ M0, M0 = tri d c cs 0 (m + 2 + 1) := ⟨_, rfl⟩
  let x : Fin (m + 2 + 1) → ℂ := fun j => if (j : ℕ) = 0 then c (m + 2) else 0
  let y : Fin (m + 2 + 1) → ℂ := fun j => if (j : ℕ) = m + 2 then cs (m + 2) else 0
  have hl0 : Fin.last (m + 2) ≠ 0 := by simp [Fin.ext_iff]
  have hrepr : cycMat (m + 2 + 1) d c cs z =
      (M0.updateRow (Fin.last (m + 2)) (M0 (Fin.last (m + 2)) + z • x)).updateRow 0
        (M0 0 + z⁻¹ • y) := by
    ext i j
    have hi := i.isLt; have hj := j.isLt
    simp only [cycMat, updateRow_apply, of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.ext_iff, Fin.val_last, Fin.val_zero, x, y, hM0, tri, h1, zero_add]
    split_ifs <;> first | omega | contradiction | ring1 | (ring_nf; congr 1 <;> omega)
  have hL : M0.updateRow (Fin.last (m + 2)) (M0 (Fin.last (m + 2))) = M0 :=
    updateRow_eq_self _ _
  have hO : M0.updateRow 0 (M0 0) = M0 := updateRow_eq_self _ _
  have hc2 : (M0.updateRow 0 y).updateRow (Fin.last (m + 2)) (M0 (Fin.last (m + 2))) =
      M0.updateRow 0 y := by
    rw [updateRow_comm _ hl0.symm, hL]
  have hkey : (cycMat (m + 2 + 1) d c cs z).det =
      M0.det + z * (M0.updateRow (Fin.last (m + 2)) x).det
      + z⁻¹ * (M0.updateRow 0 y).det
      + z⁻¹ * z * ((M0.updateRow 0 y).updateRow (Fin.last (m + 2)) x).det := by
    rw [hrepr, det_updateRow_add, det_updateRow_smul, updateRow_comm _ hl0,
      updateRow_comm _ hl0, hO, det_updateRow_add, det_updateRow_smul, hL,
      det_updateRow_add, det_updateRow_smul, hc2]
    ring
  -- the upper winding term
  have L1 : (M0.updateRow (Fin.last (m + 2)) x).det =
      (-1) ^ (m + 2) * ∏ n ∈ Finset.range (m + 2 + 1), c n := by
    rw [det_succ_row _ (Fin.last (m + 2)), Finset.sum_eq_single 0]
    · have hT : ((M0.updateRow (Fin.last (m + 2)) x).submatrix (Fin.last (m + 2)).succAbove
          (0 : Fin (m + 2 + 1)).succAbove).det = ∏ n ∈ Finset.range (m + 2), c n := by
        rw [det_of_isLowerTriangular]
        · rw [← Fin.prod_univ_eq_prod_range]
          refine Finset.prod_congr rfl fun i _ => ?_
          have hi := i.isLt
          simp only [submatrix_apply, updateRow_apply, hM0, tri, of_apply, x]
          simp only [Fin.ext_iff, val_succAbove_zero, val_succAbove_last, Fin.val_last,
            Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
          split_ifs <;> first | omega | contradiction | rfl | (congr 1 <;> omega)
        · intro i j hij
          have hij' : (i : ℕ) < j := OrderDual.toDual_lt_toDual.mp hij
          have hi := i.isLt; have hj := j.isLt
          simp only [submatrix_apply, updateRow_apply, hM0, tri, of_apply, x]
          simp only [Fin.ext_iff, val_succAbove_zero, val_succAbove_last, Fin.val_last,
            Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
          split_ifs <;> first | omega | contradiction | rfl
      rw [hT]
      simp only [updateRow_self, x]
      rw [if_pos (by simp), Finset.prod_range_succ _ (m + 2)]
      simp only [Fin.val_last, Fin.val_zero, add_zero]
      ring
    · intro j _ hj
      have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
      simp only [updateRow_self, x]
      rw [if_neg this]; simp
    · simp
  -- the lower winding term
  have L2 : (M0.updateRow 0 y).det =
      (-1) ^ (m + 2) * ∏ n ∈ Finset.range (m + 2 + 1), cs n := by
    rw [det_succ_row _ 0, Finset.sum_eq_single (Fin.last (m + 2))]
    · have hT : ((M0.updateRow 0 y).submatrix (0 : Fin (m + 2 + 1)).succAbove
          (Fin.last (m + 2)).succAbove).det = ∏ n ∈ Finset.range (m + 2), cs n := by
        rw [det_of_isUpperTriangular]
        · rw [← Fin.prod_univ_eq_prod_range]
          refine Finset.prod_congr rfl fun i _ => ?_
          have hi := i.isLt
          simp only [submatrix_apply, updateRow_apply, hM0, tri, of_apply, y]
          simp only [Fin.ext_iff, val_succAbove_zero, val_succAbove_last, Fin.val_last,
            Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
          split_ifs <;> first | omega | contradiction | rfl | (congr 1 <;> omega)
        · intro i j hij
          have hij' : (j : ℕ) < i := hij
          have hi := i.isLt; have hj := j.isLt
          simp only [submatrix_apply, updateRow_apply, hM0, tri, of_apply, y]
          simp only [Fin.ext_iff, val_succAbove_zero, val_succAbove_last, Fin.val_last,
            Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
          split_ifs <;> first | omega | contradiction | rfl
      rw [hT]
      simp only [updateRow_self, y]
      rw [if_pos (by simp), Finset.prod_range_succ _ (m + 2)]
      simp only [Fin.val_last, Fin.val_zero, zero_add]
      ring
    · intro j _ hj
      have : (j : ℕ) ≠ m + 2 := fun h => hj (Fin.ext h)
      simp only [updateRow_self, y]
      rw [if_neg this]; simp
    · simp
  -- the cross term (both corners): `-c_{q-1} c^♯_{q-1} det(open chain 1..q-2)`
  have L3 : ((M0.updateRow 0 y).updateRow (Fin.last (m + 2)) x).det =
      -(c (m + 2) * cs (m + 2) * (tri d c cs 1 (m + 1)).det) := by
    rw [det_succ_row _ (Fin.last (m + 2)), Finset.sum_eq_single 0]
    · have hN : (((M0.updateRow 0 y).updateRow (Fin.last (m + 2)) x).submatrix
          (Fin.last (m + 2)).succAbove (0 : Fin (m + 2 + 1)).succAbove).det =
          (-1) ^ (m + 1) * cs (m + 2) * (tri d c cs 1 (m + 1)).det := by
        rw [det_succ_row _ 0, Finset.sum_eq_single (Fin.last (m + 1))]
        · have e0 : (((M0.updateRow 0 y).updateRow (Fin.last (m + 2)) x).submatrix
              (Fin.last (m + 2)).succAbove (0 : Fin (m + 2 + 1)).succAbove) 0
              (Fin.last (m + 1)) = cs (m + 2) := by
            simp only [submatrix_apply, updateRow_apply, hM0, tri, of_apply, x, y]
            simp only [Fin.ext_iff, val_succAbove_zero, val_succAbove_last, Fin.val_last,
              Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
            split_ifs <;> first | omega | contradiction | rfl
          have eM : (((M0.updateRow 0 y).updateRow (Fin.last (m + 2)) x).submatrix
              (Fin.last (m + 2)).succAbove (0 : Fin (m + 2 + 1)).succAbove).submatrix
              (0 : Fin (m + 1 + 1)).succAbove (Fin.last (m + 1)).succAbove =
              tri d c cs 1 (m + 1) := by
            ext i j
            have hi := i.isLt; have hj := j.isLt
            simp only [submatrix_apply, updateRow_apply, hM0, tri, of_apply, x, y]
            simp only [Fin.ext_iff, val_succAbove_zero, val_succAbove_last, Fin.val_last,
              Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
            split_ifs <;> first | omega | contradiction | rfl | (congr 1 <;> omega)
          rw [e0, eM]; simp
        · intro j _ hj
          have : (j : ℕ) ≠ m + 1 := fun h => hj (Fin.ext h)
          have hj' := j.isLt
          simp only [submatrix_apply, updateRow_apply, hM0, tri, of_apply, x, y]
          simp only [Fin.ext_iff, val_succAbove_zero, val_succAbove_last, Fin.val_last,
            Fin.val_zero, Fin.val_succ, Fin.val_castSucc]
          split_ifs <;> first | omega | contradiction | simp
        · simp
      rw [hN]
      simp only [updateRow_self, x]
      rw [if_pos (by simp)]
      simp only [Fin.val_last, Fin.val_zero, add_zero]
      have hodd : (-1 : ℂ) ^ (m + 2) * (-1) ^ (m + 1) = -1 := by
        rw [← pow_add]; exact Odd.neg_one_pow ⟨m + 1, by ring⟩
      linear_combination (c (m + 2) * cs (m + 2) * (tri d c cs 1 (m + 1)).det) * hodd
    · intro j _ hj
      have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
      simp only [updateRow_self, x]
      rw [if_neg this]; simp
    · simp
  rw [hkey, L1, L2, L3, inv_mul_cancel₀ hz, hM0]
  ring

/-- Transfer matrix `T_n = !![-d_n/c_n, -c^♯_{n-1}/c_n; 1, 0]` of the cyclic Jacobi matrix
(indices mod `q`, so `c^♯_{-1} = c^♯_{q-1}`); paper l. 1236. -/
def transferMat (q : ℕ) (d c cs : ℕ → ℂ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-d n / c n, -(if n = 0 then cs (q - 1) else cs (n - 1)) / c n; 1, 0]

/-- Ordered transfer products `T_{k-1} ⋯ T_0`; the period transfer matrix is
`transferProd q d c cs q = T_{q-1} ⋯ T_0`. -/
def transferProd (q : ℕ) (d c cs : ℕ → ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | k + 1 => transferMat q d c cs k * transferProd q d c cs k

/-- Shifted open-chain determinants `G_k = det(open chain 1..k-1)`, `G_0 = 0`. -/
def triG (d c cs : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => (tri d c cs 1 k).det

lemma triG_succ_succ (d c cs : ℕ → ℂ) (j : ℕ) :
    triG d c cs (j + 2) = d (j + 1) * triG d c cs (j + 1) - c j * cs j * triG d c cs j := by
  cases j with
  | zero => simp [triG, tri, det_unique]
  | succ j =>
    simp only [triG]
    rw [det_tri_succ_succ, show 1 + (j + 1) = j + 1 + 1 by ring, show 1 + j = j + 1 by ring]

lemma det_tri_zero_succ_succ (d c cs : ℕ → ℂ) (j : ℕ) :
    (tri d c cs 0 (j + 2)).det = d (j + 1) * (tri d c cs 0 (j + 1)).det
      - c j * cs j * (tri d c cs 0 j).det := by
  rw [det_tri_succ_succ]; simp only [zero_add]

/-- Entries of the transfer products in terms of open-chain determinants:
`T_j ⋯ T_0 = ((-1)^{j+1}/∏_{i ≤ j} c_i) · [[D_{j+1}, c^♯_{q-1} G_{j+1}],
[-c_j D_j, -c_j c^♯_{q-1} G_j]]`. -/
lemma transferProd_succ_eq (q : ℕ) (d c cs : ℕ → ℂ) (j : ℕ) (hc : ∀ i ≤ j, c i ≠ 0) :
    transferProd q d c cs (j + 1) =
      ((-1) ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), c i) •
        !![(tri d c cs 0 (j + 1)).det, cs (q - 1) * triG d c cs (j + 1);
          -(c j * (tri d c cs 0 j).det), -(c j * cs (q - 1) * triG d c cs j)] := by
  induction j with
  | zero =>
    have h0 := hc 0 le_rfl
    ext a b
    fin_cases a <;> fin_cases b <;> simp [transferProd, transferMat, triG, tri, det_unique] <;>
      field_simp
  | succ j ih =>
    have ih' := ih (fun i hi => hc i (by omega))
    have hcj : c (j + 1) ≠ 0 := hc _ le_rfl
    have hP : ∏ i ∈ Finset.range (j + 1), c i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i hi => hc i (by simp at hi; omega))
    show transferMat q d c cs (j + 1) * transferProd q d c cs (j + 1) = _
    rw [ih', det_tri_zero_succ_succ, triG_succ_succ]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [transferMat, Matrix.mul_apply, Fin.sum_univ_two, Finset.prod_range_succ] <;>
      field_simp <;> ring

lemma det_transferProd (q : ℕ) (d c cs : ℕ → ℂ) (k : ℕ) :
    (transferProd q d c cs k).det =
      ∏ n ∈ Finset.range k, (if n = 0 then cs (q - 1) else cs (n - 1)) / c n := by
  induction k with
  | zero => simp [transferProd]
  | succ k ih =>
    rw [transferProd, det_mul, ih, Finset.prod_range_succ, transferMat, det_fin_two_of]
    ring

/-- **Transfer-matrix form of Chambers' formula** (paper l. 1236):
for `q ≥ 3`, all `c_n ≠ 0` and `z ≠ 0`, with `T = T_{q-1} ⋯ T_0`,
`det M(z) = s_q (∏ c_n) (z + z⁻¹ det T - tr T)`, `s_q = (-1)^{q-1}`;
moreover `det T = ∏ c^♯_n / ∏ c_n` (`det_transferProd_period`). -/
theorem det_cycMat_transfer {q : ℕ} (hq : 3 ≤ q) (d c cs : ℕ → ℂ)
    (hc : ∀ n < q, c n ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    (cycMat q d c cs z).det =
      (-1) ^ (q - 1) * (∏ n ∈ Finset.range q, c n) *
        (z + z⁻¹ * (transferProd q d c cs q).det - trace (transferProd q d c cs q)) := by
  rw [det_cycMat hq d c cs hz]
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 + 1 := ⟨q - 3, by omega⟩
  have h1 : m + 2 + 1 - 1 = m + 2 := by omega
  have h2 : m + 2 + 1 - 2 = m + 1 := by omega
  rw [h2]
  have hP := transferProd_succ_eq (m + 2 + 1) d c cs (m + 2) (fun i hi => hc i (by omega))
  have hPc : ∏ n ∈ Finset.range (m + 2 + 1), c n ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => hc i (by simpa using hi))
  have hcs : ∏ n ∈ Finset.range (m + 2 + 1), (if n = 0 then cs (m + 2 + 1 - 1) else cs (n - 1))
      = ∏ n ∈ Finset.range (m + 2 + 1), cs n := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ (fun n => cs n)]
    simp [h1]
  rw [det_transferProd, Finset.prod_div_distrib, hcs, hP, trace_smul, trace_fin_two_of]
  simp only [h1, triG, smul_eq_mul]
  generalize hs : (-1 : ℂ) ^ (m + 2) = s
  have hss : s * s = 1 := by rw [← hs, ← pow_add, ← two_mul, pow_mul]; norm_num
  rw [pow_succ, hs]
  generalize ∏ n ∈ Finset.range (m + 2 + 1), c n = P at hPc ⊢
  have : s * P * (z + z⁻¹ * ((∏ n ∈ Finset.range (m + 2 + 1), cs n) / P) -
      s * -1 / P * ((tri d c cs 0 (m + 2 + 1)).det +
        -(c (m + 2) * cs (m + 2) * (tri d c cs 1 (m + 1)).det))) =
      s * (z * P + z⁻¹ * ∏ n ∈ Finset.range (m + 2 + 1), cs n) +
        (s * s) * ((tri d c cs 0 (m + 2 + 1)).det
          - c (m + 2) * cs (m + 2) * (tri d c cs 1 (m + 1)).det) := by
    field_simp; ring
  rw [this, hss]; ring

/-- `det T = ∏ c^♯_n / ∏ c_n` for the period transfer matrix (paper l. 1238,
`det T_{a,E,q} = C^♯_q / C_q`). -/
theorem det_transferProd_period {q : ℕ} (hq : 1 ≤ q) (d c cs : ℕ → ℂ) :
    (transferProd q d c cs q).det =
      (∏ n ∈ Finset.range q, cs n) / ∏ n ∈ Finset.range q, c n := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  rw [det_transferProd, Finset.prod_div_distrib, Finset.prod_range_succ',
    Finset.prod_range_succ (fun n => cs n)]
  simp

end RationalBloch

end SGD
