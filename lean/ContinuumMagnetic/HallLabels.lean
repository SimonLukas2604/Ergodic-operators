/-
# Paper III: gap labels, physical densities and Hall integers

Arithmetic and Středa-formula content of Theorem `thm:physical-hall` and
§`sec:physical-hall` (proof of `thm:physical-hall`, with `lem:magnetic-gap-persistence`
supplying the local continuation in the field).

* Gap-label uniqueness in `ℤ + αℤ` for irrational `α`, and the label decomposition.
* The labels `{kα} = -⌊kα⌋ + kα`; the displayed Hall formulas after `thm:physical-hall`:
  low energy `-k`, high energy `-⌊kα_B⌋`.
* The physical densities (paper `eq:low-physical-ids`, `eq:high-physical-ids`) and the
  local lines (paper (1.10), `eq:hall-local-lines`).
* The Středa formula `Ch = 2πh · dT/dB'` taken at the level of definitions, giving the Hall
  integers `-k`, `r`, `0`, `1` of paper (1.8) `eq:low-hall-label`, (1.9) `eq:high-hall-label`.
* Block labels (paper (1.11), `ex-eq:block-ids`).
* Every nonzero relative Hall integer is realized by the labels `{kα}`, `k ≠ 0`.

The analytic content (trace compatibility, the Středa–Chern theorem of CMM, linear
response) is not formalized here: the Chern number is *defined* through the Středa
derivative of the density (`stredaChern`).
-/
import ContinuumMagnetic.Basic

noncomputable section

open Real

namespace CMS

/-! ### Gap-label uniqueness -/

/-- Gap-label uniqueness: for irrational `α`, `r + kα = r' + k'α` forces `r = r'`, `k = k'`. -/
theorem label_unique {α : ℝ} (hα : Irrational α) {r k r' k' : ℤ}
    (h : (r : ℝ) + k * α = r' + k' * α) : r = r' ∧ k = k' := by
  have hk : k = k' := by
    by_contra hne
    have hsub : ((k - k' : ℤ) : ℝ) * α = ((r' - r : ℤ) : ℝ) := by push_cast; linarith
    have hirr : Irrational (((k - k' : ℤ) : ℝ) * α) :=
      hα.intCast_mul (sub_ne_zero.mpr hne)
    exact hirr.ne_int (r' - r) hsub
  subst hk
  refine ⟨?_, rfl⟩
  exact_mod_cast (by linarith : (r : ℝ) = r')

/-- `N` has the gap label `(r, k)` with respect to `α`: `N = r + kα`. -/
def HasLabel (α N : ℝ) (r k : ℤ) : Prop := N = r + k * α

/-- The label decomposition of a value in `ℤ + αℤ` is well defined for irrational `α`. -/
theorem existsUnique_label {α N : ℝ} (hα : Irrational α) (hN : ∃ r k : ℤ, HasLabel α N r k) :
    ∃! p : ℤ × ℤ, HasLabel α N p.1 p.2 := by
  obtain ⟨r, k, h⟩ := hN
  refine ⟨(r, k), h, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := label_unique hα (hp.symm.trans h)
  exact Prod.ext h1 h2

/-! ### The labels `{kα}` and the displayed Hall formulas -/

/-- `{kα} = -⌊kα⌋ + kα`. -/
theorem fract_mul_eq (k : ℤ) (α : ℝ) :
    Int.fract (k * α) = ((-⌊(k : ℝ) * α⌋ : ℤ) : ℝ) + k * α := by
  rw [Int.fract]; push_cast; ring

/-- The label `{kα}` has decomposition `r = -⌊kα⌋`, `k`. -/
theorem hasLabel_fract (k : ℤ) (α : ℝ) : HasLabel α (Int.fract (k * α)) (-⌊(k : ℝ) * α⌋) k :=
  fract_mul_eq k α

/-- Any decomposition of `{kα}` (with `α` irrational) is `(-⌊kα⌋, k)`. -/
theorem label_of_fract {α : ℝ} (hα : Irrational α) {k r' k' : ℤ}
    (h : HasLabel α (Int.fract (k * α)) r' k') : r' = -⌊(k : ℝ) * α⌋ ∧ k' = k :=
  label_unique hα (h.symm.trans (hasLabel_fract k α))

/-- Low-energy relative Hall integer of the gap with label `r + kα` (paper (1.8)). -/
def lowHall (_r k : ℤ) : ℤ := -k

/-- High-energy relative Hall integer of the gap with label `r + kα_B` (paper (1.9)). -/
def highHall (r _k : ℤ) : ℤ := r

/-- Low-energy displayed formula: `N_h(E) = {kα} ⟹ Ch = -k` (for every decomposition). -/
theorem lowHall_of_fract {α : ℝ} (hα : Irrational α) {k r' k' : ℤ}
    (h : HasLabel α (Int.fract (k * α)) r' k') : lowHall r' k' = -k := by
  simp [lowHall, (label_of_fract hα h).2]

/-- High-energy displayed formula: `N_n(E) = {kα_B} ⟹ Ch = -⌊kα_B⌋`. -/
theorem highHall_of_fract {αB : ℝ} (hα : Irrational αB) {k r' k' : ℤ}
    (h : HasLabel αB (Int.fract (k * αB)) r' k') : highHall r' k' = -⌊(k : ℝ) * αB⌋ :=
  (label_of_fract hα h).1

/-- With `α = -γ`, `r + kα = r - kγ`. -/
theorem label_freq (r k : ℤ) (γ : ℝ) : (r : ℝ) + k * freq γ = r - k * γ := by
  unfold freq; ring

/-! ### Physical densities and local lines -/

/-- Low-energy physical density `T = N/μ` (paper `eq:low-physical-ids`). -/
def lowDensity (μ N : ℝ) : ℝ := N / μ

/-- High-energy physical density `T = (B/(2πh)) N` (paper `eq:high-physical-ids`). -/
def highDensity (B h N : ℝ) : ℝ := B / (2 * π * h) * N

/-- Low-energy local line `r/μ - k𝓑'/(2πh)` (paper (1.10)). -/
def lowLine (μ h : ℝ) (r k : ℤ) (B' : ℝ) : ℝ := r / μ - k * B' / (2 * π * h)

/-- High-energy local line `rB'/(2πh) + k` (paper (1.10)). -/
def highLine (h : ℝ) (r k : ℤ) (B' : ℝ) : ℝ := r * B' / (2 * π * h) + k

/-- The inverse of the field path: `γ' = μ𝓑'/(2πh)`. -/
def fieldParam (μ h B' : ℝ) : ℝ := μ * B' / (2 * π * h)

lemma fieldPath_fieldParam {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (B' : ℝ) :
    fieldPath μ (fieldParam μ h B') h = B' := by
  unfold fieldPath fieldParam; field_simp

lemma fieldParam_fieldPath {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (γ : ℝ) :
    fieldParam μ h (fieldPath μ γ h) = γ := by
  unfold fieldPath fieldParam; field_simp

/-- Along the field `𝓑'` (`γ' = μ𝓑'/(2πh)`, `α' = -γ'`), the low-energy density of the label
`r + kα'` is the local line `r/μ - k𝓑'/(2πh)`. -/
theorem lowDensity_eq_lowLine {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (r k : ℤ) (B' : ℝ) :
    lowDensity μ (r + k * freq (fieldParam μ h B')) = lowLine μ h r k B' := by
  unfold lowDensity freq fieldParam lowLine
  have : (π : ℝ) ≠ 0 := pi_ne_zero
  field_simp; ring

/-- High-energy density of the label `r + kα_B`, `α_B = 2πh/B`, is `rB/(2πh) + k`. -/
theorem highDensity_eq_highLine {B h : ℝ} (hB : B ≠ 0) (hh : h ≠ 0) (r k : ℤ) :
    highDensity B h (r + k * (2 * π * h / B)) = highLine h r k B := by
  unfold highDensity highLine
  have : (π : ℝ) ≠ 0 := pi_ne_zero
  field_simp

/-! ### The Středa formula -/

/-- Středa–Chern number of a density `T'` (as a function of the field) at the field `B`:
`Ch = 2πh · dT'/dB'` (proof of `thm:physical-hall`). -/
def stredaChern (h : ℝ) (T' : ℝ → ℝ) (B : ℝ) : ℝ := 2 * π * h * deriv T' B

lemma hasDerivAt_lowLine (μ h : ℝ) (r k : ℤ) (B : ℝ) :
    HasDerivAt (lowLine μ h r k) (-(k / (2 * π * h))) B := by
  have := ((hasDerivAt_id B).const_mul (k : ℝ)).div_const (2 * π * h)
  have h2 := (hasDerivAt_const B ((r : ℝ) / μ)).sub this
  convert h2 using 1
  · funext x; simp [lowLine]
  · simp

lemma hasDerivAt_highLine (h : ℝ) (r k : ℤ) (B : ℝ) :
    HasDerivAt (highLine h r k) (r / (2 * π * h)) B := by
  have := (((hasDerivAt_id B).const_mul (r : ℝ)).div_const (2 * π * h)).add_const (k : ℝ)
  convert this using 1
  · funext x; simp [highLine]
  · simp

/-- Low-energy Středa check: the local line has Chern number `-k` (paper (1.8)). -/
theorem stredaChern_lowLine {μ h : ℝ} (hh : h ≠ 0) (r k : ℤ) (B : ℝ) :
    stredaChern h (lowLine μ h r k) B = ((lowHall r k : ℤ) : ℝ) := by
  unfold stredaChern lowHall
  rw [(hasDerivAt_lowLine μ h r k B).deriv]
  have : (π : ℝ) ≠ 0 := pi_ne_zero
  push_cast; field_simp

/-- High-energy Středa check: the local line has Chern number `r` (paper (1.9)). -/
theorem stredaChern_highLine {h : ℝ} (hh : h ≠ 0) (r k : ℤ) (B : ℝ) :
    stredaChern h (highLine h r k) B = ((highHall r k : ℤ) : ℝ) := by
  unfold stredaChern highHall
  rw [(hasDerivAt_highLine h r k B).deriv]
  have : (π : ℝ) ≠ 0 := pi_ne_zero
  field_simp

/-- The full scalar projection `P_h` has density `1/μ`, constant in the field: Chern `0`. -/
theorem stredaChern_fullLow (μ h B : ℝ) : stredaChern h (fun _ => 1 / μ) B = 0 := by
  simp [stredaChern]

/-- The full Landau cluster `Π_n` has density `B'/(2πh)`: Chern `1`. -/
theorem stredaChern_fullHigh {h : ℝ} (hh : h ≠ 0) (B : ℝ) :
    stredaChern h (fun B' => B' / (2 * π * h)) B = 1 := by
  unfold stredaChern
  rw [((hasDerivAt_id' B).div_const (2 * π * h)).deriv]
  have : (π : ℝ) ≠ 0 := pi_ne_zero
  field_simp

/-- `P_h` is the low-energy line with label `(1, 0)` and `Π_n` the high-energy line with
label `(1, 0)`, consistent with Hall integers `0` and `1`. -/
theorem fullProjections_as_lines (μ h : ℝ) :
    lowLine μ h 1 0 = (fun _ => 1 / μ) ∧ highLine h 1 0 = (fun B' => B' / (2 * π * h)) := by
  constructor <;> funext x <;> simp [lowLine, highLine]

/-! ### Block labels (paper (1.11)) -/

/-- The normalized block label `(r + kα)/d` of an unnormalized trace `r + kα`. -/
def blockLabel (d : ℕ) (α : ℝ) (r k : ℤ) : ℝ := (r + k * α) / d

/-- Normalized block labels lie in `(1/d)(ℤ + αℤ)`. -/
theorem blockLabel_mem (d : ℕ) (α : ℝ) (r k : ℤ) :
    ∃ r' k' : ℤ, blockLabel d α r k = (1 / (d : ℝ)) * (r' + k' * α) :=
  ⟨r, k, by unfold blockLabel; ring⟩

/-- Block physical density `(d/μ) N^block = (r + kα)/μ`. -/
theorem block_density {d : ℕ} (hd : d ≠ 0) (μ α : ℝ) (r k : ℤ) :
    (d : ℝ) / μ * blockLabel d α r k = lowDensity μ (r + k * α) := by
  unfold blockLabel lowDensity
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  by_cases hμ : μ = 0
  · simp [hμ]
  · field_simp

/-- Block Hall integer: the block density along the field is the low-energy local line, whose
Středa–Chern number is `-k`. -/
theorem block_hall {d : ℕ} (hd : d ≠ 0) {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (r k : ℤ) (B : ℝ) :
    stredaChern h (fun B' => (d : ℝ) / μ * blockLabel d (freq (fieldParam μ h B')) r k) B
      = -k := by
  have : (fun B' => (d : ℝ) / μ * blockLabel d (freq (fieldParam μ h B')) r k)
      = lowLine μ h r k := by
    funext B'; rw [block_density hd, lowDensity_eq_lowLine hμ hh]
  rw [this, stredaChern_lowLine hh]; simp [lowHall]

/-! ### Every nonzero relative Hall integer is realized -/

/-- Each nonzero integer `m` is the relative Hall integer `-k` of a label with `k ≠ 0`. -/
theorem exists_label_hall (m : ℤ) (hm : m ≠ 0) : ∃ k : ℤ, k ≠ 0 ∧ -k = m :=
  ⟨-m, neg_ne_zero.mpr hm, neg_neg m⟩

/-- For irrational `α` and `k ≠ 0`, the label `{kα}` lies in `(0,1)`. -/
theorem fract_mem_Ioo {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    Int.fract ((k : ℝ) * α) ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨lt_of_le_of_ne (Int.fract_nonneg _) ?_, Int.fract_lt_one _⟩
  intro h0
  have h1 : ((0 : ℤ) : ℝ) + k * α = ((⌊(k : ℝ) * α⌋ : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * α := by
    have := Int.fract_add_floor ((k : ℝ) * α)
    rw [← h0] at this; push_cast; linarith
  exact hk (label_unique hα h1).2

/-- For irrational `α`, the labels `{kα}` are pairwise distinct. -/
theorem fract_injective {α : ℝ} (hα : Irrational α) :
    Function.Injective (fun k : ℤ => Int.fract ((k : ℝ) * α)) := by
  intro k k' h
  have h' : HasLabel α (Int.fract ((k : ℝ) * α)) (-⌊(k' : ℝ) * α⌋) k' := by
    simp only at h; rw [h]; exact hasLabel_fract k' α
  exact ((label_of_fract hα h').2).symm

/-- Each critical square island realizes every nonzero relative Hall integer: for `m ≠ 0`, the
gap label `{(-m)α} ∈ (0,1)` has low-energy Hall integer `m` for every decomposition. -/
theorem realizes_every_hall {α : ℝ} (hα : Irrational α) (m : ℤ) (hm : m ≠ 0) :
    ∃ k : ℤ, k ≠ 0 ∧ Int.fract ((k : ℝ) * α) ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ r' k' : ℤ, HasLabel α (Int.fract ((k : ℝ) * α)) r' k' → lowHall r' k' = m := by
  obtain ⟨k, hk, hkm⟩ := exists_label_hall m hm
  exact ⟨k, hk, fract_mem_Ioo hα hk, fun r' k' h => (lowHall_of_fract hα h).trans hkm⟩

end CMS
