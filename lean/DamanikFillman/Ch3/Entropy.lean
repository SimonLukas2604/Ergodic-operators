/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.7 Topological entropy (book pp. 266–278), core results

Setting: `Ω` a nonempty compact metric space and `T : Ω → Ω` continuous.

Main definitions (Definition 3.7.1, Definition 3.7.5):
* `DF.dynDist T n` — the Bowen metric `d_n(ω, ω') = max_{0 ≤ m < n} d(Tᵐω, Tᵐω')` (3.7.1);
* `DF.IsSpanning`, `DF.IsSeparated`, `DF.IsCovering` and the numbers `DF.spanNum`, `DF.sepNum`,
  `DF.covNum` (3.7.2)–(3.7.4);
* `DF.hEps T ε` — `h_ε(T) = lim (1/n) log cov(n, ε, T)` (3.7.6);
* `DF.htop T` — `h_top(T) = lim_{ε ↓ 0} h_ε(T) = sup_{ε > 0} h_ε(T) ∈ [0, ∞]` (3.7.8).

Main results:
* `DF.covNum_two_mul_le_spanNum`, `DF.spanNum_le_sepNum`, `DF.sepNum_le_covNum` —
  **Lemma 3.7.3**: `cov(n, 2ε) ≤ span(n, ε) ≤ sep(n, ε) ≤ cov(n, ε)`;
* `DF.covNum_add_le` — the submultiplicativity (3.7.7);
* `DF.tendsto_hEps` — **Lemma 3.7.4**: the limit defining `h_ε(T)` exists and is finite;
* `DF.htop_eq_zero_of_isometry` — **Proposition 3.7.8**: isometries have zero entropy.

Statement: `DF.EntropyMetricIndependenceStatement` (Proposition 3.7.7, in the form of
conjugacy invariance), **proved** in `DamanikFillman.Ch3.EntropyConj`
(`DF.entropyMetricIndependence`).

Not formalized: Proposition 3.7.10 and Corollary 3.7.11 (entropy of subshifts, the full shift
and topological Markov chains), Remark 3.7.12, Proposition 3.7.16 (Lipschitz bound), and the
measure-theoretic entropy with the variational principle (Definition 3.7.17–Theorem 3.7.23).
-/
import DamanikFillman.Ch3.Kingman

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology
open scoped ENNReal

namespace DF

variable {Ω : Type*} [MetricSpace Ω] (T : Ω → Ω)

/-! ### The Bowen metrics -/

/-- The Bowen metric `d_n(ω, ω') = max_{0 ≤ m ≤ n-1} d(Tᵐω, Tᵐω')` (3.7.1). -/
def dynDist (n : ℕ) (x y : Ω) : ℝ := ⨆ m : Fin n, dist (T^[m] x) (T^[m] y)

variable {T}

lemma dynDist_nonneg (n : ℕ) (x y : Ω) : 0 ≤ dynDist T n x y :=
  Real.iSup_nonneg fun _ => dist_nonneg

lemma dist_le_dynDist {n : ℕ} (m : Fin n) (x y : Ω) :
    dist (T^[m] x) (T^[m] y) ≤ dynDist T n x y :=
  le_ciSup (f := fun m : Fin n => dist (T^[m] x) (T^[m] y)) (Finite.bddAbove_range _) m

lemma dynDist_le {n : ℕ} {x y : Ω} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ m : Fin n, dist (T^[m] x) (T^[m] y) ≤ ε) : dynDist T n x y ≤ ε :=
  Real.iSup_le h hε

lemma dynDist_comm (n : ℕ) (x y : Ω) : dynDist T n x y = dynDist T n y x := by
  apply le_antisymm
  · exact dynDist_le (dynDist_nonneg _ _ _) fun m => (dist_comm _ _).trans_le (dist_le_dynDist m _ _)
  · exact dynDist_le (dynDist_nonneg _ _ _) fun m => (dist_comm _ _).trans_le (dist_le_dynDist m _ _)

lemma dynDist_triangle (n : ℕ) (x y z : Ω) :
    dynDist T n x z ≤ dynDist T n x y + dynDist T n y z :=
  dynDist_le (add_nonneg (dynDist_nonneg _ _ _) (dynDist_nonneg _ _ _)) fun m =>
    (dist_triangle _ (T^[m] y) _).trans (add_le_add (dist_le_dynDist m _ _) (dist_le_dynDist m _ _))

lemma dynDist_lt_iff {n : ℕ} {x y : Ω} {ε : ℝ} (hε : 0 < ε) :
    dynDist T n x y < ε ↔ ∀ m : Fin n, dist (T^[m] x) (T^[m] y) < ε := by
  constructor
  · exact fun h m => (dist_le_dynDist m x y).trans_lt h
  · intro h
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · simp only [dynDist, Real.iSup_of_isEmpty]; exact hε
    · obtain ⟨m, hm⟩ := exists_eq_ciSup_of_finite (f := fun m : Fin n => dist (T^[m] x) (T^[m] y))
      simp only [dynDist, ← hm]
      exact h m

lemma isOpen_dynBall (hT : Continuous T) (n : ℕ) (x : Ω) {ε : ℝ} (hε : 0 < ε) :
    IsOpen {y | dynDist T n x y < ε} := by
  have : {y | dynDist T n x y < ε} = ⋂ m : Fin n, {y | dist (T^[m] x) (T^[m] y) < ε} := by
    ext y; simp only [mem_setOf_eq, mem_iInter]; exact dynDist_lt_iff hε
  rw [this]
  exact isOpen_iInter_of_finite fun m =>
    isOpen_lt (continuous_const.dist ((hT.iterate m))) continuous_const

lemma dynDist_add_le {m n : ℕ} {x y : Ω} {ε : ℝ} (hε : 0 ≤ ε) (h1 : dynDist T m x y ≤ ε)
    (h2 : dynDist T n (T^[m] x) (T^[m] y) ≤ ε) : dynDist T (m + n) x y ≤ ε := by
  refine dynDist_le hε fun k => ?_
  by_cases hk : (k : ℕ) < m
  · exact (dist_le_dynDist (⟨k, hk⟩ : Fin m) x y).trans h1
  · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = m + j := ⟨k - m, by omega⟩
    have hjn : j < n := by have := k.2; omega
    rw [hj, add_comm m j, iterate_add_apply, iterate_add_apply]
    exact (dist_le_dynDist (⟨j, hjn⟩ : Fin n) _ _).trans h2

/-! ### Spanning, separated and covering sets -/

variable (T)

/-- `A` is `(n, ε)`-spanning: closed `d_n`-balls of radius `ε` around `A` cover `Ω`. -/
def IsSpanning (n : ℕ) (ε : ℝ) (A : Finset Ω) : Prop := ∀ x, ∃ y ∈ A, dynDist T n x y ≤ ε

/-- `B` is `(n, ε)`-separated: distinct points of `B` have `d_n`-distance `> ε`. -/
def IsSeparated (n : ℕ) (ε : ℝ) (B : Finset Ω) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ε < dynDist T n x y

/-- `C` is an `(n, ε)`-covering: a cover of `Ω` by sets of `d_n`-diameter `≤ ε`. -/
def IsCovering (n : ℕ) (ε : ℝ) (C : Finset (Set Ω)) : Prop :=
  (∀ x, ∃ s ∈ C, x ∈ s) ∧ ∀ s ∈ C, ∀ x ∈ s, ∀ y ∈ s, dynDist T n x y ≤ ε

/-- `span(n, ε, T)` (3.7.2). -/
def spanNum (n : ℕ) (ε : ℝ) : ℕ := sInf {k | ∃ A : Finset Ω, IsSpanning T n ε A ∧ A.card = k}

/-- `sep(n, ε, T)` (3.7.3). -/
def sepNum (n : ℕ) (ε : ℝ) : ℕ := sSup {k | ∃ B : Finset Ω, IsSeparated T n ε B ∧ B.card = k}

/-- `cov(n, ε, T)` (3.7.4). -/
def covNum (n : ℕ) (ε : ℝ) : ℕ := sInf {k | ∃ C : Finset (Set Ω), IsCovering T n ε C ∧ C.card = k}

variable {T}
variable [CompactSpace Ω]

/-- Remark 3.7.2(b): finite `(n, ε)`-spanning sets exist. -/
lemma exists_spanning (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset Ω, IsSpanning T n ε A := by
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover (fun x => {y | dynDist T n x y < ε})
    (fun x => isOpen_dynBall hT n x hε) (fun y _ => mem_iUnion.2 ⟨y, by
      simp only [mem_setOf_eq]
      have : dynDist T n y y = 0 := le_antisymm (dynDist_le le_rfl fun m => by simp)
        (dynDist_nonneg _ _ _)
      rw [this]; exact hε⟩)
  refine ⟨A, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hA (mem_univ x))
  exact ⟨y, hy, by rw [dynDist_comm]; exact le_of_lt hxy⟩

lemma isCovering_of_isSpanning {n : ℕ} {ε : ℝ} {A : Finset Ω} (hA : IsSpanning T n ε A) :
    IsCovering T n (2 * ε) (A.image fun a => {y | dynDist T n y a ≤ ε}) := by
  classical
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨y, hy, hxy⟩ := hA x
    exact ⟨_, Finset.mem_image_of_mem _ hy, hxy⟩
  · intro s hs x hx z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
    calc dynDist T n x z ≤ dynDist T n x a + dynDist T n a z := dynDist_triangle _ _ _ _
      _ ≤ ε + ε := add_le_add hx (by rw [dynDist_comm]; exact hz)
      _ = 2 * ε := by ring

lemma exists_covering (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset (Set Ω), IsCovering T n ε C := by
  classical
  obtain ⟨A, hA⟩ := exists_spanning hT n (half_pos hε)
  have := isCovering_of_isSpanning hA
  rw [mul_div_cancel₀ _ two_ne_zero] at this
  exact ⟨_, this⟩

lemma card_le_of_isSeparated_of_isCovering {n : ℕ} {ε : ℝ} {B : Finset Ω} {C : Finset (Set Ω)}
    (hB : IsSeparated T n ε B) (hC : IsCovering T n ε C) : B.card ≤ C.card := by
  classical
  choose f hfC hfx using hC.1
  refine Finset.card_le_card_of_injOn f (fun b _ => hfC b) ?_
  intro x hx y hy hxy
  by_contra hne
  have h1 := hB x hx y hy hne
  have h2 := hC.2 (f x) (hfC x) x (hfx x) y (by rw [hxy]; exact hfx y)
  linarith

lemma covNum_le {n : ℕ} {ε : ℝ} {C : Finset (Set Ω)} (hC : IsCovering T n ε C) :
    covNum T n ε ≤ C.card := by
  unfold covNum; exact Nat.sInf_le ⟨C, hC, rfl⟩

lemma spanNum_le {n : ℕ} {ε : ℝ} {A : Finset Ω} (hA : IsSpanning T n ε A) :
    spanNum T n ε ≤ A.card := by
  unfold spanNum; exact Nat.sInf_le ⟨A, hA, rfl⟩

lemma covNum_spec (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset (Set Ω), IsCovering T n ε C ∧ C.card = covNum T n ε := by
  obtain ⟨C, hC⟩ := exists_covering hT n hε
  unfold covNum
  exact Nat.sInf_mem (s := {k | ∃ C : Finset (Set Ω), IsCovering T n ε C ∧ C.card = k})
    ⟨C.card, C, hC, rfl⟩

lemma spanNum_spec (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset Ω, IsSpanning T n ε A ∧ A.card = spanNum T n ε := by
  obtain ⟨A, hA⟩ := exists_spanning hT n hε
  unfold spanNum
  exact Nat.sInf_mem (s := {k | ∃ A : Finset Ω, IsSpanning T n ε A ∧ A.card = k})
    ⟨A.card, A, hA, rfl⟩

lemma sepNum_spec (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Finset Ω, IsSeparated T n ε B ∧ B.card = sepNum T n ε := by
  obtain ⟨C, hC, -⟩ := covNum_spec hT n hε
  have hbdd : BddAbove {k | ∃ B : Finset Ω, IsSeparated T n ε B ∧ B.card = k} :=
    ⟨C.card, by rintro _ ⟨B, hB, rfl⟩; exact card_le_of_isSeparated_of_isCovering hB hC⟩
  have hne : {k | ∃ B : Finset Ω, IsSeparated T n ε B ∧ B.card = k}.Nonempty :=
    ⟨0, ∅, by simp [IsSeparated], rfl⟩
  unfold sepNum; exact Nat.sSup_mem hne hbdd

/-- **Lemma 3.7.3** (first inequality): `cov(n, 2ε, T) ≤ span(n, ε, T)`. -/
theorem covNum_two_mul_le_spanNum (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    covNum T n (2 * ε) ≤ spanNum T n ε := by
  classical
  obtain ⟨A, hA, hcard⟩ := spanNum_spec hT n hε
  rw [← hcard]
  exact (covNum_le (isCovering_of_isSpanning hA)).trans Finset.card_image_le

/-- **Lemma 3.7.3** (second inequality): `span(n, ε, T) ≤ sep(n, ε, T)`. -/
theorem spanNum_le_sepNum (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    spanNum T n ε ≤ sepNum T n ε := by
  classical
  obtain ⟨B, hB, hcard⟩ := sepNum_spec hT n hε
  rw [← hcard]
  refine spanNum_le fun x => ?_
  by_contra hx
  push Not at hx
  -- `B ∪ {x}` is a larger separated set
  have hxB : x ∉ B := fun h => by
    have := hx x h
    have h0 : dynDist T n x x = 0 := le_antisymm (dynDist_le le_rfl fun m => by simp)
      (dynDist_nonneg _ _ _)
    linarith
  have hsep : IsSeparated T n ε (insert x B) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.1 ha with ha' | ha'
    · rcases Finset.mem_insert.1 hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact hx b hb'
    · rcases Finset.mem_insert.1 hb with hb' | hb'
      · rw [hb', dynDist_comm]; exact hx a ha'
      · exact hB a ha' b hb' hab
  obtain ⟨C, hC, -⟩ := covNum_spec hT n hε
  have hbdd : BddAbove {k | ∃ B : Finset Ω, IsSeparated T n ε B ∧ B.card = k} :=
    ⟨C.card, by rintro _ ⟨B, hB, rfl⟩; exact card_le_of_isSeparated_of_isCovering hB hC⟩
  have := le_csSup hbdd (show (insert x B).card ∈
    {k | ∃ B : Finset Ω, IsSeparated T n ε B ∧ B.card = k} from ⟨_, hsep, rfl⟩)
  rw [Finset.card_insert_of_notMem hxB] at this
  unfold sepNum at hcard
  omega

/-- **Lemma 3.7.3** (third inequality): `sep(n, ε, T) ≤ cov(n, ε, T)`. -/
theorem sepNum_le_covNum (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    sepNum T n ε ≤ covNum T n ε := by
  obtain ⟨B, hB, hcard⟩ := sepNum_spec hT n hε
  obtain ⟨C, hC, hcard'⟩ := covNum_spec hT n hε
  rw [← hcard, ← hcard']
  exact card_le_of_isSeparated_of_isCovering hB hC

lemma one_le_covNum [Nonempty Ω] (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    1 ≤ covNum T n ε := by
  obtain ⟨C, hC, hcard⟩ := covNum_spec hT n hε
  rw [← hcard, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
  rintro rfl
  obtain ⟨s, hs, -⟩ := hC.1 (Classical.arbitrary Ω)
  simp at hs

/-- The submultiplicativity (3.7.7): `cov(m + n, ε) ≤ cov(m, ε) · cov(n, ε)`. -/
theorem covNum_add_le (hT : Continuous T) (m n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    covNum T (m + n) ε ≤ covNum T m ε * covNum T n ε := by
  classical
  obtain ⟨C, hC, hcC⟩ := covNum_spec hT m hε
  obtain ⟨D, hD, hcD⟩ := covNum_spec hT n hε
  set E := (C ×ˢ D).image fun p : Set Ω × Set Ω => p.1 ∩ T^[m] ⁻¹' p.2
  have hE : IsCovering T (m + n) ε E := by
    refine ⟨fun x => ?_, ?_⟩
    · obtain ⟨s, hs, hxs⟩ := hC.1 x
      obtain ⟨t, ht, hxt⟩ := hD.1 (T^[m] x)
      refine ⟨_, Finset.mem_image_of_mem (fun p : Set Ω × Set Ω => p.1 ∩ T^[m] ⁻¹' p.2)
        (Finset.mem_product.2 ⟨hs, ht⟩ : (s, t) ∈ C ×ˢ D), ?_⟩
      show x ∈ s ∩ T^[m] ⁻¹' t
      exact ⟨hxs, hxt⟩
    · intro u hu x hx y hy
      obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨hs, ht⟩ := Finset.mem_product.1 hst
      exact dynDist_add_le hε.le (hC.2 s hs x hx.1 y hy.1) (hD.2 t ht _ hx.2 _ hy.2)
  rw [← hcC, ← hcD, ← Finset.card_product]
  exact (covNum_le hE).trans Finset.card_image_le

/-! ### The entropy -/

variable (T)

/-- `h_ε(T) = inf_{n ≥ 1} (1/n) log cov(n, ε, T)`, which by Lemma 3.7.4 equals
`lim_n (1/n) log cov(n, ε, T)` (3.7.6). -/
def hEps (ε : ℝ) : ℝ := ⨅ n : ℕ, Real.log (covNum T (n + 1) ε) / (n + 1)

/-- The topological entropy `h_top(T) = lim_{ε ↓ 0} h_ε(T) = sup_{ε > 0} h_ε(T) ∈ [0, ∞]`
(Definition 3.7.5). -/
def htop : ℝ≥0∞ := ⨆ ε > (0 : ℝ), ENNReal.ofReal (hEps T ε)

variable {T}

/-- **Lemma 3.7.4**: for every `ε > 0`, `(1/n) log cov(n, ε, T)` converges (to `h_ε(T)`). -/
theorem tendsto_hEps [Nonempty Ω] (hT : Continuous T) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => Real.log (covNum T n ε) / n) atTop (𝓝 (hEps T ε)) := by
  have hpos : ∀ n, (0 : ℝ) < covNum T n ε := fun n => by
    exact_mod_cast (one_le_covNum hT n hε)
  refine fekete (a := fun n => Real.log (covNum T n ε)) (fun n m _ _ => ?_) ⟨0, ?_⟩
  · rw [← Real.log_mul (hpos n).ne' (hpos m).ne']
    apply Real.log_le_log (hpos _)
    exact_mod_cast covNum_add_le hT n m hε
  · rintro _ ⟨n, rfl⟩
    apply div_nonneg (Real.log_nonneg _) (by positivity)
    exact_mod_cast one_le_covNum hT (n + 1) hε

/-- **Proposition 3.7.8**: the topological entropy of an isometry is zero. -/
theorem htop_eq_zero_of_isometry [Nonempty Ω] (hT : Isometry T) : htop T = 0 := by
  have hc := hT.continuous
  have hit : ∀ m x y, dist (T^[m] x) (T^[m] y) = dist x y := by
    intro m
    induction m with
    | zero => intro x y; rfl
    | succ m ih => intro x y; rw [iterate_succ_apply, iterate_succ_apply, ih, hT.dist_eq]
  have hdyn : ∀ n x y, 1 ≤ n → dynDist T n x y = dist x y := by
    intro n x y hn
    apply le_antisymm
    · exact dynDist_le dist_nonneg fun m => by rw [hit]
    · have := dist_le_dynDist (T := T) (⟨0, hn⟩ : Fin n) x y
      simpa using this
  have hcov : ∀ n ε, 1 ≤ n → covNum T n ε = covNum T 1 ε := by
    intro n ε hn
    have : ∀ C, IsCovering T n ε C ↔ IsCovering T 1 ε C := fun C => by
      simp only [IsCovering, hdyn n _ _ hn, hdyn 1 _ _ le_rfl]
    simp only [covNum, this]
  simp only [htop, ENNReal.iSup_eq_zero, ENNReal.ofReal_eq_zero]
  intro ε hε
  have h1 := tendsto_hEps hc hε
  have h2 : Tendsto (fun n : ℕ => Real.log (covNum T n ε) / n) atTop (𝓝 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat (Real.log (covNum T 1 ε))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hcov n ε hn]
  exact (tendsto_nhds_unique h1 h2).le

/-! ### Statements -/

/-- **Proposition 3.7.7**: `h_top` does not depend on the choice of a metric generating the
topology; in particular it is a topological conjugacy invariant. Stated (as conjugacy
invariance), not proved. -/
def EntropyMetricIndependenceStatement : Prop :=
  ∀ (X Y : Type) [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Y] [CompactSpace Y]
    [Nonempty Y] (S : X → X) (R : Y → Y) (h : X ≃ₜ Y), Continuous S → (∀ x, h (S x) = R (h x)) →
    htop S = htop R

end DF
