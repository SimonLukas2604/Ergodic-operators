/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Theorem 9.1 (`gr`): the quantum-graph reduction  (tex l. 1824–1931)

* `dimH_le_of_locallyLipschitz_cover`: the abstract step, fully proved — if
  `S \ E ⊆ ⋃_i f_i(K_i)` with `E` countable, countably many `f_i` locally Lipschitz on
  `U_i ⊇ K_i`, and `K_i ⊆ T`, then `dim_H S ≤ dim_H T` (countable stability,
  `dimH_image_le_of_locally_lipschitzOn`, `dimH_countable`);
* `BHJData`, `BHJReduction α σΦ`: **the single external input** — the spectral reduction of
  [bhj, (5.3), (5.4), Lemma 4.1, §8 / proof of Lemma 8.3] for the quantum-graph Hamiltonian of
  [bhj, (3.7)], which is not available in Mathlib (see the docstring of `BHJData`);
* `dimH_graphene_le_half`: **Theorem 9.1** — for irrational `Φ/2π`, `BHJReduction α σΦ` implies
  `dim_H σΦ ≤ 1/2`, using the unconditional `dimH_SigmaPhi_le_half` of `GrapheneCover.lean`.

No `sorry`, no axioms.
-/
import CriticalAMOHausdorff.GrapheneCover

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace CAH
namespace Graphene

/-! ## 1. The abstract dimension-theoretic step -/

/-- **Countable stability + Lipschitz invariance.**  If, up to a countable set `E`, the set `S`
is covered by countably many images `f_i(K_i)` with `K_i ⊆ T` and `f_i` locally Lipschitz on a
set `U_i ⊇ K_i` (e.g. an open set avoiding the branch points of `f_i`), then
`dim_H S ≤ dim_H T`. -/
theorem dimH_le_of_locallyLipschitz_cover {ι : Type*} [Countable ι] {S T E : Set ℝ}
    (hE : E.Countable) (f : ι → ℝ → ℝ) (K U : ι → Set ℝ) (hKU : ∀ i, K i ⊆ U i)
    (hKT : ∀ i, K i ⊆ T) (hf : ∀ i, LocallyLipschitzOn (U i) (f i))
    (hS : S \ E ⊆ ⋃ i, f i '' K i) : dimH S ≤ dimH T := by
  have h1 : S ⊆ (S \ E) ∪ E := fun x hx => by
    by_cases h : x ∈ E
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  have h2 : ∀ i, dimH (f i '' K i) ≤ dimH T := fun i =>
    (dimH_image_le_of_locally_lipschitzOn fun x hx => (hf i).mono (hKU i) hx).trans
      (dimH_mono (hKT i))
  calc dimH S ≤ dimH ((S \ E) ∪ E) := dimH_mono h1
    _ = max (dimH (S \ E)) (dimH E) := dimH_union _ _
    _ = dimH (S \ E) := by rw [hE.dimH_zero]; simp
    _ ≤ dimH (⋃ i, f i '' K i) := dimH_mono hS
    _ = ⨆ i, dimH (f i '' K i) := dimH_iUnion _
    _ ≤ dimH T := iSup_le h2

/-- A function with a strict derivative at every point of a set is locally Lipschitz there. -/
lemma locallyLipschitzOn_of_hasStrictDerivAt {g : ℝ → ℝ} {U : Set ℝ}
    (hg : ∀ x ∈ U, ∃ g', HasStrictDerivAt g g' x) : LocallyLipschitzOn U g := by
  intro x hx
  obtain ⟨g', hg'⟩ := hg x hx
  obtain ⟨K, t, ht, hK⟩ := HasStrictFDerivAt.exists_lipschitzOnWith hg'
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- The square-root branches `λ ↦ ±√((λ - b)/a)` are locally Lipschitz away from the branch
point `λ = b`. -/
lemma locallyLipschitzOn_sqrt_branch (a b : ℝ) (σ : ℝ) :
    LocallyLipschitzOn {l : ℝ | 0 < (l - b) / a} (fun l => σ * Real.sqrt ((l - b) / a)) := by
  refine locallyLipschitzOn_of_hasStrictDerivAt fun x hx => ?_
  have h0 : HasStrictDerivAt (fun l : ℝ => l - b) 1 x := (hasStrictDerivAt_id x).sub_const b
  have h1 : HasStrictDerivAt (fun l : ℝ => (l - b) / a) (1 / a) x := h0.div_const a
  exact ⟨_, (h1.sqrt (ne_of_gt hx)).const_mul σ⟩

/-! ## 2. The external input from [bhj] -/

/-- **The spectral reduction of [bhj] (the single external input).**

The quantum-graph Hamiltonian `H^B` of the magnetic honeycomb lattice ([bhj, (3.7)], with a
real, symmetric Kato–Rellich edge potential `V ∈ L²[0,1]`, [bhj, (2.12)]) is not available in
Mathlib, so the facts about its spectrum `σ^Φ` used in the proof of Theorem 9.1
(tex l. 1925–1929: "[bhj, (5.3), Lemma 4.1, and the proof of Lemma 8.3]") are recorded as data:

* `σD`: the spectrum of the edge Dirichlet operator `H^D`, which is discrete, hence
  **countable** (`σD_countable`);
* `σQ`: the spectrum of the tight-binding operator `Q_Λ(Φ)`;
* `Δinv ℓ`, `ℓ ∈ ℕ`: the inverse branches of the Floquet discriminant `Δ` of the edge Hill
  operator on the `ℓ`-th band; each is **locally Lipschitz** on the set `W ℓ` obtained by
  removing its branch points (in [bhj]'s normalisation `W ℓ = (-1,1)`) (`Δinv_lip`);
* `E`: the exceptional branch values (band edges `Δinv ℓ (±1)`), a **countable** set
  (`E_countable`);
* **[bhj, Lemma 4.1 and §8]**: `σ^Φ ⊆ σ(H^D) ∪ E ∪ ⋃_ℓ Δ_ℓ^{-1}(σ(Q_Λ(Φ)) ∩ W_ℓ)`
  (`decomp`);
* **[bhj, (5.3)–(5.4)]**: `Q_Λ(Φ)` is chiral and `Q_Λ(Φ)²` is (up to the factor `1/9`)
  `3 + ` the Jacobi operator `(5.4)`, whose phase translate by `1/2` is `grJacobi`; thus every
  `μ ∈ σ(Q_Λ(Φ))` satisfies `a μ² + b ∈ Σ_Φ` for affine constants `a ≠ 0`, `b`
  (`a = 9`, `b = -3` for `Q_Λ = (1/3)[[0, 1 + τ₀ + τ₁], [(1 + τ₀ + τ₁)^*, 0]]`) (`sq`).

Here `Σ_Φ = SigmaPhi α` is the (formalized) spectrum of the Jacobi operator of Part A, and
`α = Φ/2π`. -/
structure BHJData (α : ℝ) (σΦ : Set ℝ) where
  /-- The Dirichlet spectrum `σ(H^D)`. -/
  σD : Set ℝ
  /-- The spectrum of the tight-binding operator `Q_Λ(Φ)`. -/
  σQ : Set ℝ
  /-- The exceptional branch values (band edges). -/
  E : Set ℝ
  /-- The inverse branches of the discriminant. -/
  Δinv : ℕ → ℝ → ℝ
  /-- The domains of the inverse branches, with the branch points removed. -/
  W : ℕ → Set ℝ
  /-- The affine constants relating `σ(Q_Λ)²` to `Σ_Φ`. -/
  a : ℝ
  /-- The affine constants relating `σ(Q_Λ)²` to `Σ_Φ`. -/
  b : ℝ
  σD_countable : σD.Countable
  E_countable : E.Countable
  Δinv_lip : ∀ ℓ, LocallyLipschitzOn (W ℓ) (Δinv ℓ)
  decomp : σΦ ⊆ σD ∪ E ∪ ⋃ ℓ, Δinv ℓ '' (σQ ∩ W ℓ)
  a_ne : a ≠ 0
  sq : ∀ μ ∈ σQ, a * μ ^ 2 + b ∈ SigmaPhi α

/-- `BHJReduction α σΦ`: the spectral reduction of [bhj] holds for the set `σΦ` (the spectrum of
the magnetic graphene quantum graph with flux `Φ = 2πα`). -/
def BHJReduction (α : ℝ) (σΦ : Set ℝ) : Prop := Nonempty (BHJData α σΦ)

/-! ## 3. Theorem 9.1 -/

/-- Layer 1 of the reduction: `dim_H σ(Q_Λ) ≤ dim_H Σ_Φ` (square-root branches, exceptional
value `0`). -/
lemma dimH_σQ_le {α : ℝ} {σΦ : Set ℝ} (D : BHJData α σΦ) : dimH D.σQ ≤ dimH (SigmaPhi α) := by
  refine dimH_le_of_locallyLipschitz_cover (ι := Bool) (countable_singleton 0)
    (fun s l => (if s then 1 else -1) * Real.sqrt ((l - D.b) / D.a))
    (fun _ => {l | l ∈ SigmaPhi α ∧ 0 < (l - D.b) / D.a})
    (fun _ => {l : ℝ | 0 < (l - D.b) / D.a}) (fun _ _ hl => hl.2) (fun _ _ hl => hl.1)
    (fun s => locallyLipschitzOn_sqrt_branch D.a D.b _) ?_
  rintro μ ⟨hμ, hμ0⟩
  have hμ0' : μ ≠ 0 := hμ0
  have hl := D.sq μ hμ
  have e : (D.a * μ ^ 2 + D.b - D.b) / D.a = μ ^ 2 := by field_simp [D.a_ne]; ring
  have hpos : 0 < (D.a * μ ^ 2 + D.b - D.b) / D.a := by rw [e]; positivity
  rcases le_or_gt 0 μ with h | h
  · refine mem_iUnion.2 ⟨true, D.a * μ ^ 2 + D.b, ⟨hl, hpos⟩, ?_⟩
    simp only [if_true, one_mul]
    rw [e, Real.sqrt_sq h]
  · refine mem_iUnion.2 ⟨false, D.a * μ ^ 2 + D.b, ⟨hl, hpos⟩, ?_⟩
    simp only [Bool.false_eq_true, if_false, neg_mul, one_mul]
    rw [e, Real.sqrt_sq_eq_abs, abs_of_neg h, neg_neg]

/-- Layer 2 of the reduction: `dim_H σ^Φ ≤ dim_H σ(Q_Λ)` (inverse-discriminant branches,
countable Dirichlet spectrum and band edges). -/
lemma dimH_σΦ_le {α : ℝ} {σΦ : Set ℝ} (D : BHJData α σΦ) : dimH σΦ ≤ dimH D.σQ := by
  refine dimH_le_of_locallyLipschitz_cover (D.σD_countable.union D.E_countable) D.Δinv
    (fun ℓ => D.σQ ∩ D.W ℓ) D.W (fun _ _ h => h.2) (fun _ _ h => h.1) D.Δinv_lip ?_
  rintro x ⟨hx, hxn⟩
  rcases D.decomp hx with h | h
  · exact absurd h hxn
  · exact h

/-- **Theorem 9.1** (`gr`, tex l. 1824–1829).  Let `α = Φ/2π` be irrational and let `σΦ` be the
spectrum of the magnetic graphene quantum graph of [bhj], for which the spectral reduction of
[bhj] holds (`BHJReduction`, the single external input).  Then `dim_H σΦ ≤ 1/2`. -/
theorem dimH_graphene_le_half {α : ℝ} (hα : Irrational α) {σΦ : Set ℝ}
    (h : BHJReduction α σΦ) : dimH σΦ ≤ 1 / 2 := by
  obtain ⟨D⟩ := h
  exact (dimH_σΦ_le D).trans ((dimH_σQ_le D).trans (dimH_SigmaPhi_le_half hα).1)

end Graphene
end CAH
