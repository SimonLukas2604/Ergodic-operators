/-
# Kernels of prepared Jacobi operators are at most two-dimensional

For the prepared Jacobi operator of Paper I,
`(J_x u)_n = a(x+nα) u_{n+1} + conj(a(x+(n-1)α)) u_{n-1} + b(x+nα) u_n`,
with nowhere-vanishing hopping `a` along the orbit, a solution of `J_x u = 0` is determined by
`(u_0, u_1)`: the forward recursion divides by `a(x+nα)`, the backward one by
`conj(a(x+(n-1)α))`.  Hence `u ↦ (u_0, u_1)` is injective on `ker J_x`, which is therefore
finite-dimensional of dimension `≤ 2`.

For an exact preparation `H_x - E = Q_x^* J_x Q_x` (`AMO.JacobiPrep`) we get
`ker(H_x - E) = Q_x⁻¹ (ker J_x)`, so `ker(H_x - E)` is finite-dimensional of dimension `≤ 2`
for every real phase `x`.  Boundedness of the weights (`JacobiBdd`) follows from continuity and
`1`-periodicity of `a`, `b` on the real axis.
-/
import AnalyticPerturbationsAMO

noncomputable section

open scoped ComplexConjugate
open AMO L2

namespace CMS

/-- The evaluation `u ↦ (u 0, u 1)` on the kernel of an operator on `ℓ²(ℤ)`. -/
def kerEval01 (T : Op ℤ) : LinearMap.ker (T : L2 ℤ →ₗ[ℂ] L2 ℤ) →ₗ[ℂ] ℂ × ℂ where
  toFun u := ((u : L2 ℤ) 0, (u : L2 ℤ) 1)
  map_add' u v := by simp
  map_smul' c u := by simp

/-- A solution of `J_x u = 0` vanishing at `0` and `1` vanishes identically, provided the
hopping does not vanish along the orbit. -/
theorem jacobi_ker_eq_zero_of_eval {α : ℝ} {a b : ℂ → ℂ} {x : ℝ} (hJ : JacobiBdd α a b x)
    (ha : ∀ n : ℤ, a (x + n * α : ℝ) ≠ 0) {u : L2 ℤ} (hu : jacobi α a b x u = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 0) : u = 0 := by
  have eq : ∀ n : ℤ, a (x + n * α : ℝ) * u (n + 1) + conj (a (x + (n - 1) * α : ℝ)) * u (n - 1)
      + b (x + n * α : ℝ) * u n = 0 := by
    intro n
    rw [← jacobi_apply hJ u n, hu]; rfl
  have fwd : ∀ k : ℕ, u k = 0 ∧ u (k + 1) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have e := eq ((k : ℤ) + 1)
      rw [show (k : ℤ) + 1 - 1 = k by ring, ih.1, ih.2] at e
      simp only [mul_zero, add_zero] at e
      have := (mul_eq_zero.mp e).resolve_left (ha _)
      push_cast
      exact this
  have bwd : ∀ k : ℕ, u (-(k : ℤ)) = 0 ∧ u (-(k : ℤ) + 1) = 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨?_, by rw [show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by push_cast; ring]; exact ih.1⟩
      have e := eq (-(k : ℤ))
      rw [ih.1, ih.2] at e
      simp only [mul_zero, zero_add, add_zero] at e
      have hc := ha (-(k : ℤ) - 1)
      rw [Int.cast_sub, Int.cast_one] at hc
      have := (mul_eq_zero.mp e).resolve_left ((map_ne_zero _).mpr hc)
      rw [show -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 by push_cast; ring]
      exact this
  ext n
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using (fwd k).1
  · simpa using (bwd k).1

/-- `u ↦ (u 0, u 1)` is injective on `ker J_x` when the hopping does not vanish on the orbit. -/
theorem kerEval01_injective {α : ℝ} {a b : ℂ → ℂ} {x : ℝ} (hJ : JacobiBdd α a b x)
    (ha : ∀ n : ℤ, a (x + n * α : ℝ) ≠ 0) :
    Function.Injective (kerEval01 (jacobi α a b x)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h := Prod.ext_iff.mp hu
  ext1
  exact jacobi_ker_eq_zero_of_eval hJ ha u.2 h.1 h.2

/-- The kernel of a Jacobi operator with nonvanishing hopping is finite-dimensional. -/
theorem finiteDimensional_ker_jacobi {α : ℝ} {a b : ℂ → ℂ} {x : ℝ} (hJ : JacobiBdd α a b x)
    (ha : ∀ n : ℤ, a (x + n * α : ℝ) ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (jacobi α a b x : L2 ℤ →ₗ[ℂ] L2 ℤ)) :=
  Module.Finite.of_injective _ (kerEval01_injective hJ ha)

/-- **`dim ker J_x ≤ 2`** for a Jacobi operator with nonvanishing hopping. -/
theorem finrank_ker_jacobi_le_two {α : ℝ} {a b : ℂ → ℂ} {x : ℝ} (hJ : JacobiBdd α a b x)
    (ha : ∀ n : ℤ, a (x + n * α : ℝ) ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (jacobi α a b x : L2 ℤ →ₗ[ℂ] L2 ℤ)) ≤ 2 := by
  have := LinearMap.finrank_le_finrank_of_injective (kerEval01_injective hJ ha)
  simpa using this

/-- A continuous `1`-periodic function, restricted to the real axis, is bounded along any
orbit `x + nα`. -/
theorem bdd_orbit_of_continuous_periodic {f : ℂ → ℂ} (hf : Continuous fun t : ℝ => f t)
    (hp : ∀ z, f (z + 1) = f z) (α x : ℝ) : Bdd (fun n : ℤ => f (x + n * α : ℝ)) := by
  have hper : Function.Periodic (fun t : ℝ => f t) 1 := fun t => by
    simp only [Complex.ofReal_add, Complex.ofReal_one]; exact hp _
  obtain ⟨M, hM⟩ := (hper.compact_of_continuous one_ne_zero hf).isBounded.exists_norm_le
  exact ⟨M, fun n => hM _ ⟨_, rfl⟩⟩

namespace JacobiPrep

variable {α : ℝ} {Hx : ℝ → Op ℤ} {E : ℝ}

/-- The weights of a prepared Jacobi operator are bounded along every orbit. -/
theorem jacobiBdd (P : AMO.JacobiPrep α Hx E) (x : ℝ) : JacobiBdd α P.a P.b x := by
  have hreal : ∀ t : ℝ, (t : ℂ) ∈ strip P.w := fun t => by simp [strip, P.w_pos]
  have cont : ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f (strip P.w) → Continuous fun t : ℝ => f t :=
    fun f hf => continuous_iff_continuousAt.mpr fun t =>
      ((hf _ (hreal t)).continuousAt).comp Complex.continuous_ofReal.continuousAt
  exact ⟨bdd_orbit_of_continuous_periodic (cont _ P.a_analytic) P.a_periodic α x,
    bdd_orbit_of_continuous_periodic (cont _ P.b_analytic) P.b_periodic α x⟩

lemma units_inv_apply_apply (Q : (Op ℤ)ˣ) (w : L2 ℤ) : (↑Q⁻¹ : Op ℤ) ((Q : Op ℤ) w) = w := by
  change ((↑Q⁻¹ * ↑Q : Op ℤ)) w = w
  rw [Units.inv_mul]; rfl

lemma units_apply_inv_apply (Q : (Op ℤ)ˣ) (w : L2 ℤ) : (Q : Op ℤ) ((↑Q⁻¹ : Op ℤ) w) = w := by
  change ((↑Q * ↑Q⁻¹ : Op ℤ)) w = w
  rw [Units.mul_inv]; rfl

/-- `ker(H_x - E) = Q_x⁻¹ (ker J_x)` for an exact preparation `H_x - E = Q_x^* J_x Q_x`. -/
theorem ker_eq_map (P : AMO.JacobiPrep α Hx E) (x : ℝ) :
    LinearMap.ker (Hx x - algebraMap ℂ (Op ℤ) E : L2 ℤ →ₗ[ℂ] L2 ℤ) =
      Submodule.map ((↑(P.Q x)⁻¹ : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)
        (LinearMap.ker (jacobi α P.a P.b x : L2 ℤ →ₗ[ℂ] L2 ℤ)) := by
  ext u
  rw [LinearMap.mem_ker]
  change (Hx x - algebraMap ℂ (Op ℤ) E) u = 0 ↔ _
  rw [AMO.JacobiPrep.ker_iff P x u, Submodule.mem_map]
  constructor
  · intro h
    exact ⟨_, LinearMap.mem_ker.mpr h, units_inv_apply_apply _ _⟩
  · rintro ⟨v, hv, rfl⟩
    rw [ContinuousLinearMap.coe_coe, units_apply_inv_apply]
    exact LinearMap.mem_ker.mp hv

/-- The map `u ↦ Q_x u` from `ker(H_x - E)` to `ker J_x`. -/
def kerToJacobi (P : AMO.JacobiPrep α Hx E) (x : ℝ) :
    LinearMap.ker (Hx x - algebraMap ℂ (Op ℤ) E : L2 ℤ →ₗ[ℂ] L2 ℤ) →ₗ[ℂ] LinearMap.ker (jacobi α P.a P.b x : L2 ℤ →ₗ[ℂ] L2 ℤ) :=
  ((P.Q x : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ).restrict fun u hu =>
    (AMO.JacobiPrep.ker_iff P x u).mp hu

/-- `u ↦ Q_x u` is injective on `ker(H_x - E)`. -/
theorem kerToJacobi_injective (P : AMO.JacobiPrep α Hx E) (x : ℝ) :
    Function.Injective (kerToJacobi P x) := by
  intro u v h
  have h' : (P.Q x : Op ℤ) u = (P.Q x : Op ℤ) v := congrArg Subtype.val h
  have key : ∀ w : L2 ℤ, (↑(P.Q x)⁻¹ : Op ℤ) ((P.Q x : Op ℤ) w) = w :=
    units_inv_apply_apply _
  ext1
  rw [← key u, ← key v, h']

/-- **`ker(H_x - E)` is finite-dimensional** for every real phase `x`. -/
theorem finiteDimensional_ker (P : AMO.JacobiPrep α Hx E) (x : ℝ) :
    FiniteDimensional ℂ (LinearMap.ker (Hx x - algebraMap ℂ (Op ℤ) E : L2 ℤ →ₗ[ℂ] L2 ℤ)) := by
  have := finiteDimensional_ker_jacobi (jacobiBdd P x)
    (fun n => P.a_ne (x + n * α))
  exact Module.Finite.of_injective _ (kerToJacobi_injective P x)

/-- **`dim ker(H_x - E) ≤ 2`** for every real phase `x`. -/
theorem finrank_ker_le_two (P : AMO.JacobiPrep α Hx E) (x : ℝ) :
    Module.finrank ℂ (LinearMap.ker (Hx x - algebraMap ℂ (Op ℤ) E : L2 ℤ →ₗ[ℂ] L2 ℤ)) ≤ 2 := by
  have := finiteDimensional_ker_jacobi (jacobiBdd P x)
    (fun n => P.a_ne (x + n * α))
  exact (LinearMap.finrank_le_finrank_of_injective (kerToJacobi_injective P x)).trans
    (finrank_ker_jacobi_le_two (jacobiBdd P x) (fun n => P.a_ne (x + n * α)))

end JacobiPrep

end CMS
