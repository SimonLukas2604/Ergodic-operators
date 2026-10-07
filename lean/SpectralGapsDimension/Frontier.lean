/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# The current input frontier

This file holds the **smallest current set of unproved inputs** (`PaperIIRemainingInputs`) and the
main theorems of the paper proved from it (`thm_joint_main`, `thm_liouville_main`,
`thm_finite_exponent_main`).  It is updated whenever an input is reduced or discharged; the
intermediate bundles (`PaperIIInputs`, `PaperIIInputsRefined`, `PaperIIInputsFinal`) record earlier
stages of the reduction and remain valid.

Reductions used here (all proved):
* `ComparisonClaim` ⇐ `ComparisonNonnegClaim` (`comparison_of_nonneg`, sign symmetry `H_{-b} ≅ -H_b`);
* `JacobiPrepClaim` ⇐ `JacobiPrepSmallWidthClaim` (`jacobiPrep_of_smallWidth`: for `S ≥ 7/2` the
  preparation is Paper I's `AMO.exists_jacobiPrep`).
-/
import SpectralGapsDimension.LargeWidth
import SpectralGapsDimension.ComparisonSign

noncomputable section

open MeasureTheory

namespace SGD

open AMO

/-- The remaining unproved inputs of Paper II (see the README for what each needs). -/
structure PaperIIRemainingInputs : Prop where
  comparisonNonneg : ComparisonNonnegClaim
  normalization : NormalizationClaim
  inertiaTransfer : InertiaTransferClaim
  gapLabelling : GapLabellingClaim
  infiniteExponent : InfiniteExponentClaim
  brjunoCover : BrjunoCoverClaim
  packetCover : PacketCoverClaim
  jacobiPrepSmallWidth : JacobiPrepSmallWidthClaim

theorem PaperIIRemainingInputs.toFinal (P : PaperIIRemainingInputs) : PaperIIInputsFinal where
  comparison := comparison_of_nonneg P.comparisonNonneg
  normalization := P.normalization
  inertiaTransfer := P.inertiaTransfer
  gapLabelling := P.gapLabelling
  infiniteExponent := P.infiniteExponent
  brjunoCover := P.brjunoCover
  packetCover := P.packetCover
  jacobiPrep := jacobiPrep_of_smallWidth P.jacobiPrepSmallWidth

/-- **Theorem 1.1** from the current remaining inputs. -/
theorem thm_joint_main (P : PaperIIRemainingInputs) {α : ℝ} (hα : Irrational α) :
    ∃ Sstar > 0, ∀ S ≥ Sstar, ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      AllLabelsOpen α R ∧ μH[1 / 2] (Sigma α 1 R) < ⊤ ∧ dimH (Sigma α 1 R) ≤ 1 / 2 ∧
        IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 :=
  thm_joint_final P.toFinal hα

/-- **Theorem 1.2** from the current remaining inputs. -/
theorem thm_liouville_main (P : PaperIIRemainingInputs) {α : ℝ} (hα : Irrational α)
    (hL : Liouville α) {S : ℝ} (hS : 0 < S) :
    ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      dimH (Sigma α 1 R) = 0 ∧ IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 :=
  thm_liouville_final P.toFinal hα hL hS

/-- **Theorem 3.10** from the current remaining inputs. -/
theorem thm_finite_exponent_main (P : PaperIIRemainingInputs) {α : ℝ} (hα : Irrational α)
    (hβ : AMO.beta α < ⊤) :
    ∃ Sgap > 0, ∀ S ≥ Sgap, ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      AllLabelsOpen α R :=
  thm_finite_exponent_refined P.toFinal.toRefined hα hβ

end SGD
