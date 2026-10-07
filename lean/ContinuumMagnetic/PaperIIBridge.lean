/-
# Paper II input derived from the Paper II formalization

`CMS.CriticalGeometricInputClaim` (Paper II, Theorems 1.1–1.2, as used by Paper III) follows
from the refined Paper II inputs of the `SpectralGapsDimension` library (`SGD.PaperIIInputsRefined`)
via its theorems `SGD.thm_joint_refined` and `SGD.thm_liouville_refined`.  So that hypothesis of
`PaperInputs` need not be assumed separately: it can be supplied by
`criticalGeometricInput_of_paperII`.

(Proof contributed by the Paper II formalization session.)
-/
import SpectralGapsDimension.Reductions
import ContinuumMagnetic.AnalyticInput

open MeasureTheory

/-- `CMS.CriticalGeometricInputClaim` from the refined Paper II inputs. -/
theorem CMS.criticalGeometricInput_of_paperII (P : SGD.PaperIIInputsRefined) :
    CMS.CriticalGeometricInputClaim := by
  intro α hα
  obtain ⟨Sstar, hS, h⟩ := SGD.thm_joint_refined P hα
  refine ⟨Sstar, hS, fun S' hS' => ?_, fun hL S' hS' => ?_⟩
  · obtain ⟨ρ, hρ, hR⟩ := h S' hS'
    refine ⟨ρ, hρ, fun R hsa hF hRS => ?_⟩
    obtain ⟨⟨ν, hν, hgaps⟩, hH, -⟩ := hR R ⟨hsa, hF⟩ hRS
    refine ⟨fun ν' hν' => ?_, hH⟩
    rwa [← SGD.IsDOSMeasure.unique hν hν']
  · have hL' : SGD.Liouville α := by
      unfold SGD.Liouville SGD.muIrr SGD.muSeq
      unfold CMS.OrdinaryLiouville at hL
      rw [hL]
      exact add_top 1
    obtain ⟨ρ, hρ, hR⟩ := SGD.thm_liouville_refined P hα hL' hS'
    exact ⟨ρ, hρ, fun R hsa hF hRS => (hR R ⟨hsa, hF⟩ hRS).1⟩
