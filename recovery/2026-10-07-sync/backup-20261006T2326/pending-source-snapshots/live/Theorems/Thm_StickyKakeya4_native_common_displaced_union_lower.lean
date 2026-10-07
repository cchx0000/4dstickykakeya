import Theorems.Thm_StickyKakeya4_native_displaced_ad_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeCommonDisplacedUnionLower
open Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening NativeDisplacedADLower

variable {X : Type*} [PseudoMetricSpace X]
local instance : DecidableEq X := Classical.decEq X

/-- A literal common union of displaced original fine alphabets inherits
the lower law from the original alphabet witnessing each center. The
number of component alphabets does not enter the lower constant. -/
theorem common_union_ball_lower {ι : Type*}
    (I : Finset ι) (A : ι → Finset X) (f : ι → X → X)
    {mu rho alpha K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho)
    (halpha : 1 ≤ alpha) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ∀i∈I, ADBounds (A i) mu K s)
    (hdisplace : ∀i∈I, ∀a∈A i, dist (f i a) a ≤ alpha*rho) :
    let B := I.biUnion (fun i => (A i).image (f i))
    ∀b∈B, ∀r : ℝ, rho ≤ r → r ≤ 1 →
      (r/rho)^s/(K^2*(4*alpha)^s) ≤ ((carrierBall B b r).card:ℝ) := by
  classical
  intro B b hb r hrho hr1
  obtain ⟨i,hi,hib⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hib
  have hmaps : ∀x∈A i, f i x∈B := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
  have hh := displaced_ball_lower (A i) B (f i) hmu hmurho halpha hK hs
    (hAD i hi) (hdisplace i hi) hmaps a ha r hrho hr1
  simpa only [hfa] using hh

end NativeCommonDisplacedUnionLower
