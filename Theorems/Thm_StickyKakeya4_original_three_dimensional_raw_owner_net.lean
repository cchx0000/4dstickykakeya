import Theorems.Thm_StickyKakeya4_native_original_grid_balanced_fibers
import Theorems.Thm_StickyKakeya4_original_three_dimensional_fiber_slab_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalThreeDimensionalRawOwnerNet
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalLiteralSlabCover OriginalThreeDimensionalSlabProjection
open OriginalThreeDimensionalVoronoiFibers OriginalThreeDimensionalFiberSlabGeometry

def frameSlice (P : Finset Point3) (b : Frame3) (c Delta : ℝ) : Finset Point3 :=
  P.filter (fun x => |frameCoordinate b 2 x-c| ≤ Delta)

/-- The owner net is constructed from actual raw-slab endpoints. Its full
ORIGINAL fibers fit inside the ambient expanded slab, and its exact
orthogonal image is a genuinely separated unweighted set. No population
balance is assumed or concluded here. -/
theorem exists_original_raw_owner_net (P S : Finset Point3) (b : Frame3)
    (c rho Delta : ℝ) (hSP : S⊆P) (hS : S.Nonempty) (hDelta : 0 < Delta)
    (hsmall : 48*rho ≤ Delta)
    (hraw : ∀ p∈S,|frameCoordinate b 2 p-c| ≤ 3*rho) :
    ∃ C : Finset Point3,∃ hC : C.Nonempty,C⊆S ∧ C⊆P ∧
      (∀ p∈C,∀ q∈C,p≠q → Delta/4 ≤ distance3 p q) ∧
      (∀ x∈S,distance3 x (originalOwner C hC x) < Delta/4) ∧
      S⊆originalCarrier P C hC (Delta/4) ∧
      originalCarrier P C hC (Delta/4)⊆frameSlice P b c Delta ∧
      (∀ p∈C,∀ q∈C,p≠q → Delta/8 ≤ distance2 (project b p) (project b q)) ∧
      Set.InjOn (project b) C ∧ (C.image (project b)).card=C.card := by
  obtain ⟨C,hC,hCS,hsep,hnear⟩ := exists_original_euclidean_owner_net S hS (Delta/4) (by positivity)
  have hproj (p : Point3) (hp : p∈C) (q : Point3) (hq : q∈C) (hne : p≠q) :
      Delta/8 ≤ distance2 (project b p) (project b q) :=
    original_raw_net_projected_separation b c rho Delta p q (hraw p (hCS hp))
      (hraw q (hCS hq)) (hsep p hp q hq hne) hsmall
  have hinj : Set.InjOn (project b) C := by
    intro p hp q hq he
    by_contra hne
    have hs := hproj p hp q hq hne
    rw [he] at hs
    have hz : distance2 (project b q) (project b q)=0 := dist_self _
    rw [hz] at hs
    linarith only [hs,hDelta]
  refine ⟨C,hC,hCS,hCS.trans hSP,hsep,hnear,?_,?_,hproj,hinj,Finset.card_image_of_injOn hinj⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨hSP hx,hnear x hx⟩
  · intro x hx
    obtain ⟨hxP,howner⟩ := Finset.mem_filter.mp hx
    have hpraw := hraw (originalOwner C hC x) (hCS (original_owner_mem C hC x))
    refine Finset.mem_filter.mpr ⟨hxP,?_⟩
    exact original_full_fiber_in_expanded_slab b c rho (Delta/4) Delta x
      (originalOwner C hC x) hpraw howner.le (by linarith only [hsmall,hDelta])

end OriginalThreeDimensionalRawOwnerNet
