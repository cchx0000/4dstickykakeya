import Theorems.Thm_StickyKakeya4_native_rich_strip_representatives
import Theorems.Thm_StickyKakeya4_original_pair_strip_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

noncomputable section
namespace NativeRichPairTubeFamily
open PlanarStripIntersection NativeRichStripRepresentatives OriginalPairStripGeometry

/-- Actual ordered distinct pairs of original points. -/
def candidates (Pts : Finset Point) : Finset Pair := by
  classical
  exact (Pts.product Pts).filter (fun z => z.1≠z.2)

def pairSupport (Pts : Finset Point) (w : ℝ) (z : Pair) : Finset Point :=
  support Pts normalX normalY offset w z

/-- The native representative family is constructed solely from ORIGINAL
point pairs and the original point-ball profile. Normalized line coefficients
and all incidence witnesses are derived from those genuine pairs. -/
theorem original_rich_pair_representatives
    (Pts : Finset Point) (w rho lam eps : ℝ) (hPts : Pts.Nonempty)
    (hw : 0≤w) (hrho : 0<rho) (hrho1 : rho≤1)
    (hlam : 0<lam) (heps : 0≤eps) (hsmall : eps≤lam^2/2)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hballs : ∀ p∈Pts,
      ((Pts.filter (fun q => boxDistance p q≤rho)).card : ℝ)≤eps*Pts.card) :
    ∃ F : Finset Pair, F⊆candidates Pts ∧
      (∀ z∈F, z.1∈Pts ∧ z.2∈Pts ∧ z.1≠z.2) ∧
      (∀ z∈F, lam*(Pts.card : ℝ)≤(pairSupport Pts w z).card) ∧
      ((RichFamilyIncidenceBound.incidences F (pairSupport Pts w)).card : ℝ)≤2*Pts.card ∧
      lam*(F.card : ℝ)≤2 ∧
      ∀ z∈candidates Pts, lam*(Pts.card : ℝ)≤(pairSupport Pts w z).card →
        ∃ z'∈F, ∀ p∈Pts, |PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) p|≤w →
          |PlanarStripIntersection.residual (normalX z') (normalY z') (offset z') p|≤11*w/rho := by
  classical
  have hn (z : Pair) (hz : z∈candidates Pts) :
      |normalX z|≤1 ∧ |normalY z|≤1 ∧ (|normalX z|=1 ∨ |normalY z|=1) :=
    original_pair_normalized z (Finset.mem_filter.mp hz).2
  obtain ⟨F,hFC,hrich,_hpair,hI,hcount,hcover⟩ :=
    finite_rich_strip_representatives (candidates Pts) Pts normalX normalY offset
      w rho lam eps hPts hw hrho hrho1 hlam heps hsmall hbox hn hballs
  refine ⟨F,hFC,?_,hrich,hI,hcount,hcover⟩
  intro z hz
  obtain ⟨hp,hne⟩ := Finset.mem_filter.mp (hFC hz)
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  exact ⟨h1,h2,hne⟩

end NativeRichPairTubeFamily
