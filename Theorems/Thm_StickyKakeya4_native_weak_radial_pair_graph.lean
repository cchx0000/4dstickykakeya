import Theorems.Thm_StickyKakeya4_native_rich_pair_tube_family
import Theorems.Thm_StickyKakeya4_transverse_original_strip_points
import Theorems.Thm_StickyKakeya4_original_pair_row_cut

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeWeakRadialPairGraph
open PlanarStripIntersection OriginalPairStripGeometry NativeRichPairTubeFamily
open TransverseOriginalStripPoints

def richRelation (Pts : Finset Point) (w lam : ℝ) (p q : Point) : Prop :=
  p≠q ∧ lam*(Pts.card : ℝ)≤(pairSupport Pts w (p,q)).card

/-- The finite native A.2 graph is constructed from original pair tubes,
original metric-ball counts, and the original wide-strip two-ends counts.
Its target estimates count the FULL original P support of every good tube. -/
theorem finite_weak_radial_graph
    (Pts : Finset Point) (w rho lam eps theta zeta eta : ℝ) (hPts : Pts.Nonempty)
    (hw : 0≤w) (hrho : 0<rho) (hrho1 : rho≤1)
    (hlam : 0<lam) (heps : 0≤eps) (hsmall : eps≤lam^2/2)
    (htheta : 0<theta) (hzeta : 0≤zeta) (heta : 0≤eta)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hballs : ∀ p∈Pts,
      ((Pts.filter (fun q => boxDistance p q≤rho)).card : ℝ)≤eps*Pts.card)
    (hwideballs : ∀ p∈Pts,
      ((Pts.filter (fun q => boxDistance p q≤4*(11*w/rho)/theta)).card : ℝ)≤zeta*Pts.card)
    (htwoends : ∀ z∈candidates Pts,
      ((pairSupport Pts (3*(11*w/rho)+2*theta) z).card : ℝ)≤eta*Pts.card) :
    ∃ G : Finset Pair, G⊆Pts.product Pts ∧
      (∀ z∈G, z.1≠z.2 ∧ ((pairSupport Pts w z).card : ℝ)<lam*Pts.card) ∧
      lam^2*((Pts.card : ℝ)^2-G.card-Pts.card)≤
        (lam^2*eta+4*zeta)*(Pts.card : ℝ)^2 := by
  classical
  obtain ⟨F,hFC,hFpoints,_hrichF,_hI,hcount,hcover⟩ :=
    original_rich_pair_representatives Pts w rho lam eps hPts hw hrho hrho1
      hlam heps hsmall hbox hballs
  let W := 11*w/rho
  let Bad := transverse F Pts normalX normalY offset W theta
  have hW : 0≤W := by dsimp [W]; positivity
  have hnorm (i : Pair) (hi : i∈F) :
      |normalX i|≤1 ∧ |normalY i|≤1 ∧ (|normalX i|=1 ∨ |normalY i|=1) :=
    original_pair_normalized i (hFpoints i hi).2.2
  have hbadcount : lam^2*(Bad.card : ℝ)≤4*zeta*Pts.card :=
    transverse_card_from_rich_family F Pts normalX normalY offset W theta zeta lam
      hW htheta hzeta hlam.le hcount (fun i hi => ⟨(hnorm i hi).1,(hnorm i hi).2.1⟩) hwideballs
  have hon (z : Pair) :
      |PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) z.1|≤w ∧
      |PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) z.2|≤w := by
    rw [(original_pair_on_line z).1,(original_pair_on_line z).2,abs_zero]
    exact ⟨hw,hw⟩
  have hrows (p : Point) (hpP : p∈Pts) (hgood : p∉Bad) :
      ((Pts.filter (fun q => richRelation Pts w lam p q)).card : ℝ)≤eta*Pts.card := by
    let Row := Pts.filter (fun q => richRelation Pts w lam p q)
    rcases Row.eq_empty_or_nonempty with hRow|hRow
    · change (Row.card : ℝ)≤eta*Pts.card
      rw [hRow,Finset.card_empty,Nat.cast_zero]
      exact mul_nonneg heta (Nat.cast_nonneg _)
    · obtain ⟨q0,hq0⟩ := hRow
      obtain ⟨hq0P,hq0R⟩ := Finset.mem_filter.mp hq0
      have hq0data : p≠q0 ∧ lam*(Pts.card : ℝ)≤(pairSupport Pts w (p,q0)).card := hq0R
      have hCand0 : (p,q0)∈candidates Pts := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hpP,hq0P⟩,hq0data.1⟩
      obtain ⟨j0,hj0,hcover0⟩ := hcover (p,q0) hCand0 hq0data.2
      have hp0 : |PlanarStripIntersection.residual (normalX j0) (normalY j0) (offset j0) p|≤W :=
        hcover0 p hpP (hon (p,q0)).1
      have hRowSub : Row⊆pairSupport Pts (3*W+2*theta) j0 := by
        intro q hq
        obtain ⟨hqP,hqR⟩ := Finset.mem_filter.mp hq
        have hqdata : p≠q ∧ lam*(Pts.card : ℝ)≤(pairSupport Pts w (p,q)).card := hqR
        have hCand : (p,q)∈candidates Pts := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hpP,hqP⟩,hqdata.1⟩
        obtain ⟨i,hi,hcoveri⟩ := hcover (p,q) hCand hqdata.2
        have hpi : |PlanarStripIntersection.residual (normalX i) (normalY i) (offset i) p|≤W :=
          hcoveri p hpP (hon (p,q)).1
        have hqi : |PlanarStripIntersection.residual (normalX i) (normalY i) (offset i) q|≤W :=
          hcoveri q hqP (hon (p,q)).2
        have hstrip := nontransverse_common_strip F Pts normalX normalY offset W theta p q
          hpP hqP hbox hgood i j0 hi hj0 (hnorm i hi).2.2 (hnorm j0 hj0).1
          (hnorm j0 hj0).2.1 hpi hqi hp0
        exact Finset.mem_filter.mpr ⟨hqP,hstrip⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hRowSub)).trans (htwoends j0 (hFC hj0))
  obtain ⟨G,hGP,hgoodG,hcardG⟩ := OriginalPairRowCut.exists_good_pairs
    Pts Bad (richRelation Pts w lam) eta heta hrows
  refine ⟨G,hGP,?_,?_⟩
  · intro z hz
    have hg := hgoodG z hz
    refine ⟨hg.2.1,lt_of_not_ge ?_⟩
    intro hlarge
    exact hg.2.2 ⟨hg.2.1,hlarge⟩
  · have h1 := mul_le_mul_of_nonneg_left hcardG (sq_nonneg lam)
    have h2 := mul_le_mul_of_nonneg_right hbadcount (Nat.cast_nonneg Pts.card)
    nlinarith only [h1,h2]

end NativeWeakRadialPairGraph
