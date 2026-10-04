import Theorems.Thm_StickyKakeya4_original_three_dimensional_pencil_brush_groups
import Theorems.Thm_StickyKakeya4_original_three_dimensional_group_source_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalShadedBrushSlab
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalTubeCells OriginalThreeDimensionalPairEnergy
open OriginalThreeDimensionalPencilGeometry OriginalThreeDimensionalPencilPartition
open OriginalThreeDimensionalPencilUnitSlabs OriginalThreeDimensionalPencilBrushGroups
open OriginalThreeDimensionalGroupSourceMass

/-- The geometric pencil partition, actual finite shade union, and original
localized energy produce a genuine Euclidean slab from an actual brush.
No slab-population or overlap certificate is an input. -/
theorem exists_original_shaded_brush_slab (P X : Finset Point3) (B : Finset Pair3)
    (Y : Pair3 → Finset Point3) (delta rho K nu b h A s : ℝ) (N : ℕ)
    (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (hd : 0 < delta) (hquery : delta ≤ rho) (hrho1 : rho ≤ 1)
    (hK : 1 ≤ K) (hnu : 0 ≤ nu) (hP : P.Nonempty)
    (hb : 0 < b) (hsmall : rho ≤ b/4800) (hh : 0 < h) (hA : 0 < A)
    (hs : 0 < s) (hs1 : s ≤ 1) (hterminal : 1 ≤ 2*dyadicRadius rho N)
    (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1)
    (hfrostman : ∀ p∈P, ∀ r : ℝ, delta ≤ r → r ≤ 1 →
      ((P.filter (fun q => distance3 p q ≤ r)).card : ℝ) ≤ K*r^2*P.card)
    (hXP : X⊆P) (hout : ∀ x∈X,x∉physicalTube3 stem.1 stem.2 s)
    (hcellX : Set.InjOn (cell rho) X)
    (hY : ∀ z∈B,Y z⊆X)
    (hYtube : ∀ z∈B,Y z⊆physicalPairTube3 P (4*rho) z)
    (hYmass : ∀ z∈B,b ≤ rho*(Y z).card)
    (hsne : stem.2 (e 2)-stem.1 (e 2) ≠ 0)
    (hsmax : ∀ j,|stem.2 j-stem.1 j| ≤ |stem.2 (e 2)-stem.1 (e 2)|)
    (hsbox : ∀ j,|stem.1 j| ≤ 1)
    (hne : ∀ z∈B,z.2 (e 2)-z.1 (e 2) ≠ 0)
    (hmax : ∀ z∈B,∀ j,|z.2 j-z.1 j| ≤ |z.2 (e 2)-z.1 (e 2)|)
    (hcell : Set.InjOn (parameterCell rho (e 2)) B)
    (htrans : ∀ z∈B,∃ j,slope z (e 2) j ≠ slope stem (e 2) j)
    (hmeet : ∀ z∈B,∃ p∈P,p∈physicalTube3 stem.1 stem.2 (8*rho) ∧
      p∈physicalTube3 z.1 z.2 (8*rho))
    (hrich : ∀ z∈B,nu*rho*P.card ≤ ((physicalPairTube3 P (8*rho) z).card : ℝ))
    (hpop : h ≤ rho^2*B.card) (hglobal : rho^2*X.card ≤ A) :
    ∃ n : Point3, ∃ c : ℝ, (∑ j,n j^2)=1 ∧
      h^2*b^4*nu^2*P.card ≤
        400000000000000000000000000*((N:ℝ)+1)*K*(4000/s*A)^2*
          ((P.filter (fun x => |(∑ j,n j*x j)-c| ≤ 100*rho)).card : ℝ) := by
  have hrho := hd.trans_le hquery
  have hY8 (z : Pair3) (hz : z∈B) : Y z⊆physicalPairTube3 P (8*rho) z := by
    intro x hx
    obtain ⟨hxP,l,hl⟩ := Finset.mem_filter.mp (hYtube z hz hx)
    exact Finset.mem_filter.mpr ⟨hxP,l,hl.trans (by linarith only [hrho])⟩
  obtain ⟨R,_hRB,_hinj,_himage,hcard,_hcover,hunion,hsupport⟩ :=
    exists_original_pencil_brush_groups P X B Y rho s stem e hrho hs hs1 hXP hout hY hY8
      hsne hsmax hsbox hbox hne hmax htrans hmeet
  let F := pencilGroup B rho stem e
  let S := originalPencilSlab P rho stem e
  have hFB (v : Pair3) : F v⊆B := Finset.filter_subset _ _
  have hmass : h ≤ rho^2*∑ v∈R,((F v).card : ℝ) := by
    have he : (B.card : ℝ)=∑ v∈R,((F v).card : ℝ) := by exact_mod_cast hcard
    rwa [← he]
  have hsum : rho^2*∑ v∈R,(((F v).biUnion Y).card : ℝ) ≤ 4000/s*A := by
    have h1 := mul_le_mul_of_nonneg_left hunion (sq_nonneg rho)
    have h2 := mul_le_mul_of_nonneg_left hglobal (show 0 ≤ 4000/s by positivity)
    change rho^2*∑ v∈R,((pencilShadeUnion B rho stem e Y v).card : ℝ) ≤ 4000/s*A
    nlinarith only [h1,h2]
  obtain ⟨v,hv,hpopS⟩ := exists_original_shaded_group_source_mass R P S F Y
    delta rho K nu b h (4000/s*A) N (e 2) hd hquery hrho1 hK hnu hP hb hsmall hh
    (by positivity) hterminal hbox hfrostman
    (fun _ _ => Finset.filter_subset _ _)
    (fun v _ z hz => hne z (hFB v hz))
    (fun v _ z hz => hmax z (hFB v hz))
    (fun v _ => hcell.mono (hFB v))
    (fun v _ z hz => (hY z (hFB v hz)).trans hXP)
    (fun v _ z hz x hx => (Finset.mem_filter.mp (hYtube z (hFB v hz) hx)).2)
    (fun v _ z hz => hcellX.mono (hY z (hFB v hz)))
    (fun v _ z hz => hYmass z (hFB v hz))
    (fun v hv z hz => (hsupport v hv).2.2 z hz |>.1)
    (fun v _ z hz => hrich z (hFB v hz)) hmass hsum
  exact ⟨pencilUnitNormal stem e (pencilChart stem v e) (pencilScalar stem v e),
    rawPencilCenter stem e (pencilChart stem v e) (pencilScalar stem v e)/
      pencilNormalLength stem e (pencilChart stem v e) (pencilScalar stem v e),
    (hsupport v hv).1,hpopS⟩

end OriginalThreeDimensionalShadedBrushSlab
