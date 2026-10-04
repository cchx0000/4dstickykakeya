import Theorems.Thm_StickyKakeya4_original_arbitrary_strip_cap_charge
import Theorems.Thm_StickyKakeya4_original_physical_tube_scale_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace OriginalGoodGraphCapFraction
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalUnitLineGrid OriginalClippedUnitTube OriginalArbitraryStripCapCharge
open OriginalPhysicalTubeScaleSelection

/-- The original good-pair radial cap pays the literal external-strip
pair charge at every legal physical query radius. -/
theorem original_good_graph_external_cap_charge
    (Pts : Finset Point) (G0 G4 S : Finset Pair)
    (rho w W Q tau m lam nx ny c : ℝ) (A : Set Point)
    (hrho : 0<rho) (hw : 0≤w) (hW : W≤1/4) (htau : 0<tau) (hm : 0 < m)
    (_hlam : 0≤lam) (hquery : 432*W+16*rho≤Q)
    (hS : S⊆G4) (hG4 : G4⊆G0) (hGP : G0⊆Pts.product Pts)
    (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hchart : ∀ z∈S, ∀ v∈S, normalChart z=normalChart v)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hgood : ∀ z∈G0, z.1≠z.2 ∧ ((physicalPairTube Pts Q z).card : ℝ)≤lam*Pts.card)
    (hrich : ∀ z∈G4,
      tau^2*m≤((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      tau^2*m≤((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ))
    (hunit : nx^2+ny^2=1) (hA : ∀ p∈A, |nx*p.1+ny*p.2-c|≤W) :
    tau^4*m^2*((containedInSet S w A).card : ℝ)≤539*lam^2*(Pts.card : ℝ)^2 := by
  by_cases hnonempty : (containedInSet S w A).Nonempty
  · obtain ⟨a,ha⟩ := hnonempty
    let k := tau^2*m/2
    have hclasses : ∀ z∈G4,
        2*k≤((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
        2*k≤((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ) := by
      intro z hz
      have he : 2*k=tau^2*m := by dsimp [k]; ring
      rw [he]
      exact hrich z hz
    have hpair := original_arbitrary_strip_cap_pair_charge Pts G4 S rho w W k nx ny c A a
      hrho hw hW (by dsimp [k]; positivity) hunit hA ha hS hinj hchart (hG4.trans hGP)
      hbox (fun z hz => (hgood z (hG4 hz)).1) hclasses
    have hbound : ((physicalPairTube Pts (432*W+16*rho) a).card : ℝ)≤lam*Pts.card :=
      (Nat.cast_le.mpr (Finset.card_le_card (physical_tube_mono Pts a hquery))).trans
        (hgood a (hG4 (hS (Finset.mem_filter.mp ha).1))).2
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (physicalPairTube Pts (432*W+16*rho) a).card)
      hbound 2
    dsimp [k] at hpair
    nlinarith only [hpair,hsq]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty,Finset.card_empty,Nat.cast_zero,mul_zero]
    positivity

private theorem original_source_relative_charge
    (Ncap N P G G4 H M L D beta tau m lam : ℝ)
    (hbeta : 0<beta) (htau : 0<tau) (hm : 0 < m) (hH : 0≤H)
    (hcap : tau^4*m^2*Ncap≤539*lam^2*P^2)
    (hdense : beta*P^2≤G) (hhalf : G/2≤H*G4)
    (hfamily : G4≤4*M^3*L^2*(D*m)^2*N) :
    Ncap≤(8*539*H*M^3*L^2*D^2*lam^2/(beta*tau^4))*N := by
  have hmass := mul_le_mul_of_nonneg_left hfamily hH
  have hsource : beta*P^2≤8*H*M^3*L^2*D^2*m^2*N := by
    nlinarith only [hdense,hhalf,hmass]
  have hleft := mul_le_mul_of_nonneg_left hcap hbeta.le
  have hright := mul_le_mul_of_nonneg_left hsource (show 0≤539*lam^2 by positivity)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hbeta (pow_pos htau 4))).mpr
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hm)).mp
  nlinarith only [hleft,hright]

/-- Exact finite cap fraction from the original good graph and actual
retained original family mass. The class/tube multiplicity is derived by
the original grid theorem, rather than an overlap premise. -/
theorem original_good_graph_cap_fraction
    (Pts : Finset Point) (G0 G G4 S : Finset Pair)
    (rho w W Q tau m lam nx ny c beta H M L D : ℝ) (A : Set Point)
    (hrho : 0<rho) (hw : 0≤w) (hW : W≤1/4) (htau : 0<tau) (hm : 0 < m)
    (hlam : 0≤lam) (hbeta : 0<beta) (hH : 0≤H) (hquery : 432*W+16*rho≤Q)
    (hS : S⊆G4) (hG4 : G4⊆G) (hG : G⊆G0) (hGP : G0⊆Pts.product Pts)
    (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hchart : ∀ z∈S, ∀ v∈S, normalChart z=normalChart v)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hgood : ∀ z∈G0, z.1≠z.2 ∧ ((physicalPairTube Pts Q z).card : ℝ)≤lam*Pts.card)
    (hrich : ∀ z∈G4,
      tau^2*m≤((G4.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      tau^2*m≤((G4.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ))
    (hdense : beta*(Pts.card : ℝ)^2≤G.card)
    (hhalf : (G.card : ℝ)/2≤H*G4.card)
    (hfamily : (G4.card : ℝ)≤4*M^3*L^2*(D*m)^2*S.card)
    (hunit : nx^2+ny^2=1) (hA : ∀ p∈A, |nx*p.1+ny*p.2-c|≤W) :
    ((containedInSet S w A).card : ℝ)≤
      (8*539*H*M^3*L^2*D^2*lam^2/(beta*tau^4))*S.card := by
  have hcap := original_good_graph_external_cap_charge Pts G0 G4 S rho w W Q tau m lam nx ny c A
    hrho hw hW htau hm hlam hquery hS (hG4.trans hG) hGP hinj hchart hbox hgood hrich hunit hA
  exact original_source_relative_charge _ _ _ _ _ H M L D beta tau m lam
    hbeta htau hm hH hcap hdense hhalf hfamily

end OriginalGoodGraphCapFraction
