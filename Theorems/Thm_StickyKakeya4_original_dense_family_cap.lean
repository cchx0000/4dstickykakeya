import Theorems.Thm_StickyKakeya4_original_admissible_shaded_family
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalDenseFamilyCap
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalUnitLineGrid OriginalClippedUnitTube OriginalArbitraryStripCapCharge

/-- The literal external-strip charge and the original densest-tube profile
imply a cap population on the same representative family. Empty caps cost zero;
no separate direction carrier or cap estimate is supplied. -/
theorem original_dense_external_cap
    (Pts : Finset Point) (G S : Finset Pair) (rho w W k C m sigma nx ny c : ℝ)
    (A : Set Point) (hrho : 0<rho) (hw : 0≤w) (hW : W≤1/4)
    (hk : 0≤k)
    (hunit : nx^2+ny^2=1) (hA : ∀ p∈A, |nx*p.1+ny*p.2-c|≤W)
    (hS : S⊆G) (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hchart : ∀ z∈S, ∀ v∈S, normalChart z=normalChart v)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hrich : ∀ z∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ))
    (hRlo : rho≤432*W+16*rho) (hRhi : 432*W+16*rho≤1)
    (hwide : ∀ z∈G, ∀ R : ℝ, rho≤R → R≤1 →
      ((physicalPairTube Pts R z).card : ℝ)≤C*(R/rho)^sigma*m) :
    4*k^2*((containedInSet S w A).card : ℝ)≤
      539*(C*((432*W+16*rho)/rho)^sigma*m)^2 := by
  by_cases hnonempty : (containedInSet S w A).Nonempty
  · obtain ⟨a,ha⟩ := hnonempty
    have hpair := original_arbitrary_strip_cap_pair_charge Pts G S rho w W k nx ny c A a
      hrho hw hW hk hunit hA ha hS hinj hchart hGP hbox hdistinct hrich
    have hbound := hwide a (hS (Finset.mem_filter.mp ha).1) _ hRlo hRhi
    have hp0 : (0:ℝ)≤((physicalPairTube Pts (432*W+16*rho) a).card : ℝ) := by positivity
    have hsq : ((physicalPairTube Pts (432*W+16*rho) a).card : ℝ)^2≤
        (C*((432*W+16*rho)/rho)^sigma*m)^2 := by
      nlinarith only [hbound, hp0,
        mul_nonneg (sub_nonneg.mpr hbound)
          hp0,
        sq_nonneg (C*((432*W+16*rho)/rho)^sigma*m-
          (physicalPairTube Pts (432*W+16*rho) a).card)]
    linarith only [hpair,hsq]
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty,Finset.card_empty,Nat.cast_zero,mul_zero]
    positivity

/-- Normalize the original pair charge by the ACTUAL two-sided rich-class
mass k=tau^2*m/2. There is no inverse cardinality of a newly normalized source. -/
theorem normalize_original_dense_cap (N A tau m : ℝ)
    (htau : 0<tau) (hm : 0<m)
    (h : 4*(tau^2*m/2)^2*N≤539*(A*m)^2) :
    N≤539*(A/tau^2)^2 := by
  have hpos : 0<tau^4*m^2 := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  have he : (tau^4*m^2)*(539*(A/tau^2)^2)=539*(A*m)^2 := by
    field_simp
  rw [he]
  nlinarith only [h]

end OriginalDenseFamilyCap
