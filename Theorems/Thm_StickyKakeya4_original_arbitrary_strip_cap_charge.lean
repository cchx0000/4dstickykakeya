import Theorems.Thm_StickyKakeya4_original_clipped_tube_cap_charge
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

noncomputable section
namespace OriginalArbitraryStripCapCharge
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube OriginalUnitLineParameters
open OriginalRadialSineGeometry NativeRadialClassPruning OriginalUnitLineGrid
open OriginalClippedUnitTube OriginalExternalTubeCapGeometry OriginalLocalizedLineCellCharge

/-- Every unit-normal affine line, with arbitrary offset, is represented
by the original-pair parameter convention used in the physical cap proof. -/
theorem external_unit_line_representation (nx ny c : ℝ) (hunit : nx^2+ny^2=1) :
    ∃ u : Pair, u.1≠u.2 ∧ ∀ p : Point, scaledResidual u p=nx*p.1+ny*p.2-c := by
  let u : Pair := ((2*c*nx,2*c*ny),(2*c*nx-ny,2*c*ny+nx))
  have hd : complexDifference u.1 u.2=⟨-ny,nx⟩ := by
    apply Complex.ext <;> dsimp [complexDifference,u] <;> ring
  have hnorm : ‖complexDifference u.1 u.2‖=1 := by
    have hh := Complex.sq_norm (complexDifference u.1 u.2)
    rw [hd,Complex.normSq_apply] at hh
    dsimp at hh
    rw [hd]
    nlinarith only [hh,hunit,norm_nonneg (⟨-ny,nx⟩ : ℂ)]
  have hne : u.1≠u.2 := by
    intro he
    have hz : complexDifference u.1 u.2=0 := by
      rw [he]
      apply Complex.ext <;> simp [complexDifference]
    rw [hz,norm_zero] at hnorm
    norm_num at hnorm
  have hx : unitX u=nx := by dsimp [unitX]; rw [hnorm]; dsimp [u]; ring
  have hy : unitY u=ny := by dsimp [unitY]; rw [hnorm]; dsimp [u]; ring
  refine ⟨u,hne,?_⟩
  intro p
  dsimp [scaledResidual,unitOffset]
  rw [hx,hy]
  dsimp [u]
  linear_combination -c*hunit

def containedInSet (S : Finset Pair) (w : ℝ) (A : Set Point) : Finset Pair :=
  S.filter (fun z => clippedTube z w⊆A)

/-- The cap bound holds for every geometrically placed set inside any
unit-normal W-strip. In particular, the containing rectangle may have an
arbitrary longitudinal center, orientation and offset. -/
theorem original_arbitrary_strip_cap_pair_charge
    (Pts : Finset Point) (G S : Finset Pair) (rho w W k nx ny c : ℝ)
    (A : Set Point) (a : Pair)
    (hrho : 0<rho) (hw : 0≤w) (hW : W≤1/4) (hk : 0≤k)
    (hunit : nx^2+ny^2=1)
    (hA : ∀ p∈A, |nx*p.1+ny*p.2-c|≤W)
    (ha : a∈containedInSet S w A) (hS : S⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hchart : ∀ z∈S, ∀ v∈S, normalChart z=normalChart v)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hrich : ∀ z∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) :
    4*k^2*((containedInSet S w A).card : ℝ)≤
      539*((physicalPairTube Pts (432*W+16*rho) a).card : ℝ)^2 := by
  obtain ⟨u,hu,hres⟩ := external_unit_line_representation nx ny c hunit
  have haS := (Finset.mem_filter.mp ha).1
  have hsub : containedInSet S w A⊆S.filter (parameterNear (72*W) a) := by
    intro z hz
    obtain ⟨hzS,hzcontain⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hzS,?_⟩
    apply original_common_external_strip_parameter_close z a u w W hw hW
      (hdistinct z (hS hzS)) (hdistinct a (hS haS)) hu
      (hbox z.1 (Finset.mem_product.mp (hGP (hS hzS))).1) (hchart z hzS a haS)
    · intro p hp
      rw [hres]
      exact hA p (hzcontain hp)
    · intro p hp
      rw [hres]
      exact hA p ((Finset.mem_filter.mp ha).2 hp)
  have hcount := original_local_line_cell_charge Pts G S rho (72*W) k a hrho hk
    (hdistinct a (hS haS)) hS hinj hGP hbox hdistinct hrich
  have hcard : ((containedInSet S w A).card : ℝ)≤
      ((S.filter (parameterNear (72*W) a)).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hout := (mul_le_mul_of_nonneg_left hcard (by positivity : 0≤4*k^2)).trans hcount
  simpa only [show 6*(72*W)+16*rho=432*W+16*rho by ring] using hout

end OriginalArbitraryStripCapCharge
