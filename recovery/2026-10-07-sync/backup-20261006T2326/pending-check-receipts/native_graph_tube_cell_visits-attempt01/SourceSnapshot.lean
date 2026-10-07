import Theorems.Thm_StickyKakeya4_original_w_core_dynamics
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeGraphTubeCellVisits
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalDiameterCount

/-- The fixed-tube physical-cell menu of the actual deduplicated graph. -/
def visited {T : Type*} [DecidableEq T] (I : Finset (E4 × T)) (Delta : ℝ) (t : T) :
    Finset Index := (I.filter (fun e => e.2=t)).image (fun e => wzDyadicCellIndex Delta e.1)

/-- In one rho-height window, actual tube incidences have coordinate diameter
at most4rho. This includes the real analytic tube error without a grid-origin
assumption or an assertion that original edge multiplicities are one. -/
lemma same_tube_coordinate_diameter {T : Type*} [DecidableEq T]
    (I : Finset (E4 × T)) (base slope : T → E4) {rho delta : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hinc : ∀p t, (p,t)∈I → ∀j, |p j-base t j-p 3*slope t j| ≤ delta)
    (hslope : ∀t∈I.image Prod.snd, ∀j, |slope t j| ≤ 2)
    (hdiam : ∀p∈I.image Prod.fst, ∀q∈I.image Prod.fst, |p 3-q 3| ≤ rho)
    (p q : E4) (t : T) (hp : (p,t)∈I) (hq : (q,t)∈I) (j : Fin 4) :
    |p j-q j| ≤ 4*rho := by
  have ht := hslope t (mem_image_of_mem Prod.snd hp) j
  have hd := hdiam p (mem_image_of_mem Prod.fst hp) q (mem_image_of_mem Prod.fst hq)
  calc
    |p j-q j| = |(p j-base t j-p 3*slope t j)-(q j-base t j-q 3*slope t j)+
        (p 3-q 3)*slope t j| := by congr 1; ring
    _ ≤ (|p j-base t j-p 3*slope t j|+|q j-base t j-q 3*slope t j|)+
        |(p 3-q 3)*slope t j| :=
      (abs_add _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ delta+delta+rho*2 := add_le_add (add_le_add (hinc p t hp j) (hinc q t hq j))
      (by rw [abs_mul]; exact mul_le_mul hd ht (abs_nonneg _) hrho)
    _ ≤ 4*rho := by nlinarith only [hrho,hrho1,hdscale]

/-- A tube of the same actual graph visits only a fixed number of physical
cells at a prepared scale. The denominator for later averaging is the set
of active tube indices, not the original incidence occurrences. -/
theorem visited_card_le {T : Type*} [DecidableEq T]
    (I : Finset (E4 × T)) (base slope : T → E4) {rho delta Delta : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hDelta : rho/2 ≤ Delta)
    (hinc : ∀p t, (p,t)∈I → ∀j, |p j-base t j-p 3*slope t j| ≤ delta)
    (hslope : ∀t∈I.image Prod.snd, ∀j, |slope t j| ≤ 2)
    (hdiam : ∀p∈I.image Prod.fst, ∀q∈I.image Prod.fst, |p 3-q 3| ≤ rho)
    (t : T) (ht : t∈I.image Prod.snd) : (visited I Delta t).card ≤ 17^4 := by
  obtain ⟨z,hz,hzt⟩ := mem_image.mp ht
  have hz' : (z.1,t)∈I := by simpa only [←hzt,Prod.mk.eta] using hz
  have hDpos : 0 < Delta := (half_pos hrho).trans_le hDelta
  have hsub : visited I Delta t⊆indexBox (wzDyadicCellIndex Delta z.1) 8 := by
    intro c hc
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hc
    obtain ⟨hwI,hwt⟩ := mem_filter.mp hw
    have hw' : (w.1,t)∈I := by simpa only [←hwt,Prod.mk.eta] using hwI
    apply Fintype.mem_piFinset.mpr
    intro j
    apply NativeQuantizedLinePackets.floor_mem_interval 8
    rw [←sub_div,abs_div,abs_of_pos hDpos]
    apply (div_le_iff₀ hDpos).mpr
    have hgap := same_tube_coordinate_diameter I base slope hrho.le hrho1 hdscale
      hinc hslope hdiam w.1 z.1 t hw' hz' j
    norm_num
    linarith only [hgap,hDelta]
  exact (card_le_card hsub).trans_eq (by rw [indexBox_card]; norm_num)

end NativeGraphTubeCellVisits
