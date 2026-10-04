import Theorems.Thm_StickyKakeya4_original_slab_collision
import Theorems.Thm_StickyKakeya4_original_polynomial_dimension_drop
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalFiniteDimensionReduction
open ActualRoundedAdditiveEnergy OriginalPolynomialSlab OriginalSlabRelation OriginalSlabCollision
open OriginalTensorFrostman OriginalPolynomialDimensionDrop

def coefficientBound (n : ℕ) (d L : ℝ) : ℝ :=
  d*(1+4*((2*(n:ℝ)+1)*(slabRadius n d L:ℝ)))

lemma original_interval_abs_bound {a lo d : ℝ} (hd : 0 ≤ d)
    (hlo : lo ≤ a) (hhi : a ≤ lo+d) : |a| ≤ |lo|+d := by
  apply abs_le.mpr
  constructor
  · linarith only [hlo,neg_abs_le lo,hd]
  · linarith only [hhi,le_abs_self lo]

/-- A completely finite same-mesh dimension reduction. The relation and its
nonzero coefficient are constructed from original lattice copies; the lower
cover of the new actual difference alphabet is proved, not supplied. -/
theorem exists_original_finite_dimension_reduction (n : ℕ)
    (A : Finset ℝ) (v : Fin (n+1) → ℝ) {delta lo d L : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hd : 0 < d) (hL : 0 < L)
    (hn : 1 ≤ n) (hv : ∀ i, (1/2:ℝ) ≤ v i ∧ v i ≤ 1)
    (hbox : ∀ a∈A, lo ≤ a ∧ a ≤ lo+d)
    (himage : L ≤ delta*((tensor A (n+1)).image
      (fun a => rounded delta (∑ i, v i*a i))).card) :
    ∃ tau∈slabVectors n (slabRadius n d L) v,
      ∃ sigma∈slabVectors n (slabRadius n d L) v,
        ∃ x∈tensor A (n+1), ∃ y∈tensor A (n+1), ∃ j : Fin (n+1),
          let c := relationCoefficients d tau sigma x y
          d ≤ |c j| ∧ (∀ i, |c i| ≤ coefficientBound n d L) ∧
          d*L ≤ (2+2*coefficientBound n d L)*(2*(|lo|+d)+4)*delta*
            ((tensor (reducedAlphabet A c j) n).image
              (fun b => rounded delta (∑ i, v (j.succAbove i)*b i))).card := by
  obtain ⟨tau,htau,sigma,hsigma,hneq,x,hx,y,hy,hcell⟩ :=
    exists_original_slab_collision n (tensor A (n+1)) v hdelta hdelta1 hd hL hn hv
      (fun a ha i => hbox (a i) (Fintype.mem_piFinset.mp ha i)) himage
  have hxy : ∀ i, |x i-y i| ≤ d := by
    intro i
    obtain ⟨hxlo,hxhi⟩ := hbox (x i) (Fintype.mem_piFinset.mp hx i)
    obtain ⟨hylo,hyhi⟩ := hbox (y i) (Fintype.mem_piFinset.mp hy i)
    exact abs_le.mpr ⟨by linarith only [hxlo,hyhi],by linarith only [hxhi,hylo]⟩
  have htauB : ∀ i, |(tau i:ℝ)| ≤ (2*(n:ℝ)+1)*(slabRadius n d L:ℝ) := by
    obtain ⟨a,_ha,haeq⟩ := Finset.mem_image.mp htau
    rw [← haeq]
    exact slabVector_coordinate_bound hv a
  have hsigmaB : ∀ i, |(sigma i:ℝ)| ≤ (2*(n:ℝ)+1)*(slabRadius n d L:ℝ) := by
    obtain ⟨a,_ha,haeq⟩ := Finset.mem_image.mp hsigma
    rw [← haeq]
    exact slabVector_coordinate_bound hv a
  obtain ⟨⟨j,hlarge⟩,hupper⟩ :=
    original_relation_coefficient_bounds x y tau sigma hd hneq hxy htauB hsigmaB
  let c := relationCoefficients d tau sigma x y
  have hrel : |∑ i, v i*c i| ≤ delta :=
    original_translated_cell_relation v x y tau sigma hdelta hcell
  have hC : 0 ≤ coefficientBound n d L := (abs_nonneg (c j)).trans (hupper j)
  have hB : 0 ≤ |lo|+d := add_nonneg (abs_nonneg _) hd.le
  have hA : ∀ a∈A, |a| ≤ |lo|+d :=
    fun a ha => original_interval_abs_bound hd.le (hbox a ha).1 (hbox a ha).2
  have hg := original_dimension_drop_from_relation A v c j hdelta hd hB hC
    hA hlarge (hupper j) hrel himage
  exact ⟨tau,htau,sigma,hsigma,x,hx,y,hy,j,hlarge,hupper,hg⟩

end OriginalFiniteDimensionReduction
