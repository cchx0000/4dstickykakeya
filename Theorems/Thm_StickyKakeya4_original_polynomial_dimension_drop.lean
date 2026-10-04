import Theorems.Thm_StickyKakeya4_original_tensor_frostman
import Theorems.Thm_StickyKakeya4_original_polynomial_elimination
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalPolynomialDimensionDrop
open OriginalTensorFrostman OriginalPolynomialElimination ActualRoundedAdditiveEnergy

def reducedAlphabet {n : ℕ} (A : Finset ℝ) (c : Fin (n+1) → ℝ)
    (j : Fin (n+1)) : Finset ℝ :=
  Finset.univ.biUnion (fun i : Fin n =>
    (A.product A).image (fun p => c j*p.1-c (j.succAbove i)*p.2))

def reducedPoint {n : ℕ} (c : Fin (n+1) → ℝ) (j : Fin (n+1))
    (a : Fin (n+1) → ℝ) : Fin n → ℝ :=
  fun i => c j*a (j.succAbove i)-c (j.succAbove i)*a j

lemma reduced_point_mem {n : ℕ} (A : Finset ℝ) (c : Fin (n+1) → ℝ)
    (j : Fin (n+1)) {a : Fin (n+1) → ℝ} (ha : a∈tensor A (n+1)) :
    reducedPoint c j a∈tensor (reducedAlphabet A c j) n := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩
  apply Finset.mem_image.mpr
  exact ⟨(a (j.succAbove i),a j),Finset.mem_product.mpr
    ⟨Fintype.mem_piFinset.mp ha _,Fintype.mem_piFinset.mp ha _⟩,rfl⟩

lemma reduced_projection_eq {n : ℕ} (v c a : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    (∑ i∈Finset.univ.erase j, v i*(c j*a i-c i*a j))=
      ∑ i : Fin n, v (j.succAbove i)*reducedPoint c j a i := by
  let f := fun i => v i*(c j*a i-c i*a j)
  have hz : f j=0 := by dsimp [f]; ring
  have hs := Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)
  have ht := Fin.sum_univ_succAbove f j
  rw [hz,add_zero] at hs
  rw [hz,zero_add] at ht
  exact hs.trans ht

/-- The actual original relation produces a genuine dimension drop into a
literal finite alphabet of original weighted differences. Both the original mesh
and the projection-cover lower bound are retained quantitatively. -/
theorem original_dimension_drop_from_relation {n : ℕ}
    (A : Finset ℝ) (v c : Fin (n+1) → ℝ) (j : Fin (n+1))
    {delta d B C L : ℝ} (hd : 0 < delta) (hden : 0 < d)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hA : ∀ a∈A, |a| ≤ B) (hlarge : d ≤ |c j|) (hupper : |c j| ≤ C)
    (hrelation : |∑ i, v i*c i| ≤ delta)
    (himage : L ≤ delta*((tensor A (n+1)).image
      (fun a => rounded delta (∑ i, v i*a i))).card) :
    d*L ≤ (2+2*C)*(2*B+4)*delta*
      ((tensor (reducedAlphabet A c j) n).image
        (fun b => rounded delta (∑ i, v (j.succAbove i)*b i))).card := by
  have hcne : c j≠0 := abs_pos.mp (hden.trans_le hlarge)
  have hc := original_polynomial_projection_elimination (tensor A (n+1)) v c j
    hd hB hcne (fun a ha => hA (a j) (Fintype.mem_piFinset.mp ha j)) hrelation
  have hsub : (tensor A (n+1)).image (fun a => rounded delta
      (∑ i∈Finset.univ.erase j, v i*(c j*a i-c i*a j))) ⊆
      (tensor (reducedAlphabet A c j) n).image
        (fun b => rounded delta (∑ i, v (j.succAbove i)*b i)) := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨reducedPoint c j a,reduced_point_mem A c j ha,
      congrArg (rounded delta) (reduced_projection_eq v c a j).symm⟩
  have hcard : (((tensor A (n+1)).image (fun a => rounded delta
      (∑ i∈Finset.univ.erase j, v i*(c j*a i-c i*a j)))).card:ℝ) ≤
      ((tensor (reducedAlphabet A c j) n).image
        (fun b => rounded delta (∑ i, v (j.succAbove i)*b i))).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hfactor : (2+2*|c j|)*(2*B+4) ≤ (2+2*C)*(2*B+4) :=
    mul_le_mul_of_nonneg_right (by linarith only [hupper]) (by positivity)
  have hu := mul_le_mul hfactor hcard (Nat.cast_nonneg _) (by positivity : 0 ≤ (2+2*C)*(2*B+4))
  have hlo := mul_le_mul_of_nonneg_right hlarge
    (show 0 ≤ (((tensor A (n+1)).image
      (fun a => rounded delta (∑ i, v i*a i))).card:ℝ) from Nat.cast_nonneg _)
  have hb := hlo.trans (hc.trans hu)
  have hscaled := mul_le_mul_of_nonneg_left hb hd.le
  have hgiven := mul_le_mul_of_nonneg_left himage hden.le
  nlinarith only [hscaled,hgiven]

end OriginalPolynomialDimensionDrop
