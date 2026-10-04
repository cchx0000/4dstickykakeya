import Theorems.Thm_StickyKakeya4_native_original_chart_metric
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeOriginalParentCount
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeOriginalChartMetric
open scoped ENNReal BigOperators

/-- Actual height-to-offset displacement; this is computed from the original
finite source and is not asserted to be a universal constant. -/
def chartReach {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) : NNReal :=
  univ.sup fun i : Fin n =>
    ⟨|((shift D a : ℤ) : ℝ)*mesh D-offset (D.line i) (3 : Fin 4)|, abs_nonneg _⟩
lemma le_chartReach {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (i : Fin n) :
    |((shift D a : ℤ) : ℝ)*mesh D-offset (D.line i) (3 : Fin 4)| ≤ chartReach D a := by
  exact_mod_cast (Finset.le_sup (f := fun i : Fin n =>
    (⟨|((shift D a : ℤ) : ℝ)*mesh D-offset (D.line i) (3 : Fin 4)|, abs_nonneg _⟩ : NNReal)) (mem_univ i))

def neighbours (p : Parent) : Finset Parent :=
  (Fintype.piFinset fun j => Icc (p.1 j-1) (p.1 j+1)) ×ˢ
    (Fintype.piFinset fun j => Icc (p.2 j-1) (p.2 j+1))
lemma neighbours_card (p : Parent) : (neighbours p).card = 729 := by
  have hc (k : ℤ) : (Icc (k-1) (k+1)).card=3 := by
    have hh : ((Icc (k-1) (k+1)).card : ℤ)=3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp [neighbours, Fintype.card_piFinset, hc]

lemma floor_neighbour {x y : ℝ} (h : |x-y| ≤ 1) : ⌊x⌋ ∈ Icc (⌊y⌋-1) (⌊y⌋+1) := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  apply mem_Icc.mpr
  constructor
  · simpa only [Int.floor_sub_one] using Int.floor_mono (show y-1≤x by linarith)
  · simpa only [Int.floor_add_one] using Int.floor_mono (show x≤y+1 by linarith)

lemma parentLabel_mem_neighbours {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (N : ℕ) {r : ℝ}
    (hs : 6*(N:ℝ)*r ≤ 1) (hb : ((3+6*(chartReach D a:ℝ))/4)*(N:ℝ)*r ≤ 1)
    (i k : Fin n) (hik : dist (wzCarrierPoint D i) (wzCarrierPoint D k) ≤ r) :
    parentLabel D a N i ∈ neighbours (parentLabel D a N k) := by
  have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
  apply mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro j
    apply floor_neighbour
    rw [← mul_sub, abs_mul, abs_of_nonneg hNr]
    have hh := (slope_sub_le h i k j).trans (mul_le_mul_of_nonneg_left hik (by norm_num))
    exact (mul_le_mul_of_nonneg_left hh hNr).trans (by nlinarith [hs])
  · apply Fintype.mem_piFinset.mpr
    intro j
    apply floor_neighbour
    rw [← mul_sub, abs_mul, abs_of_nonneg hNr]
    have hm := le_chartReach D a k
    have hd := shiftedIntercept_sub_le h i k a j
    have hr := dist_nonneg (x:=wzCarrierPoint D i) (y:=wzCarrierPoint D k)
    have hcoef : (0:ℝ) ≤ (3+6*(chartReach D a:ℝ))/4 := by positivity
    have hh : |shiftedIntercept (D.line i) (mesh D) (shift D a) j -
        shiftedIntercept (D.line k) (mesh D) (shift D a) j| ≤
        ((3+6*(chartReach D a:ℝ))/4)*r :=
      hd.trans ((mul_le_mul_of_nonneg_right (by linarith :
        (3+6*|((shift D a:ℤ):ℝ)*mesh D-offset (D.line k) (3:Fin 4)|)/4 ≤
          (3+6*(chartReach D a:ℝ))/4) hr).trans
            (mul_le_mul_of_nonneg_left hik hcoef))
    exact (mul_le_mul_of_nonneg_left hh hNr).trans (by nlinarith [hb])

/-- Counting the actual original parent labels by native carrier AD. The
source-dependent chart reach remains explicit in the permitted radius. -/
theorem parent_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (N : ℕ) {r : ℝ}
    (hdr : D.thickness ≤ r) (hr1 : r ≤ 1)
    (hs : 6*(N:ℝ)*r ≤ 1) (hb : ((3+6*(chartReach D a:ℝ))/4)*(N:ℝ)*r ≤ 1) :
    ((parents D a N).card:ℝ≥0∞) *
      ((ENNReal.ofReal D.thickness).rpow eta*(ENNReal.ofReal (r/D.thickness))^3) ≤
        729*(n:ℝ≥0∞) := by
  let P := parents D a N
  let f := parentLabel D a N
  let pick : Parent → Fin n := fun p =>
    if hp : ∃ i, f i=p then Classical.choose hp else ⟨0,h.1.1⟩
  have hpick (p : Parent) (hp : p∈P) : f (pick p)=p := by
    obtain ⟨i,_hi,he⟩ := mem_image.mp hp
    have he' : ∃ i, f i=p := ⟨i,he⟩
    dsimp [pick]
    rw [dif_pos he']
    exact Classical.choose_spec he'
  have hover (i : Fin n) :
      (P.filter fun p=>dist (wzCarrierPoint D i) (wzCarrierPoint D (pick p))≤r).card≤729 := by
    rw [← neighbours_card (f i)]
    apply card_le_card
    intro p hp
    obtain ⟨hpP,hnear⟩ := mem_filter.mp hp
    have hh := parentLabel_mem_neighbours h a N hs hb (pick p) i (by simpa [dist_comm] using hnear)
    rw [show parentLabel D a N (pick p)=p from hpick p hpP] at hh
    exact hh
  have hdouble :
      ∑ p∈P, wzCarrierBallCount D (pick p) r =
        ∑ i:Fin n, (P.filter fun p=>dist (wzCarrierPoint D i) (wzCarrierPoint D (pick p))≤r).card := by
    simp only [wzCarrierBallCount, card_eq_sum_ones, sum_filter]
    exact sum_comm
  calc
    _ = ∑ _p∈P, (ENNReal.ofReal D.thickness).rpow eta*(ENNReal.ofReal (r/D.thickness))^3 := by
      simp [P]
    _ ≤ ∑ p∈P, (wzCarrierBallCount D (pick p) r : ℝ≥0∞) := by
      apply sum_le_sum
      intro p _hp
      exact (h.1.2.2.2.2.2.2.2.2.2.2.1 (pick p) r hdr hr1).1
    _ = ∑ i:Fin n, ((P.filter fun p=>dist (wzCarrierPoint D i) (wzCarrierPoint D (pick p))≤r).card:ℝ≥0∞) := by
      exact_mod_cast hdouble
    _ ≤ ∑ _i:Fin n, (729:ℝ≥0∞) := sum_le_sum (fun i _hi=>by exact_mod_cast hover i)
    _ = _ := by simp [mul_comm]

end NativeOriginalParentCount
