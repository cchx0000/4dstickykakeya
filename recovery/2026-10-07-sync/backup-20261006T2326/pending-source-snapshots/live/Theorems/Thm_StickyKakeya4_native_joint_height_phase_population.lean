/- UNVERIFIED finite joint-key operator. Spatial and phase cover estimates
are displayed as separate inputs; their current-source readers are not
asserted by this module. No additional refinement is performed. -/
import Theorems.Thm_StickyKakeya4_native_configured_joint_relation
import Theorems.Thm_StickyKakeya4_native_retained_slice_count_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeJointHeightPhasePopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeConfiguredJointRelation NativeConfiguredThirdRelation
open NativeFiniteSliceHomogeneity NativeRetainedSliceCountTransfer NativeJointUniformCoarseRelations SelfUniform
open CanonicalConfiguredE4Bridge NativeHorizontalGrainSlice
open scoped BigOperators

/-- Count the literal joint support from its actual spatial and phase
projections. A and B are the two separately supplied covering bounds;
the desired product bound on joint labels is proved, not assumed. -/
theorem joint_support_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (R depth : ℕ) (T : Finset (Fin n × Index))
    (A B : ℝ) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (Hspace : ∀ h ∈ T.image (fun z => (jointKey D a m p R depth z).1),
      (((T.filter (fun z => (jointKey D a m p R depth z).1 = h)).image
        (fun z => (jointKey D a m p R depth z).2.1)).card : ℝ) ≤ A)
    (Hphase : ∀ h ∈ T.image (fun z => (jointKey D a m p R depth z).1),
      ∀ q ∈ (T.filter (fun z => (jointKey D a m p R depth z).1 = h)).image
        (fun z => (jointKey D a m p R depth z).2.1),
      (((T.filter (fun z => (jointKey D a m p R depth z).1 = h ∧
        (jointKey D a m p R depth z).2.1 = q)).image
          (fun z => (jointKey D a m p R depth z).2.2)).card : ℝ) ≤ B) :
    ((T.image (jointKey D a m p R depth)).card : ℝ) ≤
      A * B * (T.image (fun z => (jointKey D a m p R depth z).1)).card := by
  let key := jointKey D a m p R depth
  let heights := T.image (fun z => (key z).1)
  let cells := fun h => (T.filter (fun z => (key z).1 = h)).image (fun z => (key z).2.1)
  let phases := fun h q => (T.filter (fun z => (key z).1 = h ∧ (key z).2.1 = q)).image
    (fun z => (key z).2.2)
  let row := fun h => (cells h).biUnion (fun q => {q} ×ˢ phases h q)
  have hsub : T.image key ⊆ heights.biUnion (fun h => {h} ×ˢ row h) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    refine mem_biUnion.mpr ⟨(key x).1, mem_image_of_mem _ hx, ?_⟩
    apply mem_product.mpr
    refine ⟨mem_singleton_self _, ?_⟩
    refine mem_biUnion.mpr ⟨(key x).2.1,
      mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩, rfl⟩, ?_⟩
    exact mem_product.mpr ⟨mem_singleton_self _,
      mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, rfl, rfl⟩, rfl⟩⟩
  have hrow (h : ℤ) (hh : h ∈ heights) : ((row h).card : ℝ) ≤ A * B := by
    calc
      _ ≤ (∑ q ∈ cells h, ({q} ×ˢ phases h q).card : ℕ) := by
        exact_mod_cast (card_biUnion_le : (row h).card ≤ _)
      _ = ∑ q ∈ cells h, ((phases h q).card : ℝ) := by
        simp only [Nat.cast_sum, card_product, card_singleton, one_mul]
      _ ≤ ∑ _q ∈ cells h, B := sum_le_sum (fun q hq => Hphase h hh q hq)
      _ = ((cells h).card : ℝ) * B := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ A * B := mul_le_mul_of_nonneg_right (Hspace h hh) hB
  calc
    _ ≤ ((heights.biUnion (fun h => {h} ×ˢ row h)).card : ℝ) := Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ (∑ h ∈ heights, ({h} ×ˢ row h).card : ℕ) := by exact_mod_cast card_biUnion_le
    _ = ∑ h ∈ heights, ((row h).card : ℝ) := by
      simp only [Nat.cast_sum, card_product, card_singleton, one_mul]
    _ ≤ ∑ _h ∈ heights, A * B := sum_le_sum hrow
    _ = _ := by simp only [sum_const, nsmul_eq_mul, heights, key]; ring

/-- On the same original T, the installed pair and joint comparisons give
an actual distinct-geometric-pair lower in EVERY occupied joint class.
The cost is Q^4, with no equation of original edge and geometric pair counts. -/
theorem class_pair_count_from_caller {n K d : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (p : Parent) (s : Split) (P : Submodule ℝ E4)
    (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (depths : Fin K → ℕ)
    (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (T : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀ j x y, x ∈ T → y ∈ T →
      degree (fun _ : Fin n × Index => 1)
        (completeRelations D a m p s P hP hd F Fcfg R u
          (Fin.addCases (NativeConfiguredJointRelation.relations D a m p R depths) extra) j) T x ≤
      Q^2 * degree (fun _ : Fin n × Index => 1)
        (completeRelations D a m p s P hP hd F Fcfg R u
          (Fin.addCases (NativeConfiguredJointRelation.relations D a m p R depths) extra) j) T y)
    (j : Fin K) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Hspace : ∀ h ∈ T.image (fun z => (jointKey D a m p R (depths j) z).1),
      (((T.filter (fun z => (jointKey D a m p R (depths j) z).1 = h)).image
        (fun z => (jointKey D a m p R (depths j) z).2.1)).card : ℝ) ≤ A)
    (Hphase : ∀ h ∈ T.image (fun z => (jointKey D a m p R (depths j) z).1),
      ∀ q ∈ (T.filter (fun z => (jointKey D a m p R (depths j) z).1 = h)).image
        (fun z => (jointKey D a m p R (depths j) z).2.1),
      (((T.filter (fun z => (jointKey D a m p R (depths j) z).1 = h ∧
        (jointKey D a m p R (depths j) z).2.1 = q)).image
          (fun z => (jointKey D a m p R (depths j) z).2.2)).card : ℝ) ≤ B)
    (x : Fin n × Index) (hx : x ∈ T) :
    let key := jointKey D a m p R (depths j)
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    ((T.image pair).card : ℝ) ≤ (Q : ℝ)^4 * (A*B) *
      (T.image (fun z => (key z).1)).card *
      ((T.filter (fun z => key z = key x)).image pair).card := by
  intro key pair
  have HP := caller_geometricPair_uniformity D a m p s P hP hd F Fcfg R u
    (Fin.addCases (NativeConfiguredJointRelation.relations D a m p R depths) extra) T Q H
  have HK := caller_joint_uniformity D a m p s P hP hd F Fcfg R u depths extra T Q H j
  let J := T.filter (fun z => key z = key x)
  have hJ : J ⊆ T := filter_subset _ _
  have hrow := (fiber_card_average_cross T key (Q^2) HK (key x) (mem_image_of_mem key hx)).2
  have hrowR : (T.card : ℝ) ≤ ((Q : ℝ)^2 * (T.image key).card) * J.card := by
    have hh : (T.card : ℝ) ≤ (Q : ℝ)^2 * J.card * (T.image key).card := by exact_mod_cast hrow
    nlinarith only [hh]
  have hpoint := point_image_retention T J hJ ⟨x, hx⟩ pair Q HP 1
    ((Q : ℝ)^2 * (T.image key).card) (by positivity) (by simpa only [one_mul] using hrowR)
  have hkeys := joint_support_card D a m p R (depths j) T A B hA hB Hspace Hphase
  calc
    _ ≤ ((Q : ℝ)^2 * (T.image key).card) * (Q : ℝ)^2 * (J.image pair).card := by
      simpa only [one_mul] using hpoint
    _ = (Q : ℝ)^4 * (J.image pair).card * (T.image key).card := by ring
    _ ≤ (Q : ℝ)^4 * (J.image pair).card *
        (A * B * (T.image (fun z => (key z).1)).card) :=
      mul_le_mul_of_nonneg_left hkeys (by positivity)
    _ = _ := by ring

end NativeJointHeightPhasePopulation
