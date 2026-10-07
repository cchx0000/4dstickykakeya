/- UNVERIFIED combined actual higher-geometry and literal remembered-source caller.
No compiler run or gate request. Frozen source files are preserved unchanged.
This file combines48 transfer declarations,7 configured quotient readers,
and34 actual caller declarations. Only chain-internal imports are removed;
source units receive explicit anonymous-section closures where required.
The actual native caller derives its original witness, first alignment
patch, common physical height,4sigma source halo,13sigma scalar witnesses,
and full-Y all-radius grid cover in UNROTATED source cells.
Mass/key populations are on ref.E1 at sigma=S.thickness. Later-parent
normalized incidence images and all-radius profile LOWER bounds are not
claimed here. Fixed finite schedules and genuine later-cut comparability
remain required. No kappa=0 or original theorem closure is claimed.
-/
import Theorems.Thm_StickyKakeya4_native_finite_slice_homogeneity
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_native_higher_quotient_parent_transport
import Theorems.Thm_StickyKakeya4_native_literal_grid_overlap
import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge
import Theorems.Thm_StickyKakeya4_native_literal_aligned_set
import Theorems.Thm_StickyKakeya4_native_recoded_grid_upper
import Theorems.Thm_StickyKakeya4_original_representative_grid_comparison
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_quotient_grid_centers
import Theorems.Thm_StickyKakeya4_native_remembered_source_construction
import Theorems.Thm_StickyKakeya4_native_extra_queried_rank_configuration
import Theorems.Thm_StickyKakeya4_native_fixed_source_reference
import Theorems.Thm_StickyKakeya4_native_literal_Y_height_alignment
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning
import Theorems.Thm_StickyKakeya4_native_finite_kakeya_counts
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_two_stage_transversality_budget

/- Frozen source unit Thm_StickyKakeya4_native_actual_higher_transfer_construction_draft_2020.lean
   SHA256 35bc5af343b0bcc4bd08caf6c45b7a455639b80ac711cd69ca273ea02a3943b0 -/
/- UNVERIFIED consolidated actual higher-geometry transfer.
All48 declarations are uncompiled drafts; no imported-axiom readback has run.
The15-declaration literal-chart unit is retained unchanged for provenance.
Its literal higherXIndex/higherYIndex specialization is NOT the actual S caller.
The actual source uses NativePackedHigherCapacityDraft2006: the packed frame
is evaluated on unchanged native cell centers and costs a DERIVED13^4 cell
capacity. No rotation/native-admission of the cubical source is asserted.
The final endpoint first_aligned_native_Y_cover derives hereditary all-radius
higher-Y occupied-grid uppers from original NearlyLiteralAligned data and
actual occurrence/height readbacks. Point mass/degree and key uniformities
then supply the lower counts through packed_dense_X/packed_Y_class_lower.
Only fixed scheduled keys may be uniformized; later-cut comparability and
explicit gap interpolation remain caller obligations. No kappa=0 claim.

Consolidation changes only chain-internal imports and source-unit section
closures. The final source-facing endpoint is appended as its own unit.
Exact namespace-qualified declaration and source hashes are in the adjacent
consumer-drafts/native_actual_higher_transfer_construction_draft_2020.manifest.json.
-/

/- Frozen source unit: Thm_StickyKakeya4_native_actual_higher_key_population_draft_1955.lean
   SHA256 be49de7b46465250461ca1ffa20da6608e5fb11c2b452d643901c6c7017fb2f2 -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeActualHigherKeyPopulationDraft1955
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeJointUniformCoarseRelations NativeFiniteSliceHomogeneity
open scoped BigOperators

def higherXIndex (k : Index) : Fin 2 → ℤ :=
  fun j => k j.castSucc.castSucc

/-- Floor of the actual scalar quotient in source-cell mesh units. The
fields are evaluated at the literal source-cell time, never rawHeight. -/
def higherYIndex (C F : ℤ → ℝ) (k : Index) : ℤ :=
  k 2 + ⌊(1/2:ℝ)-C (k 3)*((k 0:ℝ)+1/2)-F (k 3)*((k 1:ℝ)+1/2)⌋

def higherKey (C F : ℤ → ℝ) (k : Index) : ℤ × ℤ :=
  (k 3,higherYIndex C F k)

def coarseHigherKey (C F : ℤ → ℝ) (R : ℕ) (k : Index) : ℤ × ℤ :=
  (k 3,higherYIndex C F k/(R:ℤ))

def higherQuotient (mu : ℝ) (C F : ℤ → ℝ) (k : Index) : ℝ :=
  mu*((k 2:ℝ)+1/2-C (k 3)*((k 0:ℝ)+1/2)-F (k 3)*((k 1:ℝ)+1/2))

theorem higherYIndex_readback (mu : ℝ) (hmu : 0<mu)
    (C F : ℤ → ℝ) (k : Index) :
    ⌊higherQuotient mu C F k/mu⌋=higherYIndex C F k := by
  have he : higherQuotient mu C F k/mu=(k 2:ℝ)+
      ((1/2:ℝ)-C (k 3)*((k 0:ℝ)+1/2)-F (k 3)*((k 1:ℝ)+1/2)) := by
    unfold higherQuotient
    field_simp [hmu.ne']
    <;> ring
  rw [he,Int.floor_intCast_add]
  rfl

theorem higher_coordinates_injective (C F : ℤ → ℝ) {k l : Index}
    (hY : higherKey C F k=higherKey C F l)
    (hX : higherXIndex k=higherXIndex l) : k=l := by
  have h0 : k 0=l 0 := by simpa only [higherXIndex] using congrFun hX 0
  have h1 : k 1=l 1 := by simpa only [higherXIndex] using congrFun hX 1
  have h3 : k 3=l 3 := congrArg Prod.fst hY
  have h2 : k 2=l 2 := by
    have hh := congrArg Prod.snd hY
    change higherYIndex C F k=higherYIndex C F l at hh
    simp only [higherYIndex,h0,h1,h3] at hh
    omega
  funext j
  fin_cases j <;> assumption

/-- Distinct source points in one literal higher-Y fiber are exactly
distinct higher-X indices. There is no point multiplicity hidden here. -/
theorem higherX_fiber_card (P : Finset Index) (C F : ℤ → ℝ) (v : ℤ × ℤ) :
    ((P.filter (fun k => higherKey C F k=v)).image higherXIndex).card=
      (P.filter (fun k => higherKey C F k=v)).card := by
  apply card_image_iff.mpr
  intro k hk l hl he
  exact higher_coordinates_injective C F
    ((mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm) he

theorem aligned_normal_scale (N tau w : ℝ) (hN : N*w=64) (hTau : tau=4096*w) :
    (N/512)*tau=512 := by
  calc
    _ = 8*(N*w) := by rw [hTau]; ring
    _ = 512 := by rw [hN]; norm_num

theorem aligned_mesh_in_source (N rho tau d sigma : ℝ) (hTau : tau≠0)
    (hd : d=8*rho) (hSigma : sigma=N*d/64) :
    (N/512)*tau*(rho/tau)=sigma/64 := by
  rw [hSigma,hd]
  field_simp [hTau]
  <;> ring

/-- Sum the actual point degrees. E and A are literal sets of output
tube/cell incidences, not older antecedent relations. -/
theorem subset_card_le_point_cap {n : ℕ}
    (E A : Finset (Fin n × Index)) (hAE : A⊆E) (U : ℝ)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U) :
    (A.card:ℝ)≤U*(A.image Prod.snd).card := by
  have he : (A.card:ℝ)=∑k∈A.image Prod.snd,
      ((A.filter (fun e => e.2=k)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image Prod.snd A
  rw [he]
  calc
    _ ≤ ∑_k∈A.image Prod.snd,U := by
      apply sum_le_sum
      intro k _hk
      exact (show ((A.filter (fun e => e.2=k)).card:ℝ)≤
        (E.filter (fun e => e.2=k)).card by
          exact_mod_cast card_le_card (filter_subset_filter _ hAE)).trans (hDegree k)
    _ = _ := by simp [mul_comm]

/-- A global occupied-key UPPER bound and actual graph mass force a
LOWER number of actual points in every occupied uniform class. -/
theorem occupied_class_point_lower {n : ℕ} {K : Type*} [DecidableEq K]
    (E : Finset (Fin n × Index)) (key : Index → K) (Q : ℕ)
    (H : HasUniformFibers E Q (fun e => key e.2))
    (mass cover U : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image key).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (v : K) (hv : v∈(E.image Prod.snd).image key) :
    mass≤(Q:ℝ)^2*cover*U*((E.filter (fun e => key e.2=v)).image Prod.snd).card := by
  let A := E.filter (fun e => key e.2=v)
  have hv' : v∈E.image (fun e => key e.2) := by
    simpa only [image_image,Function.comp_def] using hv
  have hAvg := (fiber_card_average_cross E (fun e => key e.2) (Q^2) H v hv').2
  have hAvgR : (E.card:ℝ)≤(Q:ℝ)^2*(A.card:ℝ)*
      (((E.image Prod.snd).image key).card:ℝ) := by
    simpa only [A,image_image,Function.comp_def,Nat.cast_mul,Nat.cast_pow] using
      (show (E.card:ℝ)≤((Q^2*(E.filter (fun e => key e.2=v)).card*
        (E.image (fun e => key e.2)).card:ℕ):ℝ) by exact_mod_cast hAvg)
  have hPoints := subset_card_le_point_cap E A (filter_subset _ _) U hDegree
  calc
    mass≤E.card := hMass
    _ ≤ (Q:ℝ)^2*(A.card:ℝ)*(((E.image Prod.snd).image key).card:ℝ) := hAvgR
    _ ≤ (Q:ℝ)^2*(A.card:ℝ)*cover :=
      mul_le_mul_of_nonneg_left hCover (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ ≤ (Q:ℝ)^2*(U*(A.image Prod.snd).card)*cover :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPoints (sq_nonneg _)) hCover0
    _ = _ := by ring

/-- The actual point-to-label capacity is the only extra cost needed to
convert the preceding LOWER to any literal fine-coordinate alphabet. -/
theorem occupied_class_label_lower {n : ℕ} {K Y : Type*}
    [DecidableEq K] [DecidableEq Y]
    (E : Finset (Fin n × Index)) (key : Index → K) (label : Index → Y) (Q : ℕ)
    (H : HasUniformFibers E Q (fun e => key e.2))
    (mass cover U capacity : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image key).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (v : K) (hv : v∈(E.image Prod.snd).image key)
    (hCapacity : ∀y∈((E.filter (fun e => key e.2=v)).image Prod.snd).image label,
      ((((E.filter (fun e => key e.2=v)).image Prod.snd).filter
        (fun k => label k=y)).card:ℝ)≤capacity) :
    mass≤(Q:ℝ)^2*cover*U*capacity*
      (((E.filter (fun e => key e.2=v)).image Prod.snd).image label).card := by
  let P := (E.filter (fun e => key e.2=v)).image Prod.snd
  have hCap : (P.card:ℝ)≤capacity*(P.image label).card := by
    have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
      P id label capacity (fun y hy => by simpa only [image_id'] using hCapacity y hy)
    simpa only [image_id'] using hh
  have hLower := occupied_class_point_lower E key Q H mass cover U hCover0 hU
    hMass hCover hDegree v hv
  calc
    mass≤(Q:ℝ)^2*cover*U*P.card := hLower
    _ ≤ (Q:ℝ)^2*cover*U*(capacity*(P.image label).card) :=
      mul_le_mul_of_nonneg_left hCap (mul_nonneg (mul_nonneg (sq_nonneg _) hCover0) hU)
    _ = _ := by ring

/-- Higher X density is derived on the actual output cells. -/
theorem dense_higher_X {n : ℕ} (E : Finset (Fin n × Index))
    (C F : ℤ → ℝ) (Q : ℕ)
    (H : HasUniformFibers E Q (fun e => higherKey C F e.2))
    (mass cover U : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image (higherKey C F)).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (v : ℤ × ℤ) (hv : v∈(E.image Prod.snd).image (higherKey C F)) :
    mass≤(Q:ℝ)^2*cover*U*
      (((E.filter (fun e => higherKey C F e.2=v)).image Prod.snd).image higherXIndex).card := by
  have hLower := occupied_class_point_lower E (higherKey C F) Q H mass cover U
    hCover0 hU hMass hCover hDegree v hv
  have hInj : Set.InjOn higherXIndex
      ↑((E.filter (fun e => higherKey C F e.2=v)).image Prod.snd) := by
    intro k hk l hl he
    obtain ⟨e,heE,rfl⟩ := mem_image.mp hk
    obtain ⟨f,hfE,rfl⟩ := mem_image.mp hl
    exact higher_coordinates_injective C F
      ((mem_filter.mp heE).2.trans (mem_filter.mp hfE).2.symm) he
  rw [card_image_iff.mpr hInj]
  exact hLower

/-- Every occupied higher-Y r-class contains many distinct fine higher-Y
labels. The only horizontal input is the GLOBAL trivial X packing upper. -/
theorem higher_Y_class_lower {n : ℕ} (E : Finset (Fin n × Index))
    (C F : ℤ → ℝ) (R Q : ℕ)
    (H : HasUniformFibers E Q (fun e => coarseHigherKey C F R e.2))
    (mass cover U Xcap : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image (coarseHigherKey C F R)).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (hXcap : (((E.image Prod.snd).image higherXIndex).card:ℝ)≤Xcap)
    (v : ℤ × ℤ) (hv : v∈(E.image Prod.snd).image (coarseHigherKey C F R)) :
    mass≤(Q:ℝ)^2*cover*U*Xcap*
      (((E.filter (fun e => coarseHigherKey C F R e.2=v)).image Prod.snd).image
        (higherYIndex C F)).card := by
  apply occupied_class_label_lower E (coarseHigherKey C F R) (higherYIndex C F) Q H
    mass cover U Xcap hCover0 hU hMass hCover hDegree v hv
  intro y _hy
  let P := (E.filter (fun e => coarseHigherKey C F R e.2=v)).image Prod.snd
  let W := P.filter (fun k => higherYIndex C F k=y)
  have hTime : ∀k∈P,k 3=v.1 := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := mem_image.mp hk
    exact congrArg Prod.fst (mem_filter.mp he).2
  have hKey : ∀k∈W,higherKey C F k=(v.1,y) := by
    intro k hk
    exact Prod.ext (hTime k (mem_filter.mp hk).1) (mem_filter.mp hk).2
  have hCard : (W.image higherXIndex).card=W.card := by
    apply card_image_iff.mpr
    intro k hk l hl he
    exact higher_coordinates_injective C F ((hKey k hk).trans (hKey l hl).symm) he
  have hSub : W⊆E.image Prod.snd :=
    (filter_subset _ _).trans (image_subset_image (filter_subset _ _))
  change (W.card:ℝ)≤Xcap
  rw [←hCard]
  exact (show ((W.image higherXIndex).card:ℝ)≤((E.image Prod.snd).image higherXIndex).card by
    exact_mod_cast card_le_card (image_subset_image hSub)).trans hXcap

end NativeActualHigherKeyPopulationDraft1955

end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit: Thm_StickyKakeya4_native_packed_higher_capacity_draft_2006.lean
   SHA256 b795b3585032664b0afbdec16e9cd99d6b4baf5aaccc7b1787a06d2266f0adaa -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativePackedHigherCapacityDraft2006
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeHigherQuotientParentTransport
open NativeLocalParentPhysicalMap NativeJointUniformCoarseRelations
open NativeActualHigherKeyPopulationDraft1955
open scoped BigOperators

def packedQuotient (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℝ) (x : E4) : ℝ :=
  higherY C F (O x)

def packedXKey (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (k : Index) : Fin 2 → ℤ :=
  fun j => ⌊O (cellCenter mu k) j.castSucc.castSucc/mu⌋

def packedYIndex (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) (k : Index) : ℤ :=
  ⌊packedQuotient O (C (k 3)) (F (k 3)) (cellCenter mu k)/mu⌋

def packedHigherKey (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) (k : Index) : ℤ × ℤ :=
  (k 3,packedYIndex mu O C F k)

def packedCoarseKey (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ)
    (R : ℕ) (k : Index) : ℤ × ℤ :=
  (k 3,packedYIndex mu O C F k/(R:ℤ))

lemma floor_equal_abs_le (mu : ℝ) (hmu : 0<mu) (x y : ℝ)
    (h : ⌊x/mu⌋=⌊y/mu⌋) : |x-y|≤mu := by
  have hx := NativeTangentGridCoarsening.coarse_floor_interval hmu (rfl : ⌊x/mu⌋=⌊x/mu⌋)
  have hy := NativeTangentGridCoarsening.coarse_floor_interval hmu h.symm
  exact abs_le.mpr ⟨by linarith only [hx.1,hx.2,hy.1,hy.2],
    by linarith only [hx.1,hx.2,hy.1,hy.2]⟩

/-- A fixed packed frame is evaluated, never applied to the native source.
Equal joint labels force a6mu diameter of the ORIGINAL native centers. -/
theorem same_joint_key_distance (mu : ℝ) (hmu : 0<mu)
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x 3=x 3)
    (C F : ℤ → ℝ) (k l : Index) (hC : |C (k 3)|≤1) (hF : |F (k 3)|≤1)
    (hY : packedHigherKey mu O C F k=packedHigherKey mu O C F l)
    (hX : packedXKey mu O k=packedXKey mu O l) :
    dist (cellCenter mu k) (cellCenter mu l)≤6*mu := by
  let x := O (cellCenter mu k)
  let y := O (cellCenter mu l)
  have ht : k 3=l 3 := congrArg Prod.fst hY
  have h0 : |x 0-y 0|≤mu := by
    apply floor_equal_abs_le mu hmu
    simpa only [packedXKey] using congrFun hX 0
  have h1 : |x 1-y 1|≤mu := by
    apply floor_equal_abs_le mu hmu
    simpa only [packedXKey] using congrFun hX 1
  have hq : |higherY (C (k 3)) (F (k 3)) x-
      higherY (C (k 3)) (F (k 3)) y|≤mu := by
    apply floor_equal_abs_le mu hmu
    have hh := congrArg Prod.snd hY
    change packedYIndex mu O C F k=packedYIndex mu O C F l at hh
    simpa only [packedYIndex,packedQuotient,ht] using hh
  have he : x 2-y 2=
      (higherY (C (k 3)) (F (k 3)) x-higherY (C (k 3)) (F (k 3)) y)+
      C (k 3)*(x 0-y 0)+F (k 3)*(x 1-y 1) := by
    unfold higherY
    ring
  have h2 : |x 2-y 2|≤3*mu := by
    rw [he]
    have hc := (mul_le_mul hC h0 (abs_nonneg _) zero_le_one)
    have hf := (mul_le_mul hF h1 (abs_nonneg _) zero_le_one)
    calc
      _ ≤ |higherY (C (k 3)) (F (k 3)) x-higherY (C (k 3)) (F (k 3)) y|+
          |C (k 3)|*|x 0-y 0|+|F (k 3)|*|x 1-y 1| := by
        have hh := abs_add_le
          ((higherY (C (k 3)) (F (k 3)) x-higherY (C (k 3)) (F (k 3)) y)+
            C (k 3)*(x 0-y 0)) (F (k 3)*(x 1-y 1))
        exact hh.trans (by
          rw [abs_mul]
          exact add_le_add_right (by simpa only [abs_mul] using
            abs_add_le (higherY (C (k 3)) (F (k 3)) x-higherY (C (k 3)) (F (k 3)) y)
              (C (k 3)*(x 0-y 0))) _)
      _ ≤ 3*mu := by nlinarith only [hq,hc,hf]
  have h3 : x 3=y 3 := by
    dsimp only [x,y]
    rw [hO,hO]
    change mu*((k 3:ℝ)+1/2)=mu*((l 3:ℝ)+1/2)
    rw [ht]
  have hcoords : ∀j : Fin 4,|x j-y j|≤3*mu := by
    intro j
    fin_cases j
    · linarith only [h0,hmu]
    · linarith only [h1,hmu]
    · exact h2
    · rw [h3,sub_self,abs_zero]
      positivity
  have hh := CanonicalConfiguredE4Bridge.dist_le_three_of_coordinate_error
    (2*mu) (by positivity) x y (fun j => by nlinarith only [hcoords j])
  have hd : dist x y≤6*mu := by nlinarith only [hh]
  simpa only [x,y,O.dist_map] using hd

/-- Native cubical packing supplies the bounded inverse capacity, even
though the packed-coordinate key is not injective on native cells. -/
theorem joint_native_cell_capacity (P : Finset Index) (mu : ℝ) (hmu : 0<mu)
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x 3=x 3)
    (C F : ℤ → ℝ) (hC : ∀k∈P,|C (k 3)|≤1) (hF : ∀k∈P,|F (k 3)|≤1)
    (v : ℤ × ℤ) (u : Fin 2 → ℤ) :
    (P.filter (fun k => packedHigherKey mu O C F k=v ∧ packedXKey mu O k=u)).card≤13^4 := by
  let W := P.filter (fun k => packedHigherKey mu O C F k=v ∧ packedXKey mu O k=u)
  change W.card≤13^4
  by_cases hW : W.Nonempty
  · obtain ⟨l,hl⟩ := hW
    have hsub : W⊆GridQuotientAD.box l 6 := by
      intro k hk
      obtain ⟨hkP,hkY,hkX⟩ := mem_filter.mp hk
      obtain ⟨_hlP,hlY,hlX⟩ := mem_filter.mp hl
      have hd := same_joint_key_distance mu hmu O hO C F k l (hC k hkP) (hF k hkP)
        (hkY.trans hlY.symm) (hkX.trans hlX.symm)
      apply NativeLiteralGridOverlap.close_centers_mem_box hmu k l 6
      apply (dist_pi_le_iff (by positivity : (0:ℝ)≤(6:ℕ)*mu)).mpr
      intro j
      have hh := (PiLp.dist_apply_le (cellCenter mu k) (cellCenter mu l) j).trans hd
      simpa only [NativeLiteralGridOverlap.center,cellCenter] using hh
    exact (card_le_card hsub).trans_eq (by rw [GridQuotientAD.box_card]; norm_num)
  · simp only [not_nonempty_iff_eq_empty.mp hW,card_empty,Nat.zero_le]

/-- The derived native-cell capacity, not a rotation of the source,
converts an occupied actual higher-Y class into dense packed higher X. -/
theorem packed_dense_X {n : ℕ} (E : Finset (Fin n × Index))
    (mu : ℝ) (hmu : 0<mu) (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x 3=x 3)
    (C F : ℤ → ℝ) (hC : ∀k∈E.image Prod.snd,|C (k 3)|≤1)
    (hF : ∀k∈E.image Prod.snd,|F (k 3)|≤1) (Q : ℕ)
    (H : HasUniformFibers E Q (fun e => packedHigherKey mu O C F e.2))
    (mass cover U : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image (packedHigherKey mu O C F)).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (v : ℤ × ℤ) (hv : v∈(E.image Prod.snd).image (packedHigherKey mu O C F)) :
    mass≤(Q:ℝ)^2*cover*U*(13^4:ℕ)*
      (((E.filter (fun e => packedHigherKey mu O C F e.2=v)).image Prod.snd).image
        (packedXKey mu O)).card := by
  apply occupied_class_label_lower E (packedHigherKey mu O C F) (packedXKey mu O) Q H
    mass cover U ((13^4:ℕ):ℝ) hCover0 hU hMass hCover hDegree v hv
  intro u _hu
  have hsub : ((E.filter (fun e => packedHigherKey mu O C F e.2=v)).image Prod.snd).filter
      (fun k => packedXKey mu O k=u) ⊆
      (E.image Prod.snd).filter (fun k => packedHigherKey mu O C F k=v ∧ packedXKey mu O k=u) := by
    intro k hk
    obtain ⟨hkP,hkX⟩ := mem_filter.mp hk
    obtain ⟨e,he,rfl⟩ := mem_image.mp hkP
    exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp he).1,(mem_filter.mp he).2,hkX⟩
  exact_mod_cast (card_le_card hsub).trans
    (joint_native_cell_capacity (E.image Prod.snd) mu hmu O hO C F hC hF v u)

/-- The same bounded inverse gives the desired fine-Y count in every
occupied coarse-Y class. Only global tangent-grid packing is an input. -/
theorem packed_Y_class_lower {n : ℕ} (E : Finset (Fin n × Index))
    (mu : ℝ) (hmu : 0<mu) (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4,O x 3=x 3)
    (C F : ℤ → ℝ) (hC : ∀k∈E.image Prod.snd,|C (k 3)|≤1)
    (hF : ∀k∈E.image Prod.snd,|F (k 3)|≤1) (R Q : ℕ)
    (H : HasUniformFibers E Q (fun e => packedCoarseKey mu O C F R e.2))
    (mass cover U Xcap : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image (packedCoarseKey mu O C F R)).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (hXcap : (((E.image Prod.snd).image (packedXKey mu O)).card:ℝ)≤Xcap)
    (v : ℤ × ℤ) (hv : v∈(E.image Prod.snd).image (packedCoarseKey mu O C F R)) :
    mass≤(Q:ℝ)^2*cover*U*((13^4:ℕ):ℝ)*Xcap*
      (((E.filter (fun e => packedCoarseKey mu O C F R e.2=v)).image Prod.snd).image
        (packedYIndex mu O C F)).card := by
  have hOut := occupied_class_label_lower E (packedCoarseKey mu O C F R)
    (packedYIndex mu O C F) Q H mass cover U (((13^4:ℕ):ℝ)*Xcap)
    hCover0 hU hMass hCover hDegree v hv
  have hCap : ∀y∈((E.filter (fun e => packedCoarseKey mu O C F R e.2=v)).image Prod.snd).image
      (packedYIndex mu O C F),
      ((((E.filter (fun e => packedCoarseKey mu O C F R e.2=v)).image Prod.snd).filter
        (fun k => packedYIndex mu O C F k=y)).card:ℝ)≤((13^4:ℕ):ℝ)*Xcap := by
    intro y _hy
    let P := (E.filter (fun e => packedCoarseKey mu O C F R e.2=v)).image Prod.snd
    let W := P.filter (fun k => packedYIndex mu O C F k=y)
    have hSub : W⊆E.image Prod.snd :=
      (filter_subset _ _).trans (image_subset_image (filter_subset _ _))
    have hKey : ∀k∈W,packedHigherKey mu O C F k=(v.1,y) := by
      intro k hk
      obtain ⟨hkP,hky⟩ := mem_filter.mp hk
      obtain ⟨e,he,rfl⟩ := mem_image.mp hkP
      exact Prod.ext (congrArg Prod.fst (mem_filter.mp he).2) hky
    have hEach : ∀u∈W.image (packedXKey mu O),
        (((W.filter (fun k => packedXKey mu O k=u)).image id).card:ℝ)≤((13^4:ℕ):ℝ) := by
      intro u _hu
      have hs : W.filter (fun k => packedXKey mu O k=u) ⊆
          (E.image Prod.snd).filter (fun k => packedHigherKey mu O C F k=(v.1,y) ∧
            packedXKey mu O k=u) := by
        intro k hk
        exact mem_filter.mpr ⟨hSub (mem_filter.mp hk).1,hKey k (mem_filter.mp hk).1,
          (mem_filter.mp hk).2⟩
      simpa only [image_id'] using
        (show ((W.filter (fun k => packedXKey mu O k=u)).card:ℝ)≤((13^4:ℕ):ℝ) by
          exact_mod_cast (card_le_card hs).trans
            (joint_native_cell_capacity (E.image Prod.snd) mu hmu O hO C F hC hF (v.1,y) u))
    have hPack := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
      W id (packedXKey mu O) ((13^4:ℕ):ℝ) hEach
    simp only [image_id'] at hPack
    have hX : ((W.image (packedXKey mu O)).card:ℝ)≤Xcap :=
      (show _≤(((E.image Prod.snd).image (packedXKey mu O)).card:ℝ) by
        exact_mod_cast card_le_card (image_subset_image hSub)).trans hXcap
    exact hPack.trans (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _))
  have hh := hOut hCap
  convert hh using 1 <;> ring

/-- Exact affine parent action on differences at one OLD physical height.
No value of a packed coordinate is identified with a native cell index. -/
theorem physical_difference_same_height {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : NativeOriginalParentSelection.Parent) (x y : E4)
    (ht : x 3=y 3) :
    physicalMap D a N p x-physicalMap D a N p y=horizontalScale N • (x-y) := by
  ext v
  refine Fin.lastCases ?_ (fun j => ?_) v
  · simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    rw [physical_height,physical_height,ht]
    ring
  · simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    rw [physical_coordinate,physical_coordinate,ht]
    unfold horizontalScale
    ring

lemma packedQuotient_sub (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℝ) (x y : E4) :
    packedQuotient O C F (x-y)=packedQuotient O C F x-packedQuotient O C F y := by
  simp only [packedQuotient,higherY,map_sub,PiLp.sub_apply]
  ring

lemma packedQuotient_smul (O : E4 ≃ₗᵢ[ℝ] E4) (C F t : ℝ) (x : E4) :
    packedQuotient O C F (t • x)=t*packedQuotient O C F x := by
  simp only [packedQuotient,higherY,map_smul,PiLp.smul_apply,smul_eq_mul]
  ring

def packedParentShift {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : NativeOriginalParentSelection.Parent) (O : E4 ≃ₗᵢ[ℝ] E4)
    (C F : ℝ) (anchor : E4) : ℝ :=
  packedQuotient O C F (physicalMap D a N p anchor)-horizontalScale N*packedQuotient O C F anchor

theorem packed_parent_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : NativeOriginalParentSelection.Parent) (O : E4 ≃ₗᵢ[ℝ] E4)
    (C F : ℝ) (x anchor : E4) (ht : x 3=anchor 3) :
    packedQuotient O C F (physicalMap D a N p x)=
      horizontalScale N*packedQuotient O C F x+packedParentShift D a N p O C F anchor := by
  have hh := congrArg (packedQuotient O C F) (physical_difference_same_height D a N p x anchor ht)
  rw [packedQuotient_sub,packedQuotient_smul,packedQuotient_sub] at hh
  unfold packedParentShift
  linarith only [hh]

theorem packed_quotient_motion (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℝ) (x y : E4) :
    |packedQuotient O C F x-packedQuotient O C F y|≤(1+|C|+|F|)*dist x y := by
  have hc (j : Fin 4) : |O x j-O y j|≤dist x y := by
    simpa only [Real.dist_eq,O.dist_map] using PiLp.dist_apply_le (O x) (O y) j
  have he : packedQuotient O C F x-packedQuotient O C F y=
      (O x 2-O y 2)-C*(O x 0-O y 0)-F*(O x 1-O y 1) := by
    unfold packedQuotient higherY
    ring
  rw [he]
  calc
    _ ≤ |O x 2-O y 2|+|C|*|O x 0-O y 0|+|F|*|O x 1-O y 1| := by
      have hh := abs_sub ((O x 2-O y 2)-C*(O x 0-O y 0)) (F*(O x 1-O y 1))
      exact hh.trans (by
        rw [abs_mul]
        exact add_le_add_right (by simpa only [abs_mul] using
          abs_sub (O x 2-O y 2) (C*(O x 0-O y 0))) _)
    _ ≤ dist x y+|C|*dist x y+|F|*dist x y :=
      add_le_add (add_le_add (hc 2) (mul_le_mul_of_nonneg_left (hc 0) (abs_nonneg C)))
        (mul_le_mul_of_nonneg_left (hc 1) (abs_nonneg F))
    _ = _ := by ring

/-- A genuine old scalar witness and the actual occurrence-to-cell halo
give an explicit scalar witness on the UNROTATED native output center.
The actual occurrence reader supplies hHalo with constant4. -/
theorem parent_scalar_witness {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : NativeOriginalParentSelection.Parent) (O : E4 ≃ₗᵢ[ℝ] E4)
    (C F : ℝ) (hC : |C|≤1) (hF : |F|≤1)
    (rho tau d sigma alpha y : ℝ) (hSigma : 0<sigma)
    (hd : d=8*rho) (hScale : sigma=(N:ℝ)*d/64)
    (hTau : horizontalScale N*tau=512)
    (x anchor : E4) (ht : x 3=anchor 3) (k : Index)
    (hOld : |packedQuotient O C F x-(tau*y+alpha)|≤2*rho)
    (hHalo : dist (cellCenter (sigma/2) k) (physicalMap D a N p x)≤4*sigma) :
    |packedQuotient O C F (cellCenter (sigma/2) k)-
      (512*y+(horizontalScale N*alpha+packedParentShift D a N p O C F anchor))|≤13*sigma := by
  let z := cellCenter (sigma/2) k
  let q := physicalMap D a N p x
  have hCost : 1+|C|+|F|≤3 := by linarith only [hC,hF]
  have hMove : |packedQuotient O C F z-packedQuotient O C F q|≤12*sigma := by
    have hh := packed_quotient_motion O C F z q
    have hnon : 0≤1+|C|+|F| := by positivity
    have hu := mul_le_mul_of_nonneg_left hHalo hnon
    have hc := mul_le_mul_of_nonneg_right hCost (show 0≤4*sigma by positivity)
    nlinarith only [hh,hu,hc]
  have hOldScaled : horizontalScale N*(2*rho)=sigma/32 := by
    rw [hScale,hd]
    unfold horizontalScale
    ring
  have hRead := packed_parent_readback D a N p O C F x anchor ht
  have he : packedQuotient O C F q-
      (512*y+(horizontalScale N*alpha+packedParentShift D a N p O C F anchor))=
      horizontalScale N*(packedQuotient O C F x-(tau*y+alpha)) := by
    dsimp only [q]
    rw [hRead]
    have hh := congrArg (fun z : ℝ => z*y) hTau
    nlinarith only [hh]
  have hWitness : |packedQuotient O C F q-
      (512*y+(horizontalScale N*alpha+packedParentShift D a N p O C F anchor))|≤sigma/32 := by
    rw [he,abs_mul,abs_of_nonneg (horizontalScale_nonneg N),←hOldScaled]
    exact mul_le_mul_of_nonneg_left hOld (horizontalScale_nonneg N)
  have hTri := abs_sub_le (packedQuotient O C F z) (packedQuotient O C F q)
    (512*y+(horizontalScale N*alpha+packedParentShift D a N p O C F anchor))
  change |packedQuotient O C F z-_ |≤13*sigma
  linarith only [hTri,hMove,hWitness,hSigma]

/-- The first planar output supplies one FULL scalar Y and a common slope,
with one-sided witnesses for every original point in the aligned patch.
Its scalar mesh is e=rho/tau; no deltaY/rho mesh is introduced. -/
theorem nearly_aligned_scalar_witnesses
    (A : Finset (Fin 2 → ℝ)) (e t s K : ℝ)
    (H : NativeLiteralAlignedSet.NearlyLiteralAligned A e t s K) :
    ∃(theta : ℝ) (Y : Finset ℝ),|theta|≤1 ∧ Y.Nonempty ∧
      (∀y∈Y,|y|≤1) ∧ FiniteVoronoiRealADCoarsening.ADBounds Y e K (t-s) ∧
      ∀p∈A,∃y∈Y,|p 1-theta*p 0-y|≤2*e := by
  obtain ⟨P,hP,hNear,_hBack⟩ := H.aligned
  obtain ⟨theta,Y,X,hTheta,hYn,hYbox,hYAD,_hX,hGraph⟩ := hP.fibers
  refine ⟨theta,Y,hTheta,hYn,hYbox,hYAD,?_⟩
  intro p hp
  obtain ⟨q,hq,hpq⟩ := hNear p hp
  rw [hGraph] at hq
  obtain ⟨y,hy,hq⟩ := mem_biUnion.mp hq
  obtain ⟨x,_hx,rfl⟩ := mem_image.mp hq
  have h0 : |p 0-x|≤e := by
    simpa only [Matrix.cons_val_zero] using
      (EuclideanAlignmentPatches.coordinate_dist_le p ![x,theta*x+(y:ℝ)] 0).trans hpq.le
  have h1 : |p 1-(theta*x+(y:ℝ))|≤e := by
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using
      (EuclideanAlignmentPatches.coordinate_dist_le p ![x,theta*x+(y:ℝ)] 1).trans hpq.le
  refine ⟨y.val,y.property,?_⟩
  have he : p 1-theta*p 0-y.val=(p 1-(theta*x+y.val))-theta*(p 0-x) := by ring
  rw [he]
  have hh := abs_sub (p 1-(theta*x+y.val)) (theta*(p 0-x))
  rw [abs_mul] at hh
  have hm := mul_le_mul hTheta h0 (abs_nonneg _) zero_le_one
  nlinarith only [hh,h1,hm]

/-- The actual lower quotient of a configured point, in the fixed common
planar chart and the literal first5.3 normalization. -/
def normalizedLowerQuotient (p : E4) (A B : ℝ)
    (anchor : Fin 2 → ℝ) (tau : ℝ) : Fin 2 → ℝ :=
  ![(p 1-A*p 0-anchor 0)/tau,(p 2-B*p 0-anchor 1)/tau]

lemma normalized_lower_identity (p : E4) (A B theta : ℝ)
    (anchor : Fin 2 → ℝ) (tau : ℝ) (hTau : tau≠0) :
    higherY (B-theta*A) theta p=
      tau*(normalizedLowerQuotient p A B anchor tau 1-
        theta*normalizedLowerQuotient p A B anchor tau 0)+(anchor 1-theta*anchor 0) := by
  simp only [higherY,normalizedLowerQuotient,Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [hTau]
  <;> ring

/-- Fixed-old-height source-facing reduction. P is a set of literal native
output cell indices, cfg k is its chosen ORIGINAL configured witness, and
hHalo is exactly the conclusion supplied by occurrence_center_near.
The common planar patch is genuine NearlyLiteralAligned data; the scalar
witness/error, common slope, normal coefficient and affine translation are
all derived. No upper/lower property of the selected output Y is assumed. -/
theorem first_aligned_native_scalar_witness {n : ℕ}
    (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : NativeOriginalParentSelection.Parent) (O : E4 ≃ₗᵢ[ℝ] E4)
    (P : Finset Index) (cfg : Index → E4) (physicalAnchor : E4)
    (A B : ℝ) (hA : |A|≤1/4) (hB : |B|≤1/4)
    (planarAnchor : Fin 2 → ℝ) (rho tau d sigma t s K : ℝ)
    (hTau0 : 0<tau) (hSigma : 0<sigma)
    (hd : d=8*rho) (hScale : sigma=(N:ℝ)*d/64)
    (hTau : horizontalScale N*tau=512)
    (Patch : Finset (Fin 2 → ℝ))
    (H : NativeLiteralAlignedSet.NearlyLiteralAligned Patch (rho/tau) t s K)
    (hPatch : ∀k∈P,normalizedLowerQuotient (cfg k) A B planarAnchor tau∈Patch)
    (hHeight : ∀k∈P,(O.symm (cfg k)) 3=physicalAnchor 3)
    (hHalo : ∀k∈P,dist (cellCenter (sigma/2) k)
      (physicalMap D a N p (O.symm (cfg k)))≤4*sigma) :
    ∃(theta : ℝ) (Y : Finset ℝ) (beta : ℝ),
      |theta|≤1 ∧ |B-theta*A|≤1/2 ∧ Y.Nonempty ∧
      (∀y∈Y,|y|≤1) ∧
      FiniteVoronoiRealADCoarsening.ADBounds Y (rho/tau) K (t-s) ∧
      beta=horizontalScale N*(planarAnchor 1-theta*planarAnchor 0)+
        packedParentShift D a N p O (B-theta*A) theta physicalAnchor ∧
      ∀k∈P,∃y∈Y,
        |packedQuotient O (B-theta*A) theta (cellCenter (sigma/2) k)-(512*y+beta)|≤13*sigma := by
  obtain ⟨theta,Y,hTheta,hYn,hYbox,hYAD,hWitness⟩ :=
    nearly_aligned_scalar_witnesses Patch (rho/tau) t s K H
  have hC : |B-theta*A|≤1/2 := by
    have hh := abs_sub B (theta*A)
    rw [abs_mul] at hh
    have hm := mul_le_mul hTheta hA (abs_nonneg A) zero_le_one
    linarith only [hh,hm,hB]
  let alpha := planarAnchor 1-theta*planarAnchor 0
  let beta := horizontalScale N*alpha+packedParentShift D a N p O (B-theta*A) theta physicalAnchor
  refine ⟨theta,Y,beta,hTheta,hC,hYn,hYbox,hYAD,rfl,?_⟩
  intro k hk
  obtain ⟨y,hy,he⟩ := hWitness (normalizedLowerQuotient (cfg k) A B planarAnchor tau) (hPatch k hk)
  have hOriginal : |higherY (B-theta*A) theta (cfg k)-(tau*y+alpha)|≤2*rho := by
    rw [normalized_lower_identity (cfg k) A B theta planarAnchor tau hTau0.ne']
    have hid : tau*(normalizedLowerQuotient (cfg k) A B planarAnchor tau 1-
        theta*normalizedLowerQuotient (cfg k) A B planarAnchor tau 0)+
        (planarAnchor 1-theta*planarAnchor 0)-(tau*y+alpha)=
      tau*(normalizedLowerQuotient (cfg k) A B planarAnchor tau 1-
        theta*normalizedLowerQuotient (cfg k) A B planarAnchor tau 0-y) := by
      dsimp only [alpha]
      ring
    rw [hid,abs_mul,abs_of_pos hTau0]
    have hh := mul_le_mul_of_nonneg_left he hTau0.le
    have hcancel : tau*(2*(rho/tau))=2*rho := by
      field_simp [hTau0.ne']
      <;> ring
    exact hh.trans_eq hcancel
  have hOld : |packedQuotient O (B-theta*A) theta (O.symm (cfg k))-(tau*y+alpha)|≤2*rho := by
    simpa only [packedQuotient,LinearIsometryEquiv.apply_symm_apply] using hOriginal
  refine ⟨y,hy,?_⟩
  exact parent_scalar_witness D a N p O (B-theta*A) theta (hC.trans (by norm_num)) hTheta
    rho tau d sigma alpha y hSigma hd hScale hTau (O.symm (cfg k)) physicalAnchor (hHeight k hk)
    k hOld (hHalo k hk)

end NativePackedHigherCapacityDraft2006

end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit: Thm_StickyKakeya4_native_full_Y_halo_cover_draft_2017.lean
   SHA256 f661015897bfc674d651d9626158f97bf1d06153428252223ea9ad16be1ad5f2 -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeFullYHaloCoverDraft2017
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeLiteralGridOverlap NativeRecodedGridUpper
open scoped BigOperators

lemma scalar_unit_interval_count (Y S : Finset ℝ) (hSY : S⊆Y)
    (e K alpha a : ℝ) (he : 0<e) (he1 : e≤1) (hK : 0<K)
    (H : ADBounds Y e K alpha) (hS : ∀y∈S,a≤y ∧ y≤a+1) :
    (S.card:ℝ)≤K*e^(-alpha) := by
  by_cases hSn : S.Nonempty
  · obtain ⟨c,hc⟩ := hSn
    have hsub : S⊆carrierBall Y c 1 := by
      intro y hy
      apply (mem_carrierBall Y y c 1).mpr
      refine ⟨hSY hy,?_⟩
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith only [(hS y hy).1,(hS y hy).2,(hS c hc).1,(hS c hc).2],
        by linarith only [(hS y hy).1,(hS y hy).2,(hS c hc).1,(hS c hc).2]⟩
    have hu := (H c (hSY hc) 1 he1 le_rfl).2
    have hid : (1/e)^alpha=e^(-alpha) := by
      rw [Real.div_rpow (by norm_num) he.le,Real.one_rpow,Real.rpow_neg he.le,one_div]
    exact (show (S.card:ℝ)≤(carrierBall Y c 1).card by exact_mod_cast card_le_card hsub).trans
      (by simpa only [hid] using hu)
  · rw [not_nonempty_iff_eq_empty.mp hSn,card_empty,Nat.cast_zero]
    exact mul_nonneg hK.le (Real.rpow_nonneg he.le _)

/-- LiteralAligned supplies |y|<=1, not a silently strengthened unit
diameter hypothesis. Two genuine unit intervals give the global count. -/
theorem full_scalar_global_count (Y : Finset ℝ) (e K alpha : ℝ)
    (he : 0<e) (he1 : e≤1) (hK : 0<K)
    (H : ADBounds Y e K alpha) (hY : ∀y∈Y,|y|≤1) :
    (Y.card:ℝ)≤2*K*e^(-alpha) := by
  let L := Y.filter (fun y => y≤0)
  let R := Y.filter (fun y => 0≤y)
  have hcover : Y⊆L∪R := by
    intro y hy
    rcases le_total y 0 with h | h
    · exact mem_union_left R (mem_filter.mpr ⟨hy,h⟩)
    · exact mem_union_right L (mem_filter.mpr ⟨hy,h⟩)
  have hL := scalar_unit_interval_count Y L (filter_subset _ _) e K alpha (-1) he he1 hK H
    (fun y hy => by
      have hb := abs_le.mp (hY y (mem_filter.mp hy).1)
      exact ⟨hb.1,by simpa using (mem_filter.mp hy).2⟩)
  have hR := scalar_unit_interval_count Y R (filter_subset _ _) e K alpha 0 he he1 hK H
    (fun y hy => by
      have hb := abs_le.mp (hY y (mem_filter.mp hy).1)
      exact ⟨(mem_filter.mp hy).2,by simpa using hb.2⟩)
  have hc : (Y.card:ℝ)≤(L.card:ℝ)+R.card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le L R)
  linarith only [hc,hL,hR]

lemma weaken_AD (Y : Finset ℝ) (e K L alpha : ℝ) (he : 0<e)
    (hK : 0<K) (hKL : K≤L) (H : ADBounds Y e K alpha) : ADBounds Y e L alpha := by
  intro y hy r hr hr1
  have hh := H y hy r hr hr1
  have hp : 0≤(r/e)^alpha := Real.rpow_nonneg (div_nonneg (he.le.trans hr) he.le) _
  exact ⟨(div_le_div_of_nonneg_left hp hK hKL).trans hh.1,
    hh.2.trans (mul_le_mul_of_nonneg_right hKL hp)⟩

def shiftedScalar (b : ℝ) : ℝ ≃ᵢ (Fin 1 → ℝ) where
  toFun := fun y _ => y+b
  invFun := fun x => x 0-b
  left_inv := by intro y; simp
  right_inv := by
    intro x
    funext j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp
  isometry_toFun := Isometry.of_dist_eq (by
    intro x y
    rw [dist_pi_const,Real.dist_eq,Real.dist_eq]
    congr 1
    ring)

def scalarGrid {X : Type*} (P : Finset X) (q : X → ℝ) (r : ℝ) : Finset (Fin 1 → ℤ) :=
  P.image (fun p _ => ⌊q p/r⌋)

lemma midpoint_error (r : ℝ) (hr : 0<r) (x : ℝ) :
    |r*((⌊x/r⌋:ℝ)+1/2)-x|≤r/2 := by
  have hl := (le_div_iff₀ hr).mp (Int.floor_le (x/r))
  have hu := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (x/r))
  exact abs_le.mpr ⟨by nlinarith only [hl,hu],by nlinarith only [hl,hu]⟩

/-- The actual normal-grid labels obtain witnesses in a translated copy
of FULL Y at the literal inverse physical scale. -/
theorem inverse_grid_witness {X : Type*} (P : Finset X) (q : X → ℝ) (Y : Finset ℝ)
    (sigma r beta : ℝ) (hSigma : 0<sigma) (hr : sigma/2≤r)
    (H : ∀p∈P,∃y∈Y,|q p-(512*y+beta)|≤13*sigma) :
    ∀k∈scalarGrid P q r,∃a∈Y.image (shiftedScalar (beta/512)),
      dist (center (r/512) k) a≤27*(r/512) := by
  have hr0 : 0<r := (half_pos hSigma).trans_le hr
  intro k hk
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
  obtain ⟨y,hy,hclose⟩ := H p hp
  refine ⟨shiftedScalar (beta/512) y,mem_image_of_mem _ hy,?_⟩
  apply (dist_pi_le_iff (by positivity : (0:ℝ)≤27*(r/512))).mpr
  intro j
  rw [Real.dist_eq]
  change |(r/512)*((⌊q p/r⌋:ℝ)+1/2)-(y+beta/512)|≤27*(r/512)
  have hm := midpoint_error r hr0 (q p)
  have ht := abs_sub_le (r*((⌊q p/r⌋:ℝ)+1/2)) (q p) (512*y+beta)
  have hh : |r*((⌊q p/r⌋:ℝ)+1/2)-(512*y+beta)|≤27*r := by
    nlinarith only [hm,ht,hclose,hr]
  have he : (r/512)*((⌊q p/r⌋:ℝ)+1/2)-(y+beta/512)=
      (r*((⌊q p/r⌋:ℝ)+1/2)-(512*y+beta))/512 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤512)).trans_eq (by ring)

/-- Global version of the existing grid-ball double count. Full-reference
AD lower mass and actual grid overlap give the entire occupied cover upper. -/
theorem global_grid_upper {l : ℕ} (A : Finset (Fin l → ℝ)) (B : Finset (Fin l → ℤ))
    (witness : (Fin l → ℤ) → (Fin l → ℝ)) (N : ℕ)
    (e r K alpha : ℝ) (he : 0<e) (her : e≤r) (hr1 : r≤1) (hK : 0<K)
    (H : ADBounds A e K alpha) (hGlobal : e^alpha*(A.card:ℝ)≤K)
    (hMem : ∀k∈B,witness k∈A)
    (hClose : ∀k∈B,dist (center r k) (witness k)≤(N:ℝ)*r) :
    (B.card:ℝ)≤(((4*N+5)^l:ℕ):ℝ)*K^2*r^(-alpha) := by
  have hr : 0<r := he.trans_le her
  have hScaled := scaled_bounds_of_ADBounds he hK H
  let M : ℝ := (((4*N+5)^l:ℕ):ℝ)
  have hM : 0≤M := Nat.cast_nonneg _
  have hRows : (B.card:ℝ)*r^alpha≤K*e^alpha*
      ∑k∈B,((A.filter (fun a => dist a (witness k)≤r)).card:ℝ) := by
    calc
      _ = ∑_k∈B,r^alpha := by simp
      _ ≤ ∑k∈B,K*e^alpha*((A.filter (fun a => dist a (witness k)≤r)).card:ℝ) := by
        apply sum_le_sum
        intro k hk
        exact (hScaled (witness k) (hMem k hk) r her hr1).1
      _ = _ := by rw [mul_sum]
  have hCols : ∀a∈A,((B.filter (fun k => dist a (witness k)≤r)).card:ℝ)≤M := by
    intro a _ha
    have hsub : B.filter (fun k => dist a (witness k)≤r) ⊆
        B.filter (fun k => dist (center r k) a≤((N+1:ℕ):ℝ)*r) := by
      intro k hk
      obtain ⟨hkB,hka⟩ := mem_filter.mp hk
      have ht := dist_triangle (center r k) (witness k) a
      have hc := hClose k hkB
      rw [dist_comm (witness k) a] at ht
      apply mem_filter.mpr ⟨hkB,?_⟩
      push_cast
      nlinarith only [ht,hc,hka]
    have hh := (card_le_card hsub).trans (grid_ball_card_le B hr a (N+1))
    dsimp only [M]
    have hid : 4*(N+1)+1=4*N+5 := by omega
    simpa only [hid] using
      (show ((B.filter (fun k => dist a (witness k)≤r)).card:ℝ)≤
        (((4*(N+1)+1)^l:ℕ):ℝ) by exact_mod_cast hh)
  rw [NativeRecodedGridUpper.incidence_sum_swap] at hRows
  have hSum : (∑a∈A,((B.filter (fun k => dist a (witness k)≤r)).card:ℝ))≤(A.card:ℝ)*M := by
    calc
      _ ≤ ∑_a∈A,M := sum_le_sum hCols
      _ = _ := by simp
  have hTotal : (B.card:ℝ)*r^alpha≤M*K^2 := by
    calc
      _ ≤ K*e^alpha*((A.card:ℝ)*M) := hRows.trans
        (mul_le_mul_of_nonneg_left hSum (mul_nonneg hK.le (Real.rpow_nonneg he.le _)))
      _ = M*K*(e^alpha*(A.card:ℝ)) := by ring
      _ ≤ M*K*K := mul_le_mul_of_nonneg_left hGlobal (mul_nonneg hM hK.le)
      _ = _ := by ring
  rw [Real.rpow_neg hr.le]
  have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hr alpha)).mpr hTotal
  simpa only [div_eq_mul_inv] using hh

/-- Full scalar bounds, translation and the13sigma actual-source halo
produce global and local occupied normal-grid uppers. Radius R is in
inverse-physical units in the local conclusion; it is later set to rOut/512. -/
theorem scalar_halo_grid_upper {X : Type*} (P : Finset X) (q : X → ℝ) (Y : Finset ℝ)
    (sigma e r beta K alpha : ℝ) (hSigma : 0<sigma) (heq : e=sigma/32768)
    (hr : sigma/2≤r) (hr1 : r≤1) (hK : 1≤K) (hAlpha : 0≤alpha)
    (H : ADBounds Y e K alpha) (hY : ∀y∈Y,|y|≤1)
    (hNear : ∀p∈P,∃y∈Y,|q p-(512*y+beta)|≤13*sigma) :
    ((scalarGrid P q r).card:ℝ)≤452*K^2*(r/512)^(-alpha) ∧
    ∀(x : Fin 1 → ℝ) (R : ℝ),r/512≤R → R≤1 →
      (((scalarGrid P q r).filter (fun k => dist (center (r/512) k) x≤R)).card:ℝ)≤
        452*K^2*58^alpha*(R/(r/512))^alpha := by
  have he : 0<e := by rw [heq]; positivity
  have hr0 : 0<r := (half_pos hSigma).trans_le hr
  have her : e≤r/512 := by rw [heq]; linarith only [hr,hSigma]
  have hr512 : r/512≤1 := by linarith only [hr1]
  have he1 : e≤1 := her.trans hr512
  have hK0 : 0<K := lt_of_lt_of_le zero_lt_one hK
  have h2K : 1≤2*K := by linarith only [hK]
  let A := Y.image (shiftedScalar (beta/512))
  let B := scalarGrid P q r
  have hYad : ADBounds Y e (2*K) alpha := weaken_AD Y e K (2*K) alpha he hK0 (by linarith) H
  have hAad : ADBounds A e (2*K) alpha :=
    OriginalRepresentativeGridComparison.point_AD_isometric_image (shiftedScalar (beta/512)) Y hYad
  have hGlobal : (A.card:ℝ)≤(2*K)*e^(-alpha) := by
    rw [card_image_of_injective _ (shiftedScalar (beta/512)).injective]
    exact full_scalar_global_count Y e K alpha he he1 hK0 H hY
  have hScaledGlobal : e^alpha*(A.card:ℝ)≤2*K := by
    have hh := mul_le_mul_of_nonneg_left hGlobal (Real.rpow_nonneg he.le alpha)
    have hc : e^alpha*e^(-alpha)=1 := by rw [←Real.rpow_add he,add_neg_cancel,Real.rpow_zero]
    calc
      _ ≤ e^alpha*((2*K)*e^(-alpha)) := hh
      _ = (2*K)*(e^alpha*e^(-alpha)) := by ring
      _ = _ := by rw [hc,mul_one]
  have hN := inverse_grid_witness P q Y sigma r beta hSigma hr hNear
  let witness : (Fin 1 → ℤ) → (Fin 1 → ℝ) := fun k =>
    if hk : k∈B then Classical.choose (hN k hk) else 0
  have hMem : ∀k∈B,witness k∈A := by
    intro k hk
    simp only [witness,dif_pos hk]
    exact (Classical.choose_spec (hN k hk)).1
  have hClose : ∀k∈B,dist (center (r/512) k) (witness k)≤(27:ℕ)*(r/512) := by
    intro k hk
    simp only [witness,dif_pos hk]
    exact (Classical.choose_spec (hN k hk)).2
  constructor
  · have hh := global_grid_upper A B witness 27 e (r/512) (2*K) alpha he her hr512
      (by positivity) hAad hScaledGlobal hMem hClose
    convert hh using 1 <;> norm_num <;> ring
  · intro x R hR hR1
    have hh := grid_ball_upper_of_witnesses A B witness 27 he her h2K hAlpha hAad hGlobal
      hMem hClose x R hR hR1
    convert hh using 1 <;> norm_num <;> ring

/-- The actual HeightAlignment exponent range supplies these hypotheses:
0<=kappa<=1 and0<=s<=1. The extra exponent is charged at native sigma. -/
theorem exponent_range_and_charge (kappa s sigma r : ℝ)
    (hk0 : 0≤kappa) (hk1 : kappa≤1) (hs0 : 0≤s) (hs1 : s≤1)
    (hSigma : 0<sigma) (hr : sigma≤r) :
    0≤2-kappa-s ∧ 2-kappa-s≤2 ∧
      (512:ℝ)^(2-kappa-s)≤512^2 ∧
      r^(-(2-kappa-s))≤sigma^(-(1-s))*r^(-(1-kappa)) := by
  have ha0 : 0≤2-kappa-s := by linarith only [hk1,hs1]
  have ha2 : 2-kappa-s≤2 := by linarith only [hk0,hs0]
  have hr0 : 0<r := hSigma.trans_le hr
  refine ⟨ha0,ha2,?_,?_⟩
  · have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤512) ha2
    norm_num at hh ⊢
    exact hh
  · have hsplit : -(2-kappa-s)=-(1-kappa)+(-(1-s)) := by ring
    rw [hsplit,Real.rpow_add hr0]
    have hh := Real.rpow_le_rpow_of_nonpos hSigma hr (by linarith only [hs1] : -(1-s)≤0)
    exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr0.le _)).trans_eq (by ring)

end NativeFullYHaloCoverDraft2017

end -- explicit anonymous noncomputable source-unit section

/- Source-facing endpoint: original planar output -> actual unrotated native
scalar cover. The four-sigma halo is the actual occurrence reader's output;
normalizedLowerQuotient is the literal configured-point readback. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeActualHigherTransferConstructionDraft2020
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeHigherQuotientParentTransport
open NativeLocalParentPhysicalMap NativePackedHigherCapacityDraft2006
open NativeFullYHaloCoverDraft2017 NativeLiteralGridOverlap

/-- Exact connection between the installed integer coarse key and the
actual scalar grid used by the full-Y halo-cover theorem. -/
theorem packed_coarse_scalar_readback (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4)
    (C F : ℤ → ℝ) (R : ℕ) (k : Index) :
    ⌊packedQuotient O (C (k 3)) (F (k 3)) (cellCenter mu k)/(mu*(R:ℝ))⌋=
      packedYIndex mu O C F k/(R:ℤ) := by
  rw [div_mul_eq_div_div,Int.floor_div_natCast]
  rfl

theorem first_aligned_native_Y_cover {n : ℕ}
    (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : NativeOriginalParentSelection.Parent) (O : E4 ≃ₗᵢ[ℝ] E4)
    (P : Finset Index) (cfg : Index → E4) (physicalAnchor : E4)
    (A B : ℝ) (hA : |A|≤1/4) (hB : |B|≤1/4)
    (planarAnchor : Fin 2 → ℝ) (rho tau d sigma kappa s K : ℝ)
    (hTau0 : 0<tau) (hSigma : 0<sigma)
    (hd : d=8*rho) (hScale : sigma=(N:ℝ)*d/64)
    (hTau : horizontalScale N*tau=512)
    (hk0 : 0≤kappa) (hk1 : kappa≤1) (hs0 : 0≤s) (hs1 : s≤1) (hK : 1≤K)
    (Patch : Finset (Fin 2 → ℝ))
    (H : NativeLiteralAlignedSet.NearlyLiteralAligned Patch (rho/tau) (2-kappa) s K)
    (hPatch : ∀k∈P,normalizedLowerQuotient (cfg k) A B planarAnchor tau∈Patch)
    (hHeight : ∀k∈P,(O.symm (cfg k)) 3=physicalAnchor 3)
    (hHalo : ∀k∈P,dist (cellCenter (sigma/2) k)
      (physicalMap D a N p (O.symm (cfg k)))≤4*sigma) :
    ∃(theta : ℝ) (Y : Finset ℝ) (beta : ℝ),
      |theta|≤1 ∧ |B-theta*A|≤1/2 ∧ Y.Nonempty ∧
      (∀y∈Y,|y|≤1) ∧
      FiniteVoronoiRealADCoarsening.ADBounds Y (rho/tau) K (2-kappa-s) ∧
      (∀k∈P,∃y∈Y,
        |packedQuotient O (B-theta*A) theta (cellCenter (sigma/2) k)-(512*y+beta)|≤13*sigma) ∧
      ∀r : ℝ,sigma/2≤r → r≤1 →
        let q := fun k : Index => packedQuotient O (B-theta*A) theta (cellCenter (sigma/2) k)
        ((scalarGrid P q r).card:ℝ)≤452*K^2*(r/512)^(-(2-kappa-s)) ∧
        ∀(x : Fin 1 → ℝ) (R : ℝ),r/512≤R → R≤1 →
          (((scalarGrid P q r).filter (fun k => dist (center (r/512) k) x≤R)).card:ℝ)≤
            452*K^2*58^(2-kappa-s)*(R/(r/512))^(2-kappa-s) := by
  obtain ⟨theta,Y,beta,hTheta,hC,hYn,hYbox,hYAD,_hBeta,hWitness⟩ :=
    first_aligned_native_scalar_witness D a N p O P cfg physicalAnchor A B hA hB planarAnchor
      rho tau d sigma (2-kappa) s K hTau0 hSigma hd hScale hTau Patch H hPatch hHeight hHalo
  have hN : (N:ℝ)*tau=262144 := by
    unfold horizontalScale at hTau
    nlinarith only [hTau]
  have heq : rho/tau=sigma/32768 := by
    apply (div_eq_iff hTau0.ne').mpr
    rw [hScale,hd]
    have hh := congrArg (fun z : ℝ => z*rho) hN
    nlinarith only [hh]
  have hAlpha : 0≤2-kappa-s := by linarith only [hk1,hs1]
  refine ⟨theta,Y,beta,hTheta,hC,hYn,hYbox,hYAD,hWitness,?_⟩
  intro r hr hr1
  exact scalar_halo_grid_upper P
    (fun k : Index => packedQuotient O (B-theta*A) theta (cellCenter (sigma/2) k))
    Y sigma (rho/tau) r beta K (2-kappa-s) hSigma heq hr hr1 hK hAlpha hYAD hYbox hWitness

end NativeActualHigherTransferConstructionDraft2020
end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit Thm_StickyKakeya4_native_configured_lower_quotient_readback.lean
   SHA256 d4b42067665eeef0a3d87b7e0b86f5872ea9e3c34555cd7827ff68b967e635c5 -/

/- UNVERIFIED actual configured lower-quotient readback. The height in
coarseYKey remains its coarse integer height; it is not the old translated
height. No field regularity, field freeze, or alignment-ball input is used. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeConfiguredLowerQuotientReadback
open Classical StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge CanonicalGridRecoding
open NativeActualConfiguredPoint NativeConfiguredThirdRelation NativeReferenceXYGridPoints
open CanonicalConfiguredPointRounding NativeTranslatedGrainHeightOverlap
open scoped BigOperators

/-- The literal rank-two quotient in the already packed E4 chart. -/
def lowerQuotient (F : Matrix (Fin 2) (Fin 1) ℝ) (x : E4) : Fin 2 → ℝ :=
  fun j => x j.castSucc.succ-F j 0*x 0

/-- Exact cancellation in the configured graph, including its physical
/512 contraction and the actual recoded normal key. -/
theorem graphGrid_quotient (mu : ℝ) (R : ℕ)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (z : Label ℤ 1 2) :
    lowerQuotient (Fcfg (z.1/((8*R:ℕ):ℤ))) (graphGrid .oneTwo mu R F Fcfg z) =
      NativeQuotientGridCenters.center (mu*(R:ℝ)/512)
        (newY mu R (fun t : ℤ => t/((8*R:ℕ):ℤ)) F Fcfg z).2 := by
  funext j
  fin_cases j <;>
    simp [lowerQuotient,graphGrid,assemble,configuredNormal,graphPoint,
      NativeQuotientGridCenters.center,CanonicalGridRecoding.center,newY,errorMatrix] <;> ring

/-- The actual source key's first coordinate is precisely the coarse
translated-height label. The converse needs the separately supplied Hsingle. -/
lemma coarse_height_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (p : Parent) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P=1) (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (R : ℕ) (k : Index) :
    (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).1 =
      translatedHeight D a m k/((8*R:ℕ):ℤ) := by
  simp only [coarseYKey,newY,sourceLabel_height]

/-- This is exactly the Y point passed to the first planar alignment. -/
theorem point_quotient_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (p : Parent) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P=1) (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (R : ℕ) (k : Index) :
    lowerQuotient (Fcfg (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).1)
        (point D a m p .oneTwo P hP hd F Fcfg R k) =
      NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).2 :=
  graphGrid_quotient (mu m) R F Fcfg (sourceLabel D a m p .oneTwo P hP hd F k)

/-- One tangent coordinate and the actual matrix entry bound give the
5/4 Lipschitz constant from E4 to the planar sup metric. -/
theorem lowerQuotient_dist (F : Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀j,|F j 0| ≤ 1/4) (x y : E4) :
    dist (lowerQuotient F x) (lowerQuotient F y) ≤ (5/4:ℝ)*dist x y := by
  apply (dist_pi_le_iff (by positivity : (0:ℝ) ≤ (5/4:ℝ)*dist x y)).mpr
  intro j
  have hn : |x j.castSucc.succ-y j.castSucc.succ| ≤ dist x y := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x y j.castSucc.succ
  have hx : |x 0-y 0| ≤ dist x y := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x y (0:Fin 4)
  have he : lowerQuotient F x j-lowerQuotient F y j =
      (x j.castSucc.succ-y j.castSucc.succ)-F j 0*(x 0-y 0) := by
    dsimp only [lowerQuotient]
    ring
  rw [Real.dist_eq,he]
  calc
    _ ≤ |x j.castSucc.succ-y j.castSucc.succ|+|F j 0*(x 0-y 0)| := abs_sub _ _
    _ ≤ dist x y+(1/4:ℝ)*dist x y := by
      rw [abs_mul]
      exact add_le_add hn (mul_le_mul (hF j) hx (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- Equal coarse heights suffice; no converse from coarse to old height
is smuggled into this statement. -/
theorem key_center_dist_of_same_coarse_height {n : ℕ}
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t j,|Fcfg t j 0| ≤ 1/4) (R : ℕ) (k l : Index)
    (hh : (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).1 =
      (coarseYKey D a m p .oneTwo P hP hd F Fcfg R l).1) :
    dist (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).2)
      (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R l).2) ≤
      (5/4:ℝ)*dist (point D a m p .oneTwo P hP hd F Fcfg R k)
        (point D a m p .oneTwo P hP hd F Fcfg R l) := by
  rw [←point_quotient_readback D a m p P hP hd F Fcfg R k,
    ←point_quotient_readback D a m p P hP hd F Fcfg R l,hh]
  exact lowerQuotient_dist _ (hCfg _) _ _

/-- Equality of original translated heights implies the needed equality
of coarse heights directly; Hsingle is not needed in this direction. -/
theorem key_center_dist_of_same_old_height {n : ℕ}
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t j,|Fcfg t j 0| ≤ 1/4) (R : ℕ) (k l : Index)
    (hh : translatedHeight D a m k=translatedHeight D a m l) :
    dist (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R k).2)
      (NativeQuotientGridCenters.center (mu m*(R:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R l).2) ≤
      (5/4:ℝ)*dist (point D a m p .oneTwo P hP hd F Fcfg R k)
        (point D a m p .oneTwo P hP hd F Fcfg R l) := by
  apply key_center_dist_of_same_coarse_height D a m p P hP hd F Fcfg hCfg R k l
  rw [coarse_height_readback,coarse_height_readback,hh]

end NativeConfiguredLowerQuotientReadback
end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit Thm_StickyKakeya4_native_remembered_higher_key_factory_draft_2032.lean
   SHA256 fbee7a0b60df47d7747c7c386754ac9be63b3c0f2b5c54e3fa4b95b9720a0eeb -/
/- UNVERIFIED source-cell witness and fixed-arity higher-key factory.
No compiler or imported-axiom check has run. Frozen48 source is unchanged.

oldHeight reads only the SELECTED remembered tagged image B. The source-cell
reader selects one genuine original witness, never asserts that every old
antecedent of a forgotten intermediate pair has the same height.

The higher-key factory reserves1+2(g+1) slots before the source. Its actual
field values and packed isometry may be chosen after the native source S
exists and before the unique second Reference core. It evaluates a frame
on original source-cell centers; S's source and cells are never rotated.
Key comparability below concerns ref.E1 only. A later rank/subset cut needs
its own actual same-core relation query before any profile lower is reused.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRememberedHigherKeyFactoryDraft2032
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeRememberedSourceMaps NativeLocalCellCoherence NativeTranslatedGrainHeightOverlap
open NativePackedHigherCapacityDraft2006 NativeGenericReferenceData
open NativeExtraQueriedRankConfiguration NativeJointUniformCoarseRelations
open SelfUniform

def oldHeight {nA : ℕ} (B : Finset (ℤ × (Fin nA × Index))) (t : ℤ) : ℤ :=
  if ht : ∃v∈B,finalTime v=t then (Classical.choose ht).1 else 0

theorem oldHeight_readback {nA : ℕ} (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (v : ℤ × (Fin nA × Index)) (hv : v∈B) : oldHeight B (finalTime v)=v.1 := by
  have ht : ∃w∈B,finalTime w=finalTime v := ⟨v,hv,rfl⟩
  simp only [oldHeight,dif_pos ht]
  exact hB (Classical.choose ht) (Classical.choose_spec ht).1 v hv (Classical.choose_spec ht).2

/-- Literal membership of the reindexed local source's cells supplies the
original occurrence and its SELECTED tag, including its exact source time.
This derives the same-old-height fact from the actual source constructor. -/
theorem source_cell_occurrence {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (R : Finset (Fin nA)) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index)
    (hk : k∈sourceCells C R (selectedPairs D a m C c pA O B) 0 (2^c) pA i) :
    ∃(v : Fin nA × Index) (z : Fin n × Index),
      v∈selectedPairs D a m C c pA O B ∧ (v,z)∈O ∧
      parentLabel C 0 (2^c) v.1=pA ∧ localCellLabel C 0 (2^c) pA v=k ∧
      taggedKey D a m C c pA (v,z)∈B ∧
      translatedHeight D a m z.2=oldHeight B (k 3) := by
  let j := NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i
  have hk' : k∈outputCells C (selectedPairs D a m C c pA O B) 0 (2^c) pA j := hk
  obtain ⟨l,hl,hlabel⟩ := (mem_outputCells C (selectedPairs D a m C c pA O B) 0 (2^c) pA j k).mp hk'
  obtain ⟨z,hOcc,hTag⟩ := selected_pair_witness D a m C c pA O B (j,l) hl
  have hj : parentLabel C 0 (2^c) j=pA :=
    ((mem_parentLabels C R 0 (2^c) pA j).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels C R 0 (2^c) pA) i)).2
  have hcell : localCellLabel C 0 (2^c) pA (j,l)=k := hlabel
  have htime : finalTime (taggedKey D a m C c pA ((j,l),z))=k 3 := by
    change localCellLabel C 0 (2^c) pA (j,l) 3=k 3
    exact congrFun hcell 3
  have hHeight := oldHeight_readback B hB (taggedKey D a m C c pA ((j,l),z)) hTag
  rw [htime] at hHeight
  exact ⟨(j,l),z,hl,hOcc,hj,hcell,hTag,hHeight.symm⟩

/-- Every cell surviving the second literal Reference or rank cut still
has a good original witness. Subset membership alone suffices here. -/
theorem retained_cell_occurrence {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (R : Finset (Fin nA)) (c : ℕ) (pA : Parent)
    (O : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (E : Finset (Fin (parentLabels C R 0 (2^c) pA).card × Index))
    (hE : E⊆incidences (sourceCells C R (selectedPairs D a m C c pA O B) 0 (2^c) pA)) :
    ∀k∈E.image Prod.snd,∃(v : Fin nA × Index) (z : Fin n × Index),
      v∈selectedPairs D a m C c pA O B ∧ (v,z)∈O ∧
      parentLabel C 0 (2^c) v.1=pA ∧ localCellLabel C 0 (2^c) pA v=k ∧
      taggedKey D a m C c pA (v,z)∈B ∧
      translatedHeight D a m z.2=oldHeight B (k 3) := by
  intro k hk
  obtain ⟨e,he,rfl⟩ := mem_image.mp hk
  exact source_cell_occurrence D a m C R c pA O B hB e.1 e.2
    ((mem_incidences _ e.1 e.2).mp (hE he))

/-- The number of relation slots depends on the prepared schedule size,
not on source depth, source height count, or the later coefficient values. -/
def extraCount (g : ℕ) : ℕ := 1+((g+1)+(g+1))

def coarseRatio (level : ℕ) (depth : Fin (level+1)) : ℕ := 2^(level-depth.val)

def coarseXKey (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (R : ℕ) (k : Index) : Fin 2 → ℤ :=
  fun j => packedXKey mu O k j/(R:ℤ)

def localXKey (mu : ℝ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ)
    (R : ℕ) (k : Index) : (ℤ × ℤ) × (Fin 2 → ℤ) :=
  (packedHigherKey mu O C F k,coarseXKey mu O R k)

def keyRelations {n level g : ℕ} (D : FiniteScaleSource n)
    (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ)
    (schedule : Fin (g+1) → Fin (level+1)) :
    Fin (extraCount g) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases
    (fun _ : Fin 1 => fun x y => packedHigherKey (D.thickness/2) O C F x.2=
      packedHigherKey (D.thickness/2) O C F y.2)
    (Fin.addCases
      (fun j x y => packedCoarseKey (D.thickness/2) O C F (coarseRatio level (schedule j)) x.2=
        packedCoarseKey (D.thickness/2) O C F (coarseRatio level (schedule j)) y.2)
      (fun j x y => localXKey (D.thickness/2) O C F (coarseRatio level (schedule j)) x.2=
        localXKey (D.thickness/2) O C F (coarseRatio level (schedule j)) y.2))

/-- Quantified labels are evaluated after D/backbone/schedule exist and
before E1. The fixed O,C,F are read-only source data, not selected-core data. -/
def factory (g : ℕ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) : MenuFactory g (extraCount g) :=
  fun _n D _eta _h _a _level _R _original schedule => keyRelations D O C F schedule

lemma factory_refl (g : ℕ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) : MenuRefl (factory g O C F) := by
  intro n D eta h a level R original schedule i
  refine Fin.addCases (fun _ _ => rfl) ?_ i
  exact Fin.addCases (fun _ _ => rfl) (fun _ _ => rfl)

lemma factory_symm (g : ℕ) (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ) : MenuSymm (factory g O C F) := by
  intro n D eta h a level R original schedule i
  refine Fin.addCases (fun _ _ _ hh => hh.symm) ?_ i
  exact Fin.addCases (fun _ _ _ hh => hh.symm) (fun _ _ _ hh => hh.symm)

/-- Source-derived point and higher-key labels remain separate. This
reads the actual caller slot comparison on the SAME literal E1 graph. -/
theorem reference_key_uniformities {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ)
    (H : HasCallerUniformities ref (factory g O C F)) :
    HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix ref.original ref.R L)
      (fun z => packedHigherKey (D.thickness/2) O C F z.2) ∧
    (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix ref.original ref.R L)
      (fun z => packedCoarseKey (D.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) ∧
    (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix ref.original ref.R L)
      (fun z => localXKey (D.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) := by
  constructor
  · intro x hx y hy
    have hh := H (Fin.castAdd ((g+1)+(g+1)) (0:Fin 1)) x hx y hy
    simpa only [factory,keyRelations,Fin.addCases_left,unit_degree_eq_fiber] using hh
  · constructor
    · intro j x hx y hy
      have hh := H (Fin.natAdd 1 (Fin.castAdd (g+1) j)) x hx y hy
      simpa only [factory,keyRelations,Fin.addCases_right,Fin.addCases_left,unit_degree_eq_fiber] using hh
    · intro j x hx y hy
      have hh := H (Fin.natAdd 1 (Fin.natAdd (g+1) j)) x hx y hy
      simpa only [factory,keyRelations,Fin.addCases_right,unit_degree_eq_fiber] using hh

/-- The second Reference parameters and arity precede the native remembered
source. The actual O,C,F values are chosen only AFTER that source exists.
This installs the real finite keys on its literal output incidence graph.
Near extremality is derived by the fixed-source factory from actual volume
estimates; no multiplicity certificate or chosen-source substitution occurs. -/
theorem exists_reference_with_higher_keys (tau : ℝ) (htau : 0<tau) :
    ∃(seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0<seed ∧ seed≤tau/16384 ∧ 0<e ∧ 0<zeta ∧ zeta≤seed/256 ∧ 0<L ∧ 0<g ∧
      1/(g:ℝ)<min (NativeAllTwoScaleConfiguration.boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0<eta0 ∧ eta0≤seed/8 ∧ 0<delta0 ∧
      ∀(n : ℕ) (S : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput S eta),
        (∀i,S.line i∈NativeUnitParentNormalization.fixedCompactClass) →
        0≤eta → eta≤eta0 → S.thickness≤delta0 →
        ∀(shadeLower unionCost : ℝ),0<unionCost →
        ENNReal.ofReal shadeLower≤wzTotalShadingVolume S →
        MeasureTheory.volume (sourceUnion S)≤
          ENNReal.ofReal (unionCost*S.thickness^NativeFixedCompactKakeyaExponent.extremalExponent) →
        unionCost*S.thickness^eta≤shadeLower →
        ∀cells : Fin n → Finset Index,
        (∀i,S.shading i=wzCellShading (mesh S) cells i) →
        ∀(O : E4 ≃ₗᵢ[ℝ] E4) (C F : ℤ → ℝ),
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.original=cells ∧ ref.E1⊆incidences cells ∧
          S.thickness^(-NativeFixedCompactKakeyaExponent.extremalExponent+eta)≤
            (NativeFiniteKakeyaCounts.multiplicity S).toReal ∧
          S.thickness^(-NativeFixedCompactKakeyaExponent.extremalExponent+seed/4)≤
            NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          HasCallerUniformities ref (factory g O C F) ∧
          HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix cells ref.R L)
            (fun z => packedHigherKey (S.thickness/2) O C F z.2) ∧
          (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix cells ref.R L)
            (fun z => packedCoarseKey (S.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) ∧
          (∀j,HasUniformFibers ref.E1 (NativeOriginalParentDensityCore.coreRadix cells ref.R L)
            (fun z => localXKey (S.thickness/2) O C F (coarseRatio ref.level (ref.schedule j)) z.2)) := by
  obtain ⟨seed,e,zeta,L,g,eta0,delta0,hs,hst,he,hz,hzs,hL,hg,hgrid,heta0,hetaSeed,hdelta0,H⟩ :=
    NativeFixedSourceReference.exists_reference_from_volume_bounds tau htau extraCount
  refine ⟨seed,e,zeta,L,g,eta0,delta0,hs,hst,he,hz,hzs,hL,hg,hgrid,heta0,hetaSeed,hdelta0,?_⟩
  intro n S eta h hK heta hetaSmall hsmall shadeLower unionCost hU hShade hUnion hPay cells hCells O C F
  obtain ⟨ref,_hDim,hCaller,hOriginal,hSubset,hNear,hCoreNear⟩ :=
    H n S eta h hK heta hetaSmall hsmall shadeLower unionCost hU hShade hUnion hPay cells hCells
      (factory g O C F) (factory_refl g O C F) (factory_symm g O C F)
  have hKeys := reference_key_uniformities ref O C F hCaller
  rw [hOriginal] at hKeys
  exact ⟨ref,hOriginal,hSubset,hNear,hCoreNear,hCaller,hKeys.1,hKeys.2.1,hKeys.2.2⟩

end NativeRememberedHigherKeyFactoryDraft2032
end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit Thm_StickyKakeya4_native_remembered_alignment_patch_draft_2036.lean
   SHA256 8ef6e32dcbae8536eecb6a3989cc7c7ca6bc11dd7c2a78887c1df60d2d73e6bb -/
/- UNVERIFIED actual first-alignment patch attachment. No compiler run.
The source remains in its original native cubical coordinates.
normalChart is composed only with the packed frame evaluated by key maps.
The actual same-old-phase reader gives74w in E4, hence185w in the planar
Euclidean metric used by localBall;185w<tau when tau=4096w.
Selected-key membership is the literal mother Ycut membership. It is not
an assumed higher-plane support or lower-population condition.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeRememberedAlignmentPatchDraft2036
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints NativeTranslatedGrainHeightOverlap
open NativeConfiguredThirdRelation NativeActualConfiguredPoint NativeLocalParentSource
open NativeConfiguredLowerQuotientReadback NativeRememberedPhaseFootprint
open NativeRelativeParentLabels NativeFixedCompactKakeyaExponent
open CanonicalConfiguredE4Bridge NativeLiteralYHeightAlignment NativePaperAlignmentScales
open NativeAngularChartSelection NativePackedHigherCapacityDraft2006
open scoped BigOperators

/-- The common planar coordinate permutation is applied to the packed
key frame, not to native lines or native cubical cells. -/
def normalChart (j : Fin 2) : E4 ≃ₗᵢ[ℝ] E4 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1:Fin 4) j.castSucc.succ)

lemma normalChart_height (j : Fin 2) (x : E4) : normalChart j x 3=x 3 := by
  fin_cases j <;> simp [normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

lemma normalChart_tangent (j : Fin 2) (x : E4) : normalChart j x 0=x 0 := by
  fin_cases j <;> simp [normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

def chartRows (j : Fin 2) (F : Matrix (Fin 2) (Fin 1) ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  fun i a => F (chartPerm j i) a

theorem normalChart_quotient (j : Fin 2) (F : Matrix (Fin 2) (Fin 1) ℝ) (x : E4) :
    lowerQuotient (chartRows j F) (normalChart j x)=chartPoint j (lowerQuotient F x) := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft',
      lowerQuotient,chartRows,chartPoint,chartPerm]

theorem normalized_chart_quotient (j : Fin 2) (F : Matrix (Fin 2) (Fin 1) ℝ)
    (x : E4) (anchor : Fin 2 → ℝ) (tau : ℝ) :
    normalizedLowerQuotient (normalChart j x) (chartRows j F 0 0) (chartRows j F 1 0)
      (chartPoint j anchor) tau = normalization j anchor tau (lowerQuotient F x) := by
  rw [normalization_apply]
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [normalizedLowerQuotient,normalChart,LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft',chartRows,chartPoint,chartPerm,lowerQuotient,
      NormalizedQuantizedPatches.affine]

theorem permuted_witness_pullback (O : E4 ≃ₗᵢ[ℝ] E4) (j : Fin 2) (x : E4) :
    (O.trans (normalChart j)).symm (normalChart j x)=O.symm x := by simp

/-- At one genuine old height, the literal first planar Y points inherit
their Euclidean distance bound from the ACTUAL original phase, not from a
substitute enlarged patch or a higher-field Lipschitz assertion. -/
theorem actual_phase_Y_distance {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T : Finset (Fin n × Index)) (m : ℕ) (hm : 6≤m)
    (hscale : D.thickness≤(rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hSK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b0 c : ℕ) (hb0 : 8≤b0) (hc : c≤b0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b0:ℕ):ℝ))
    (z z' : Fin n × Index)
    (hz : z∈NativeCubicalIncidenceCounts.incidences original)
    (hz' : z'∈NativeCubicalIncidenceCounts.incidences original)
    (hzP : z.1∈parentLabels D backbone a (2^m) p)
    (hzP' : z'.1∈parentLabels D backbone a (2^m) p)
    (ht : translatedHeight D a m z.2=translatedHeight D a m z'.2)
    (hphase : relativeLabel D a (2^m) p (2^c) z.1=relativeLabel D a (2^m) p (2^c) z'.1) :
    dist (EuclideanAlignmentPatches.euclidean
      (NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2).2))
      (EuclideanAlignmentPatches.euclidean
      (NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
        (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z'.2).2))≤
      185*(64/((2^c:ℕ):ℝ)) := by
  have hE4 := actual_configured_diameter h original horiginal ha backbone Eref T m hm hscale p hS hSK
    levelS b0 c hb0 hc .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch z z' hz hz' hzP hzP' ht hphase
  have hSup := key_center_dist_of_same_old_height D a m p P hP hd F Fcfg
    (fun t i => hCfg t i 0) R0 z.2 z'.2 ht
  let x := NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
    (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2).2
  let y := NativeQuotientGridCenters.center (mu m*(R0:ℝ)/512)
    (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z'.2).2
  have hc0 : 0≤(5/4:ℝ)*dist (point D a m p .oneTwo P hP hd F Fcfg R0 z.2)
      (point D a m p .oneTwo P hP hd F Fcfg R0 z'.2) := by positivity
  have hEuclid := EuclideanAlignmentPatches.euclidean_dist_le_card_mul x y _ hc0 (fun j => by
    exact (show |x j-y j|≤dist x y by simpa only [Real.dist_eq] using dist_le_pi_dist x y j).trans hSup)
  change dist (EuclideanAlignmentPatches.euclidean x) (EuclideanAlignmentPatches.euclidean y)≤_
  norm_num only [Nat.cast_ofNat] at hEuclid
  nlinarith only [hEuclid,hE4]

lemma selected_key_center_mem (kept : Finset Key) (delta : ℝ) (q : Key) (hq : q∈kept) :
    NativeQuotientGridCenters.center delta q.2∈heightPoints kept delta q.1 := by
  exact mem_image_of_mem _ (mem_filter.mpr ⟨hq,rfl⟩)

/-- Consume the actual first common-menu selected slice, including its
original selected point set. The caller obtains hNear from the preceding
actual-phase reader with185w<tau, so hPatch is an output here. -/
theorem selected_height_patch {X : Type*} (A : Finset X) (key : X → Key)
    (kept Y : Finset Key) (u : ℕ) (t zeta chi : ℝ) (height : ℤ)
    (W : HeightAlignment Y u t zeta chi height)
    (hSelected : heightPoints kept ((2:ℝ)⁻¹^u/512) height=W.selected)
    (hKey : ∀z∈A,key z∈kept) (hHeight : ∀z∈A,(key z).1=height)
    (z0 : X) (hz0 : z0∈A)
    (hNear : ∀z∈A,
      dist (EuclideanAlignmentPatches.euclidean (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2))
        (EuclideanAlignmentPatches.euclidean (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z0).2))<
        NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val) :
    let anchor := NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z0).2
    let tau := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val
    let rho := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val
    let Patch := (localBall W.selected anchor tau).image (normalization W.chart anchor tau)
    NativeLiteralAlignedSet.NearlyLiteralAligned Patch (rho/tau) t W.exponent ((rho/tau)^(-zeta)) ∧
      ∀z∈A,normalization W.chart anchor tau
        (NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2)∈Patch := by
  intro anchor tau rho Patch
  have hMem : ∀z∈A,NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2∈W.selected := by
    intro z hz
    rw [←hSelected]
    have hh := selected_key_center_mem kept ((2:ℝ)⁻¹^u/512) (key z) (hKey z hz)
    simpa only [hHeight z hz] using hh
  refine ⟨W.aligned anchor (hMem z0 hz0),?_⟩
  intro z hz
  exact mem_image_of_mem _ (mem_filter.mpr ⟨hMem z hz,hNear z hz⟩)

/-- One ORIGINAL occupied-height/old-phase slice supplies its genuine
common higher field and FULL scalar Y. The patch membership and its radius
are derived internally from actual original incidences, the literal Ycut,
and the original HeightAlignment selected slice. -/
theorem actual_old_height_scalar_family {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T A : Finset (Fin n × Index)) (hAn : A.Nonempty)
    (m : ℕ) (hm : 6≤m) (hscale : D.thickness≤(rho m)^2) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hSK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b0 c : ℕ) (hb0 : 8≤b0) (hc : c≤b0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b0:ℕ):ℝ))
    (hA : A⊆NativeCubicalIncidenceCounts.incidences original)
    (hParent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (oldH : ℤ) (hHeight : ∀z∈A,translatedHeight D a m z.2=oldH)
    (q : Parent) (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=q)
    (kept Ybase : Finset Key) (u : ℕ) (t zeta chi : ℝ)
    (hBaseEq : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (W : HeightAlignment Ybase u t zeta chi (oldH/((8*R0:ℕ):ℤ)))
    (hSelected : heightPoints kept ((2:ℝ)⁻¹^u/512) (oldH/((8*R0:ℕ):ℤ))=W.selected)
    (hKey : ∀z∈A,coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2∈kept)
    (hTau : NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=
      4096*(64/((2^c:ℕ):ℝ))) :
    let tau := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val
    let rhoA := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val
    let M := chartRows W.chart (Fcfg (oldH/((8*R0:ℕ):ℤ)))
    ∃(anchor : Fin 2 → ℝ) (theta : ℝ) (Y : Finset ℝ),
      anchor∈W.selected ∧ |theta|≤1 ∧ |M 1 0-theta*M 0 0|≤1/2 ∧ Y.Nonempty ∧
      (∀y∈Y,|y|≤1) ∧
      FiniteVoronoiRealADCoarsening.ADBounds Y (rhoA/tau) ((rhoA/tau)^(-zeta)) (t-W.exponent) ∧
      ∀z∈A,∃y∈Y,
        |NativeHigherQuotientParentTransport.higherY (M 1 0-theta*M 0 0) theta
          (normalChart W.chart (point D a m p .oneTwo P hP hd F Fcfg R0 z.2))-
          (tau*y+(chartPoint W.chart anchor 1-theta*chartPoint W.chart anchor 0))|≤2*rhoA := by
  intro tau rhoA M
  let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
  let ypoint := fun z : Fin n × Index => NativeQuotientGridCenters.center ((2:ℝ)⁻¹^u/512) (key z).2
  obtain ⟨z0,hz0⟩ := hAn
  let anchor := ypoint z0
  have hKeyHeight : ∀z∈A,(key z).1=oldH/((8*R0:ℕ):ℤ) := by
    intro z hz
    rw [coarse_height_readback,hHeight z hz]
  have hAnchor : anchor∈W.selected := by
    rw [←hSelected]
    have hh := selected_key_center_mem kept ((2:ℝ)⁻¹^u/512) (key z0) (hKey z0 hz0)
    simpa only [hKeyHeight z0 hz0] using hh
  have hNear : ∀z∈A,dist (EuclideanAlignmentPatches.euclidean (ypoint z))
      (EuclideanAlignmentPatches.euclidean anchor)<tau := by
    intro z hz
    have hh := actual_phase_Y_distance h original horiginal ha backbone Eref T m hm hscale p hS hSK
      levelS b0 c hb0 hc P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch z z0
      (hA hz) (hA hz0) (hParent z hz) (hParent z0 hz0)
      ((hHeight z hz).trans (hHeight z0 hz0).symm) ((hPhase z hz).trans (hPhase z0 hz0).symm)
    rw [hBaseEq] at hh
    have hw : (0:ℝ)<64/((2^c:ℕ):ℝ) := by positivity
    change dist (EuclideanAlignmentPatches.euclidean (ypoint z))
      (EuclideanAlignmentPatches.euclidean (ypoint z0))≤_ at hh
    change dist (EuclideanAlignmentPatches.euclidean (ypoint z))
      (EuclideanAlignmentPatches.euclidean (ypoint z0))<_
    change tau=4096*(64/((2^c:ℕ):ℝ)) at hTau
    linarith only [hh,hTau,hw]
  obtain ⟨hPatch,hMem⟩ := selected_height_patch A key kept Ybase u t zeta chi
    (oldH/((8*R0:ℕ):ℤ)) W hSelected hKey hKeyHeight z0 hz0 hNear
  let Patch := (localBall W.selected anchor tau).image (normalization W.chart anchor tau)
  obtain ⟨theta,Y,hTheta,hYn,hYbox,hYAD,hWitness⟩ :=
    nearly_aligned_scalar_witnesses Patch (rhoA/tau) t W.exponent ((rhoA/tau)^(-zeta)) hPatch
  have hM0 : |M 0 0|≤1/4 := hCfg _ _ _
  have hM1 : |M 1 0|≤1/4 := hCfg _ _ _
  have hC : |M 1 0-theta*M 0 0|≤1/2 := by
    have hh := abs_sub (M 1 0) (theta*M 0 0)
    rw [abs_mul] at hh
    have hm' := mul_le_mul hTheta hM0 (abs_nonneg _) zero_le_one
    linarith only [hh,hm',hM1]
  refine ⟨anchor,theta,Y,hAnchor,hTheta,hC,hYn,hYbox,hYAD,?_⟩
  intro z hz
  let cfg := point D a m p .oneTwo P hP hd F Fcfg R0 z.2
  have hRead : lowerQuotient (Fcfg (oldH/((8*R0:ℕ):ℤ))) cfg=ypoint z := by
    have hh := point_quotient_readback D a m p P hP hd F Fcfg R0 z.2
    rw [hBaseEq] at hh
    simpa only [hKeyHeight z hz] using hh
  have hNorm : normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau = normalization W.chart anchor tau (ypoint z) := by
    rw [normalized_chart_quotient,hRead]
  have hIn : normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau∈Patch := by
    rw [hNorm]
    exact hMem z hz
  obtain ⟨y,hy,he⟩ := hWitness _ hIn
  have htau0 : 0<tau := NativeDyadicTubeStopping.scale_pos (by positivity) _
  refine ⟨y,hy,?_⟩
  rw [normalized_lower_identity (normalChart W.chart cfg) (M 0 0) (M 1 0)
    theta (chartPoint W.chart anchor) tau htau0.ne']
  have hid : tau*(normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau 1-
      theta*normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
        (chartPoint W.chart anchor) tau 0)+
      (chartPoint W.chart anchor 1-theta*chartPoint W.chart anchor 0)-
      (tau*y+(chartPoint W.chart anchor 1-theta*chartPoint W.chart anchor 0))=
    tau*(normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
      (chartPoint W.chart anchor) tau 1-
      theta*normalizedLowerQuotient (normalChart W.chart cfg) (M 0 0) (M 1 0)
        (chartPoint W.chart anchor) tau 0-y) := by ring
  rw [hid,abs_mul,abs_of_pos htau0]
  have hh := mul_le_mul_of_nonneg_left he htau0.le
  have hcancel : tau*(2*(rhoA/tau))=2*rhoA := by field_simp [htau0.ne'] <;> ring
  exact hh.trans_eq hcancel

end NativeRememberedAlignmentPatchDraft2036
end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit Thm_StickyKakeya4_native_second_reference_payment_draft_2043.lean
   SHA256 cb702eebc03eabb9fa853fac9ddc815c9a6a9d60b08da02068e3d8399d3ee89d -/
/- UNVERIFIED scalar payment at the actual final native sigma.
The second Reference's eta0 precedes first-stage E, zeta53, chi and D.
The final admission is weakened to eta0/2; no intermediate z2 is substituted.
This pays the actual U,L inequalities when their source readers are composed
on one S. It does not assert those source inequalities or native admission.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeSecondReferencePaymentDraft2043
open StickyKakeya4

/-- A fixed quarter-eta0 gap pays the concrete shading denominator and
union numerator, uniformly over the later allowed E,chi,etaUnion. -/
theorem exists_volume_payment_cutoff (eta0 Cnum Cden : ℝ)
    (hEta : 0<eta0) (hNum : 0<Cnum) (hDen : 0<Cden) :
    ∃sigma0 : ℝ,0<sigma0 ∧ sigma0≤1 ∧
      ∀(E chi etaUnion sigma L U : ℝ),
        0≤E → E≤eta0/4 → 0<chi → 0≤etaUnion → etaUnion≤chi*eta0/32 →
        0<sigma → sigma≤sigma0 →
        sigma^(5*E/4096)/Cden≤L → U≤Cnum*sigma^(-(2*etaUnion/chi)) →
        U*sigma^(eta0/2)≤L := by
  obtain ⟨sigma0,hs0,hs01,Hcut⟩ := exists_positive_rpow_absorption_threshold
    (show 0<eta0/4 by positivity) (show 0≤Cnum*Cden by positivity) (by norm_num : (0:ℝ)<1)
  refine ⟨sigma0,hs0,hs01,?_⟩
  intro E chi etaUnion sigma L U _hE hEtop hChi _hUnion hUnionTop hSigma hSmall hL hU
  have hs1 : sigma≤1 := hSmall.trans hs01
  have hUnionLoss : 2*etaUnion/chi≤eta0/16 := by
    apply (div_le_iff₀ hChi).mpr
    nlinarith only [hUnionTop]
  have hMargin : 5*E/4096+eta0/4≤eta0/2-2*etaUnion/chi := by
    linarith only [hUnionLoss,hEtop,hEta]
  have hPow : sigma^(eta0/2-2*etaUnion/chi)≤sigma^(5*E/4096+eta0/4) :=
    Real.rpow_le_rpow_of_exponent_ge hSigma hs1 hMargin
  have hAbsorb := Hcut sigma hSigma hSmall
  calc
    U*sigma^(eta0/2)≤(Cnum*sigma^(-(2*etaUnion/chi)))*sigma^(eta0/2) :=
      mul_le_mul_of_nonneg_right hU (Real.rpow_nonneg hSigma.le _)
    _ = Cnum*sigma^(eta0/2-2*etaUnion/chi) := by
      rw [mul_assoc,←Real.rpow_add hSigma]
      congr 2
      ring
    _ ≤ Cnum*sigma^(5*E/4096+eta0/4) := mul_le_mul_of_nonneg_left hPow hNum.le
    _ = Cnum*sigma^(eta0/4)*sigma^(5*E/4096) := by
      rw [Real.rpow_add hSigma]
      ring
    _ ≤ sigma^(5*E/4096)/Cden := by
      apply (le_div_iff₀ hDen).mpr
      calc
        _ = (Cnum*Cden*sigma^(eta0/4))*sigma^(5*E/4096) := by ring
        _ ≤ 1*sigma^(5*E/4096) :=
          mul_le_mul_of_nonneg_right hAbsorb (Real.rpow_nonneg hSigma.le _)
        _ = _ := one_mul _
    _ ≤ L := hL

/-- The actual stronger source admission may be used with eta0/2 in the
fixed Reference. This does not require a lower bound for its old exponent. -/
theorem native_input_at_half_eta0 {n : ℕ} {S : FiniteScaleSource n} {E eta0 : ℝ}
    (hS : IsWangZakharovNativeFiniteInput S E) (hE : E≤eta0/4) (hEta : 0≤eta0) :
    IsWangZakharovNativeFiniteInput S (eta0/2) :=
  NativeFiniteKakeyaCounts.input_mono hS (by linarith only [hE,hEta])

/-- Any proved positive source power window pulls the two final cutoffs
back to one ORIGINAL-datum cutoff chosen before the original datum. -/
theorem exists_original_cutoff (power sigma0 deltaRef : ℝ)
    (hPower : 0<power) (hSigma : 0<sigma0) (hRef : 0<deltaRef) :
    ∃delta0 : ℝ,0<delta0 ∧ delta0≤1 ∧
      ∀delta sigma : ℝ,0<delta → delta≤delta0 → sigma≤delta^power →
        sigma≤sigma0 ∧ sigma≤deltaRef := by
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    hPower (by norm_num : (0:ℝ)≤1) (lt_min hSigma hRef)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta sigma hd hsmall hwindow
  have hh : delta^power≤min sigma0 deltaRef := by simpa only [one_mul] using H delta hd hsmall
  exact ⟨hwindow.trans (hh.trans (min_le_left _ _)),hwindow.trans (hh.trans (min_le_right _ _))⟩

end NativeSecondReferencePaymentDraft2043
end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit Thm_StickyKakeya4_native_higher_reference_mass_draft_2045.lean
   SHA256 d0cd00662f421fc997ebe65e7a780bdb829c69999527a5787798825537141a80 -/
/- UNVERIFIED actual fixed-Reference mass reader. No compiler run.
L is the remembered source's actual total-shading lower. The literal source
cells have volume(sigma/2)^4. The new E1 is a deduplicated incidence set on
those cells, and only its actual IsCore retention factor is paid.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeHigherReferenceMassDraft2045
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeGenericReferenceData NativeOriginalParentDensityCore

theorem reference_factor_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (heta : 0≤eta) :
    (factor ref.dimension (g+1) L:ℝ)≤D.thickness^(-(seed/8)) := by
  let Q := coreRadix ref.original ref.R L
  have hQ4 : 4≤Q := NativeSourceSizeBounds.radix_four_le _ _
  have hQ : (1:ℝ)≤(Q:ℝ)^2 := by
    have hh : (4:ℝ)≤Q := by exact_mod_cast hQ4
    nlinarith only [hh]
  have hBudget := NativeTwoStageTransversalityBudget.retention_radix_le_of_transfer_cost
    h.1.2.1 h.1.2.2.1 heta (factor ref.dimension (g+1) L) Q
    (factor ref.dimension (g+1) L:ℝ) le_rfl ref.cost
  exact (show (factor ref.dimension (g+1) L:ℝ)≤(factor ref.dimension (g+1) L:ℝ)*(Q:ℝ)^2 by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg _)).trans hBudget

theorem actual_shading_to_reference_mass {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (shadeLower : ℝ) (hShade0 : 0≤shadeLower)
    (hShade : ENNReal.ofReal shadeLower≤wzTotalShadingVolume D) :
    16*shadeLower≤(factor ref.dimension (g+1) L:ℝ)*(ref.E1.card:ℝ)*D.thickness^4 := by
  have hMesh : 0<mesh D := half_pos h.1.2.1
  have hRead := total_shading_eq_incidence_volume D hMesh ref.original ref.backbone.1
  have hFinite : wzTotalShadingVolume D≠⊤ := by rw [hRead]; finiteness
  have hReal := ENNReal.toReal_mono hFinite hShade
  rw [hRead] at hReal
  have hMass : shadeLower≤((incidences ref.original).card:ℝ)*(D.thickness/2)^4 := by
    simpa only [ENNReal.toReal_ofReal hShade0,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_natCast,ENNReal.toReal_ofReal hMesh.le,mesh] using hReal
  have hCore : ((incidences ref.original).card:ℝ)≤
      (factor ref.dimension (g+1) L:ℝ)*ref.E1.card := by
    exact_mod_cast ref.core.2.2.1
  have hh := hMass.trans (mul_le_mul_of_nonneg_right hCore (pow_nonneg (half_pos h.1.2.1).le 4))
  nlinarith only [hh]

/-- This is the actual mass input for packed_dense_X/packed_Y_class_lower.
The older native coarse thickness never replaces D.thickness. -/
theorem normalized_reference_mass {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (heta : 0≤eta) (shadeLower : ℝ) (hShade0 : 0≤shadeLower)
    (hShade : ENNReal.ofReal shadeLower≤wzTotalShadingVolume D) :
    16*shadeLower*D.thickness^(seed/8)≤(ref.E1.card:ℝ)*D.thickness^4 := by
  have hd := h.1.2.1
  have hMass := actual_shading_to_reference_mass ref shadeLower hShade0 hShade
  have hFactor := reference_factor_upper ref heta
  have hh : 16*shadeLower≤D.thickness^(-(seed/8))*(ref.E1.card:ℝ)*D.thickness^4 :=
    hMass.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hFactor (Nat.cast_nonneg _)) (pow_nonneg hd.le 4))
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le (seed/8))
  have hCancel : D.thickness^(-(seed/8))*D.thickness^(seed/8)=1 := by
    rw [←Real.rpow_add hd,neg_add_cancel,Real.rpow_zero]
  calc
    _ ≤ (D.thickness^(-(seed/8))*(ref.E1.card:ℝ)*D.thickness^4)*D.thickness^(seed/8) := hm
    _ = (D.thickness^(-(seed/8))*D.thickness^(seed/8))*((ref.E1.card:ℝ)*D.thickness^4) := by ring
    _ = _ := by rw [hCancel,one_mul]

end NativeHigherReferenceMassDraft2045
end -- explicit anonymous noncomputable source-unit section

/- Frozen source unit Thm_StickyKakeya4_native_remembered_final_time_scalar_draft_2054.lean
   SHA256 6f5334528f208c9173d7a3096ade6da94c31c4c8d9b5c8e0b4607cbe19de6c47 -/
/- UNVERIFIED actual remembered-source scalar caller. No compiler run.
The final-time field is obtained from the literal first HeightAlignment.
Every source cell supplies its own selected original occurrence; the actual
source halo is then derived. No higher support, hPatch, normalized quotient
membership, common physical-height or halo input is admitted here.
The scalar set Y is FULL first-alignment Y, at rho/tau=sigma/32768.
All cells and keys remain in the original native cubical source coordinates.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedFinalTimeScalarDraft2054
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeParentLabels
open NativeTranslatedGrainHeightOverlap NativeConfiguredThirdRelation NativeActualConfiguredPoint
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints CanonicalConfiguredE4Bridge
open NativeLiteralYHeightAlignment NativePaperAlignmentScales NativePackedHigherCapacityDraft2006
open NativeRememberedSourceMaps NativeRememberedCellHalo NativeLocalCellCoherence
open NativeRememberedHigherKeyFactoryDraft2032 NativeRememberedAlignmentPatchDraft2036
open NativeFullYHaloCoverDraft2017

def timeCells {n : ℕ} (cells : Fin n → Finset Index) (t : ℤ) : Finset Index :=
  ((incidences cells).image Prod.snd).filter (fun k => k 3=t)

/-- Read the actual common5.3 menu at an occupied final native time.
Its original coarse height is derived from the selected source occurrence.
Consequently the common chart, rho/tau depths, retained exponent bin, and
whole selected planar slice are all available for the following caller. -/
theorem occupied_alignment_height {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
    (a : ℝ) (m b : ℕ) (p : Parent) (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card) (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) (c : ℕ) (R : Finset (Fin Q.card)) (pA : Parent)
    (B : Finset (ℤ × (Fin Q.card × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (R0 : ℕ)
    (kept Ybase : Finset NativeLiteralYHeightAlignment.Key) (u bins : ℕ) (t zeta chi : ℝ)
    (W : ∀h : {h : ℤ // h∈Ybase.image Prod.fst},HeightAlignment Ybase u t zeta chi h.val)
    (bin : ℝ → Fin (bins+1)) (menu : NativeYCommonScaleSelection.Menu u bins)
    (hCommon : ∀h∈kept.image Prod.fst,∃hh : h∈Ybase.image Prod.fst,
      (W ⟨h,hh⟩).chart=menu.1 ∧ (W ⟨h,hh⟩).rhoDepth=menu.2.1 ∧
      (W ⟨h,hh⟩).tauDepth=menu.2.2.1 ∧ bin (W ⟨h,hh⟩).exponent=menu.2.2.2 ∧
      heightPoints kept ((2:ℝ)⁻¹^u/512) h=(W ⟨h,hh⟩).selected)
    (hKey : ∀z∈A,coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2∈kept)
    (finalH : ℤ) (i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index)
    (hk : k∈sourceCells C R
      (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B)
      0 (2^c) pA i) (ht : k 3=finalH) :
    ∃hh : oldHeight B finalH/((8*R0:ℕ):ℤ)∈Ybase.image Prod.fst,
      let H := W ⟨oldHeight B finalH/((8*R0:ℕ):ℤ),hh⟩
      H.chart=menu.1 ∧ H.rhoDepth=menu.2.1 ∧ H.tauDepth=menu.2.2.1 ∧
      bin H.exponent=menu.2.2.2 ∧
      heightPoints kept ((2:ℝ)⁻¹^u/512) (oldHeight B finalH/((8*R0:ℕ):ℤ))=H.selected := by
  obtain ⟨v,z,_hv,hOcc,_hCurrent,_hCell,_hTag,hOld⟩ :=
    source_cell_occurrence D a m C R c pA
      (occurrences h backbone a m b p hp Q cells A) B hB i k hk
  have hzA := ((mem_occurrences h backbone a m b p hp Q cells A (v,z)).mp hOcc).2.1
  have hHeight : (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2).1=
      oldHeight B finalH/((8*R0:ℕ):ℤ) := by
    rw [NativeConfiguredLowerQuotientReadback.coarse_height_readback,hOld,ht]
  apply hCommon
  exact mem_image.mpr ⟨coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2,hKey z hzA,hHeight⟩

/-- For one OCCUPIED native S cell-time, derive the actual common corrected
higher field, full scalar family, and every native-cell witness directly
from selected occurrences and the first HeightAlignment. The old-height
slice is constructed inside the proof, so no per-old-height population
hypothesis is required. Its nonemptiness comes from a genuine S cell. -/
theorem actual_final_time_scalar_family {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T A : Finset (Fin n × Index))
    (m : ℕ) (hm : 6≤m) (p : Parent) (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hscale : D.thickness≤(rho m)^2)
    (hS : IsWangZakharovNativeFiniteInput (source h backbone Eref a m p) etaS)
    (hSK : ∀i,(source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b c : ℕ) (hb : 8≤b) (hc : c≤b)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness≤1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ)≤64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (hA : A⊆incidences original)
    (hParent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (q : Parent) (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=q)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b:ℕ):ℝ))
    (R : Finset (Fin Q.card)) (pA : Parent)
    (B : Finset (ℤ × (Fin Q.card × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (finalH : ℤ)
    (i0 : Fin (parentLabels C R 0 (2^c) pA).card) (k0 : Index)
    (hk0 : k0∈sourceCells C R
      (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B)
      0 (2^c) pA i0) (ht0 : k0 3=finalH)
    (kept Ybase : Finset NativeLiteralYHeightAlignment.Key) (u : ℕ) (t zeta chi : ℝ)
    (hZeta : 0≤zeta)
    (hBaseEq : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (W : HeightAlignment Ybase u t zeta chi (oldHeight B finalH/((8*R0:ℕ):ℤ)))
    (hSelected : heightPoints kept ((2:ℝ)⁻¹^u/512)
      (oldHeight B finalH/((8*R0:ℕ):ℤ))=W.selected)
    (hKey : ∀z∈A,coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2∈kept)
    (hTau : NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=
      4096*(64/((2^c:ℕ):ℝ)))
    (hRho : C.thickness=8*NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val) :
    let sigma := ((2^c:ℕ):ℝ)*C.thickness/64
    let O := (NativePackedFrameIsometry.frame .oneTwo P hP hd).trans (normalChart W.chart)
    let M := chartRows W.chart (Fcfg (oldHeight B finalH/((8*R0:ℕ):ℤ)))
    let cellsS := sourceCells C R
      (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B) 0 (2^c) pA
    ∃(theta beta : ℝ) (Y : Finset ℝ),
      |theta|≤1 ∧ |M 1 0-theta*M 0 0|≤1/2 ∧ Y.Nonempty ∧ (∀y∈Y,|y|≤1) ∧
      FiniteVoronoiRealADCoarsening.ADBounds Y (sigma/32768)
        ((sigma/32768)^(-zeta)) (t-W.exponent) ∧
      (∀(i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index),
        k∈sourceCells C R
          (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B)
          0 (2^c) pA i → k 3=finalH →
        ∃y∈Y,|packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)-
          (512*y+beta)|≤13*sigma) ∧
      ∀r : ℝ,sigma/2≤r → r≤1 →
        ((scalarGrid (timeCells cellsS finalH)
          (fun k => packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)) r).card:ℝ)≤
          452*((sigma/32768)^(-zeta))^2*(r/512)^(-(t-W.exponent)) ∧
        ∀(x : Fin 1 → ℝ) (radius : ℝ),r/512≤radius → radius≤1 →
          (((scalarGrid (timeCells cellsS finalH)
            (fun k => packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)) r).filter
              (fun k => dist (NativeQuotientGridCenters.center (r/512) k) x≤radius)).card:ℝ)≤
            452*((sigma/32768)^(-zeta))^2*58^(t-W.exponent)*(radius/(r/512))^(t-W.exponent) := by
  intro sigma O M cellsS
  let oldH := oldHeight B finalH
  let Occ := occurrences h backbone a m b p hp Q cells A
  let Aold := A.filter (fun z => translatedHeight D a m z.2=oldH)
  let cfg := point D a m p .oneTwo P hP hd F Fcfg R0
  let O0 := NativePackedFrameIsometry.frame .oneTwo P hP hd
  let tau := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val
  let rhoA := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val
  obtain ⟨v0,z0,_hv0,hOcc0,_hp0,_hcell0,_htag0,hOld0⟩ :=
    source_cell_occurrence D a m C R c pA Occ B hB i0 k0 hk0
  have hz0A : z0∈A := ((mem_occurrences h backbone a m b p hp Q cells A (v0,z0)).mp hOcc0).2.1
  have hz0old : z0∈Aold := by
    apply mem_filter.mpr
    exact ⟨hz0A,by simpa only [ht0] using hOld0⟩
  have hAold : Aold⊆incidences original := fun _ hz => hA (mem_filter.mp hz).1
  have hParentOld : ∀z∈Aold,z.1∈parentLabels D backbone a (2^m) p :=
    fun z hz => hParent z (mem_filter.mp hz).1
  have hHeightOld : ∀z∈Aold,translatedHeight D a m z.2=oldH := fun _ hz => (mem_filter.mp hz).2
  obtain ⟨anchor,theta,Y,_hAnchor,hTheta,hCoeff,hYn,hYbox,hYAD,hOldWitness⟩ :=
    actual_old_height_scalar_family h original horiginal ha backbone Eref T Aold ⟨z0,hz0old⟩
      m hm hscale p hS hSK levelS b c hb hc P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      hAold hParentOld oldH hHeightOld q (fun z hz => hPhase z (mem_filter.mp hz).1)
      kept Ybase u t zeta chi hBaseEq W hSelected (fun z hz => hKey z (mem_filter.mp hz).1) hTau
  let alpha := NativeAngularChartSelection.chartPoint W.chart anchor 1-
    theta*NativeAngularChartSelection.chartPoint W.chart anchor 0
  let anchorNative := O0.symm (cfg z0.2)
  let beta := NativeHigherQuotientParentTransport.horizontalScale (2^c)*alpha+
    packedParentShift C 0 (2^c) pA O (M 1 0-theta*M 0 0) theta anchorNative
  have hSigma : 0<sigma := by have hh := hC.1.2.1; dsimp only [sigma]; positivity
  have hPow : ((2^c:ℕ):ℝ)≠0 := by positivity
  have hTauScale : NativeHigherQuotientParentTransport.horizontalScale (2^c)*tau=512 := by
    change (_:ℝ)*NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=512
    rw [hTau]
    unfold NativeHigherQuotientParentTransport.horizontalScale
    field_simp [hPow]
    <;> ring
  have hMesh : rhoA/tau=sigma/32768 := by
    change NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val/
      NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=
      (((2^c:ℕ):ℝ)*C.thickness/64)/32768
    rw [hTau,hRho]
    field_simp [hPow]
    <;> ring
  have hNativeWitness : ∀(i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index),
      k∈cellsS i → k 3=finalH →
      ∃y∈Y,|packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)-
        (512*y+beta)|≤13*sigma := by
    intro i k hk hkt
    obtain ⟨v,z,_hv,hOcc,hCurrent,hCell,_hTag,hOld⟩ :=
      source_cell_occurrence D a m C R c pA Occ B hB i k hk
    have hzA : z∈A := ((mem_occurrences h backbone a m b p hp Q cells A (v,z)).mp hOcc).2.1
    have hzold : z∈Aold := mem_filter.mpr ⟨hzA,by simpa only [hkt] using hOld⟩
    obtain ⟨y,hy,hWitness⟩ := hOldWitness z hzold
    have hTimeCfg : cfg z.2 3=cfg z0.2 3 := by
      simp only [cfg,point,graphGrid_height,sourceLabel_height,hHeightOld z hzold,hHeightOld z0 hz0old]
    have hInverseHeight (x : E4) : O0.symm x 3=x 3 := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (NativePackedFrameIsometry.frame_height .oneTwo P hP hd (O0.symm x)).symm
    have hTime : O0.symm (cfg z.2) 3=anchorNative 3 := by
      rw [hInverseHeight,hInverseHeight]
      exact hTimeCfg
    have hOldScalar : |packedQuotient O (M 1 0-theta*M 0 0) theta (O0.symm (cfg z.2))-
        (tau*y+alpha)|≤2*rhoA := by
      simpa only [packedQuotient,LinearIsometryEquiv.trans_apply,
        LinearIsometryEquiv.apply_symm_apply] using hWitness
    have hHalo := occurrence_center_near h original horiginal ha backbone m b hm p hp hNscale hRelScale
      Q C hC cells hcells haC hthickness A hA hParent .oneTwo P hP hd F Fcfg hF hCfg
      R0 hR0 hbase hmatch c pA (v,z) hOcc hCurrent
    change dist (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128) (localCellLabel C 0 (2^c) pA v))
      (physicalMap C 0 (2^c) pA (O0.symm (cfg z.2)))≤4*sigma at hHalo
    rw [hCell] at hHalo
    have hMu : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp only [sigma]; ring
    rw [hMu] at hHalo
    exact ⟨y,hy,parent_scalar_witness C 0 (2^c) pA O (M 1 0-theta*M 0 0) theta
      (hCoeff.trans (by norm_num)) hTheta rhoA tau C.thickness sigma alpha y hSigma hRho rfl
      hTauScale (O0.symm (cfg z.2)) anchorNative hTime k hOldScalar hHalo⟩

  have hAD : FiniteVoronoiRealADCoarsening.ADBounds Y (sigma/32768)
      ((sigma/32768)^(-zeta)) (t-W.exponent) := by simpa only [hMesh] using hYAD
  refine ⟨theta,beta,Y,hTheta,hCoeff,hYn,hYbox,hAD,hNativeWitness,?_⟩
  intro r hr hr1
  have htau0 : 0<tau := NativeDyadicTubeStopping.scale_pos (by positivity) _
  have he1 : sigma/32768≤1 := by
    rw [←hMesh]
    exact (div_le_one htau0).mpr W.scale_order.le
  have hK : 1≤(sigma/32768)^(-zeta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) he1 (neg_nonpos.mpr hZeta)
  have hAlpha : 0≤t-W.exponent := sub_nonneg.mpr (W.exponent_upper.trans (min_le_left _ _))
  apply scalar_halo_grid_upper (timeCells cellsS finalH)
    (fun k => packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k))
    Y sigma (sigma/32768) r beta ((sigma/32768)^(-zeta)) (t-W.exponent)
    hSigma rfl hr hr1 hK hAlpha hAD hYbox
  intro k hk
  obtain ⟨hkCells,hTime⟩ := mem_filter.mp hk
  obtain ⟨ik,hik,heq⟩ := mem_image.mp hkCells
  subst k
  exact hNativeWitness ik.1 ik.2 ((mem_incidences cellsS ik.1 ik.2).mp hik) hTime

end NativeRememberedFinalTimeScalarDraft2054
end -- explicit anonymous noncomputable source-unit section
