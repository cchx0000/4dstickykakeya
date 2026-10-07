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
import Theorems.Thm_StickyKakeya4_native_finite_slice_homogeneity
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_native_higher_quotient_parent_transport
import Theorems.Thm_StickyKakeya4_native_literal_grid_overlap
import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge
import Theorems.Thm_StickyKakeya4_native_literal_aligned_set
import Theorems.Thm_StickyKakeya4_native_recoded_grid_upper
import Theorems.Thm_StickyKakeya4_original_representative_grid_comparison

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
