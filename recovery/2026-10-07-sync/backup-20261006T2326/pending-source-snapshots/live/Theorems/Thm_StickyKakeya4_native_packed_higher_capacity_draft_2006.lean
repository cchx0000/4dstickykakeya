/- UNVERIFIED staging source. No compiler or axiom audit has run.

Scope manifest, 2026-10-06:
1. Evaluate a fixed packed isometry on native cell CENTERS only. The native
   source, tube indices, cells, shading and measure are not rotated.
2. Derive the13^4 native-cell capacity of a joint(time,X,Y) key from equal
   floor labels, unit higher coefficients, isometry and actual grid packing.
3. Insert this derived capacity into the actual-graph population inequalities
   of the frozen draft1955. Higher X/Y lower counts remain conclusions.
4. Derive packed scalar affine transport at one original physical height,
   its explicit point-motion error, and the sigma/64 first-alignment mesh.
5. Extract scalar witnesses from a genuine NearlyLiteralAligned FULL set.

The output graph must be the actual native source-cell graph or its exact
pushforward, not a raw antecedent edge multiset. Source coefficients must be
functions of the literal source time via the already chosen old-height tag.
The keys are installed on the fixed finite g/J schedule. Later cuts retain
upper bounds but must reestablish key comparability before using lower bounds.
The actual all-radius halo/grid upper is to be read with
NativeRecodedGridUpper.actual_grid_ball_upper using the full aligned Y;
this file does not assume or conclude AD of a selected Y subset.

The frozen literal-chart draft1955 is intentionally unchanged.
-/
import Theorems.Thm_StickyKakeya4_native_actual_higher_key_population_draft_1955
import Theorems.Thm_StickyKakeya4_native_higher_quotient_parent_transport
import Theorems.Thm_StickyKakeya4_native_literal_grid_overlap
import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge
import Theorems.Thm_StickyKakeya4_native_literal_aligned_set

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
