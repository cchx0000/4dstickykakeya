import Theorems.Thm_StickyKakeya4_native_incident_rank_selection
import Theorems.Thm_StickyKakeya4_native_slab_original_plane

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeCurrentGraphRankCap
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeHorizontalGrainSlice
open NativeGrainQuotientInjection NativeReferenceXYGridLinear NativeSlabPlaneFrame
open NativeIncidentAffineAnchorGeometry NativeSlabParentNormalization NativeSlabOriginalPlane
open NativeGrainHeightProjectionTransport
open scoped BigOperators Matrix.Norms.Elementwise

/-- The full matrix graph in the actual fixed physical frame. Unlike the
slab plane, this imposes no extra linear constraint on its tangent variable. -/
def graphPlane (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 2) (M : Matrix (Fin 1) (Fin 2) ℝ)
    (xi : EuclideanSpace ℝ (Fin 1)) : Submodule ℝ E4 :=
  (LinearMap.range (SlabPlanePullback.graphMap (matrixContinuous (ell:=3) M) xi)).map
    (frameEquiv P hP 3 (by norm_num) (by norm_num) hd).symm.toLinearMap

/-- Pull the displayed graph back to the original source's slope-vector
space. Both coordinate changes are explicit linear equivalences. -/
def originalGraphPlane (N : ℕ) (hN : 0 < N) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (M : Matrix (Fin 1) (Fin 2) ℝ) (xi : EuclideanSpace ℝ (Fin 1)) : Submodule ℝ E4 :=
  (graphPlane P hP hd M xi).map (parentEquiv N hN p).symm.toLinearMap

lemma originalGraphPlane_finrank (N : ℕ) (hN : 0 < N) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (M : Matrix (Fin 1) (Fin 2) ℝ) (xi : EuclideanSpace ℝ (Fin 1)) :
    Module.finrank ℝ (originalGraphPlane N hN p P hP hd M xi) = 3 := by
  rw [originalGraphPlane, LinearEquiv.finrank_map_eq, graphPlane,
    LinearEquiv.finrank_map_eq,
    LinearMap.finrank_range_of_inj (SlabPlanePullback.graphMap_injective _ _)]
  simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]

/-- Literal graph witness with the tangent coordinates of the SAME tube. -/
def graphWitness (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 2) (M : Matrix (Fin 1) (Fin 2) ℝ)
    (xi : EuclideanSpace ℝ (Fin 1)) (phi : EuclideanSpace ℝ (Fin 2)) : E4 :=
  (frameEquiv P hP 3 (by norm_num) (by norm_num) hd).symm
    (SlabPlanePullback.graphMap (matrixContinuous (ell:=3) M) xi (phi, 1))

lemma graphWitness_coordinates (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 2) (M : Matrix (Fin 1) (Fin 2) ℝ)
    (xi : EuclideanSpace ℝ (Fin 1)) (phi : EuclideanSpace ℝ (Fin 2)) :
    tangentCoordinates P 3 hd (graphWitness P hP hd M xi phi) = phi ∧
    quotientMap P hP 3 (by norm_num) (by norm_num) hd M
      (graphWitness P hP hd M xi phi) = xi ∧
    graphWitness P hP hd M xi phi (3 : Fin 4) = 1 := by
  have hh := inverse_coordinates P hP 3 (by norm_num) (by norm_num) hd
    (SlabPlanePullback.graphMap (matrixContinuous (ell:=3) M) xi (phi, 1))
  simp only [SlabPlanePullback.graphMap_apply, one_smul, matrixContinuous_apply] at hh
  refine ⟨hh.1, ?_, hh.2.2⟩
  change NativeReferenceXYGridLinear.normalCoordinates P hP 3 _ _ hd
    (graphWitness P hP hd M xi phi) -
      M.toEuclideanLin (tangentCoordinates P 3 hd (graphWitness P hP hd M xi phi)) = xi
  rw [hh.1, hh.2.1]
  abel

lemma graphWitness_mem (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 2) (M : Matrix (Fin 1) (Fin 2) ℝ)
    (xi : EuclideanSpace ℝ (Fin 1)) (phi : EuclideanSpace ℝ (Fin 2)) :
    graphWitness P hP hd M xi phi ∈ graphPlane P hP hd M xi := by
  exact Submodule.mem_map.mpr ⟨_, ⟨(phi, 1), rfl⟩, rfl⟩

/-- Same-height reconstruction costs exactly the current quotient residual.
No top-rank containment or approximate graph plane is supplied as a premise. -/
lemma graphWitness_distance (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hd : Module.finrank ℝ P = 2) (M : Matrix (Fin 1) (Fin 2) ℝ)
    (hM : ‖M‖ ≤ (1/4 : ℝ)) (xi : EuclideanSpace ℝ (Fin 1))
    (v : E4) (hv : v (3 : Fin 4) = 1) (e : ℝ)
    (hres : ‖quotientMap P hP 3 (by norm_num) (by norm_num) hd M v - xi‖ ≤ e) :
    dist v (graphWitness P hP hd M xi (tangentCoordinates P 3 hd v)) ≤ e := by
  let w := graphWitness P hP hd M xi (tangentCoordinates P 3 hd v)
  obtain ⟨hwT, hwQ, hw3⟩ := graphWitness_coordinates P hP hd M xi (tangentCoordinates P 3 hd v)
  change tangentCoordinates P 3 hd w = tangentCoordinates P 3 hd v at hwT
  change quotientMap P hP 3 (by norm_num) (by norm_num) hd M w = xi at hwQ
  change w (3 : Fin 4) = 1 at hw3
  have hdiff : v - w ∈ heightKernel := by
    change (v - w) (3 : Fin 4) = 0
    simp only [PiLp.sub_apply, hv, hw3, sub_self]
  have hh := horizontal_inverse P hP 3 (by norm_num) (by norm_num) hd M hM hdiff
  rw [map_sub, map_sub, hwT, hwQ, sub_self, norm_zero, mul_zero, zero_add] at hh
  exact (show dist v w ≤ _ by rw [dist_eq_norm]; exact hh).trans hres

theorem original_graph_infDist {n : ℕ} (D : FiniteScaleSource n)
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (M : Matrix (Fin 1) (Fin 2) ℝ) (hM : ‖M‖ ≤ (1/4 : ℝ))
    (xi : EuclideanSpace ℝ (Fin 1)) (e : ℝ)
    (hres : ‖quotientMap P hP 3 (by norm_num) (by norm_num) hd M
      (localHorizontalSlope D N p i) - xi‖ ≤ e) :
    Metric.infDist (slopeVector D i)
      (originalGraphPlane N hN p P hP hd M xi : Set E4) ≤ e / (N : ℝ) := by
  let v := parentDirection N p (slopeVector D i)
  let w := graphWitness P hP hd M xi (tangentCoordinates P 3 hd v)
  have hv : v (3 : Fin 4) = 1 := by rw [parentDirection_last, slopeVector_last]
  have hw : w (3 : Fin 4) = 1 :=
    (graphWitness_coordinates P hP hd M xi (tangentCoordinates P 3 hd v)).2.2
  have hq := (parent_coordinates D N p i P hP 3 (by norm_num) (by norm_num) hd M).2
  have hdist : dist v w ≤ e :=
    graphWitness_distance P hP hd M hM xi v hv e (by rw [hq]; exact hres)
  have hmem : (parentEquiv N hN p).symm w ∈ originalGraphPlane N hN p P hP hd M xi :=
    Submodule.mem_map.mpr ⟨w, graphWitness_mem P hP hd M xi _, rfl⟩
  apply (Metric.infDist_le_dist_of_mem hmem).trans
  have he := unparent_distance N p v w (hv.trans hw.symm)
  rw [unparent_parent N hN p] at he
  change dist (slopeVector D i) (unparentDirection N p w) ≤ _
  rw [he]
  exact div_le_div_of_nonneg_right hdist (Nat.cast_nonneg N)

/-- Restriction and the fixed/raw field readback carry the actual upstream
graph residual to a current third-stage incidence set. HasThirdXYSourceData
alone contains no offset/residual; the latter comes from its upstream affine
anchor/coherence producer and is restricted along its literal T subset S. -/
lemma current_residual_of_readback {n : ℕ} (D : FiniteScaleSource n)
    (N : ℕ) (p : Parent) (S I : Finset (Fin n × Index)) (hIS : I ⊆ S)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (raw current : Index → Matrix (Fin 1) (Fin 2) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin 1)) (e : ℝ)
    (hraw : ∀z ∈ S, ‖quotientMap P hP 3 (by norm_num) (by norm_num) hd (raw z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e)
    (hread : ∀z ∈ I, current z.2 = raw z.2) :
    ∀z ∈ I, ‖quotientMap P hP 3 (by norm_num) (by norm_num) hd (current z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e := by
  intro z hz
  rw [hread z hz]
  exact hraw z (hIS hz)

lemma pointNear_graph_eq {n : ℕ} (D : FiniteScaleSource n)
    (I : Finset (Fin n × Index)) (N : ℕ) (hN : 0 < N) (p : Parent)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (M : Index → Matrix (Fin 1) (Fin 2) ℝ) (hM : ∀k, ‖M k‖ ≤ (1/4 : ℝ))
    (xi : Index → EuclideanSpace ℝ (Fin 1)) (e r : ℝ) (her : e/(N:ℝ) ≤ r)
    (hres : ∀z ∈ I, ‖quotientMap P hP 3 (by norm_num) (by norm_num) hd (M z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e) (k : Index) :
    pointNear D I k r (originalGraphPlane N hN p P hP hd (M k) (xi k)) = pointSet I k := by
  apply filter_eq_self.mpr
  intro z hz
  obtain ⟨hzI, hzk⟩ := mem_filter.mp hz
  have hh := (original_graph_infDist D N hN p z.1 P hP hd (M z.2) (hM z.2)
    (xi z.2) e (hres z hzI)).trans her
  simpa only [hzk] using hh

/-- The displayed actual graph plane supplies rank-three admissibility at
an allowed radius above the original-scale graph error. No ambient-four
fallback and no caller-provided concentration plane enter the selection. -/
theorem point_minimal_graph_rank {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (N : ℕ) (hN : 0 < N) (p : Parent)
    (P0 : Submodule ℝ E4) (hP0 : P0 ≤ heightKernel) (hd0 : Module.finrank ℝ P0 = 2)
    (M : Index → Matrix (Fin 1) (Fin 2) ℝ) (hM : ∀k, ‖M k‖ ≤ (1/4 : ℝ))
    (xi : Index → EuclideanSpace ℝ (Fin 1)) (e : ℝ)
    (hres : ∀z ∈ E, ‖quotientMap P0 hP0 3 (by norm_num) (by norm_num) hd0 (M z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e)
    (radius : ι → ℝ) (eta : Fin 3 → ℝ) (allowed : Fin 3 → Finset ι)
    (heta : ∀ell,0 < eta ell)
    (hradius : ∀ell,∀j∈allowed ell,0 < radius j ∧ radius j ≤ 1)
    (top : ι) (htop : top ∈ allowed (2 : Fin 3))
    (hcover : e/(N:ℝ) ≤ radius top) (k : Index) :
    ∃ell : Fin 3,∃j∈allowed ell,∃P : Submodule ℝ E4,
      Module.finrank ℝ P ≤ ell.val+1 ∧
      (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointNear D E k (radius j) P).card ∧
      ∀ell' : Fin 3,ell' < ell → ∀j'∈allowed ell',∀Q : Submodule ℝ E4,
        Module.finrank ℝ Q ≤ ell'.val+1 →
        ((pointNear D E k (radius j') Q).card:ℝ) <
          (radius j')^(eta ell')*((pointSet E k).card:ℝ) := by
  let S := (univ:Finset (Fin 3)).filter (fun ell => ∃j∈allowed ell,∃P : Submodule ℝ E4,
    Module.finrank ℝ P ≤ ell.val+1 ∧
      (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointNear D E k (radius j) P).card)
  have hS : S.Nonempty := by
    refine ⟨2, mem_filter.mpr ⟨mem_univ _, top, htop,
      originalGraphPlane N hN p P0 hP0 hd0 (M k) (xi k), ?_, ?_⟩⟩
    · rw [originalGraphPlane_finrank]
      norm_num
    · rw [pointNear_graph_eq D E N hN p P0 hP0 hd0 M hM xi e (radius top) hcover hres k]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _)
        (Real.rpow_le_one (hradius 2 top htop).1.le (hradius 2 top htop).2 (heta 2).le)
  let ell := S.min' hS
  have hell : ell∈S := min'_mem S hS
  obtain ⟨j,hj,P,hP,hmass⟩ := (mem_filter.mp hell).2
  refine ⟨ell,j,hj,P,hP,hmass,?_⟩
  intro ell' hlt j' hj' Q hQ
  apply lt_of_not_ge
  intro hmass'
  have hm : ell ≤ ell' := min'_le S ell' (mem_filter.mpr ⟨mem_univ _,j',hj',Q,hQ,hmass'⟩)
  exact (not_le_of_gt hlt) hm

/-- Least-rank selection on the ORIGINAL current incidences. The common
rank/scale category is selected with point weight equal to its literal current
incidence degree; the denominator is 3 times the scale-menu cardinality.
Each surviving point has exactly its original current near-plane fiber.
All lower-rank failure statements retain that same current denominator. -/
theorem exists_current_graph_rank_retention {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E : Finset (Fin n × Index)) (hEn : E.Nonempty)
    (N : ℕ) (hN : 0 < N) (p : Parent)
    (P0 : Submodule ℝ E4) (hP0 : P0 ≤ heightKernel) (hd0 : Module.finrank ℝ P0 = 2)
    (M : Index → Matrix (Fin 1) (Fin 2) ℝ) (hM : ∀k, ‖M k‖ ≤ (1/4 : ℝ))
    (xi : Index → EuclideanSpace ℝ (Fin 1)) (e : ℝ)
    (hres : ∀z ∈ E, ‖quotientMap P0 hP0 3 (by norm_num) (by norm_num) hd0 (M z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e)
    (menu : Finset ι) (radius : ι → ℝ) (eta : Fin 3 → ℝ)
    (allowed : Fin 3 → Finset ι) (hallowed : ∀ell,allowed ell⊆menu)
    (heta : ∀ell,0 < eta ell) (hradius : ∀j∈menu,0 < radius j ∧ radius j ≤ 1)
    (top : ι) (htop : top ∈ allowed (2 : Fin 3))
    (hcover : e/(N:ℝ) ≤ radius top) :
    ∃ell : Fin 3,∃j∈allowed ell,∃F⊆E,F.Nonempty ∧
      ((radius j)^(eta ell)/(3*(menu.card:ℝ)))*(E.card:ℝ) ≤ (F.card:ℝ) ∧
      ∃P : Index → Submodule ℝ E4,
        (∀z∈F,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ radius j) ∧
        ∀k∈F.image Prod.snd,
          Module.finrank ℝ (P k) ≤ ell.val+1 ∧
          pointSet F k=pointNear D E k (radius j) (P k) ∧
          (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointSet F k).card ∧
          ∀ell' : Fin 3,ell' < ell → ∀j'∈allowed ell',∀Q : Submodule ℝ E4,
            Module.finrank ℝ Q ≤ ell'.val+1 →
            ((pointNear D E k (radius j') Q).card:ℝ) <
              (radius j')^(eta ell')*((pointSet E k).card:ℝ) := by
  have hex := fun k => point_minimal_graph_rank D E N hN p P0 hP0 hd0 M hM xi e hres
    radius eta allowed heta (fun ell j hj => hradius j (hallowed ell hj)) top htop hcover k
  choose rank scale hscale plane hdim hrich hearlier using hex
  let category : Index → Fin 3 × ι := fun k => (rank k,scale k)
  let C : Finset (Fin 3 × ι) := (univ:Finset (Fin 3)) ×ˢ menu
  have hmenu : menu.Nonempty := ⟨top, hallowed 2 htop⟩
  have hC : C.Nonempty := (univ_nonempty: (univ:Finset (Fin 3)).Nonempty).product hmenu
  obtain ⟨c,hc,hmax⟩ := exists_max_image C
    (fun c => (E.filter (fun z => category z.2=c)).card) hC
  let J := E.filter (fun z => category z.2=c)
  have hCcard : C.card=3*menu.card := by simp only [C,card_product,card_univ,Fintype.card_fin]
  have hcat : E.card ≤ J.card*C.card := by
    apply card_le_mul_card_image_of_maps_to (f:=fun z => category z.2)
    · intro z _hz
      exact mem_product.mpr ⟨mem_univ _,hallowed _ (hscale z.2)⟩
    · exact hmax
  have hJn : J.Nonempty := by
    apply card_pos.mp
    have hp := card_pos.mpr hEn
    by_contra hz
    have hz' : J.card=0 := by omega
    rw [hz',zero_mul] at hcat
    omega
  obtain ⟨z0,hz0⟩ := hJn
  have hzcat : category z0.2=c := (mem_filter.mp hz0).2
  have hj : c.2∈allowed c.1 := by
    have he : rank z0.2=c.1 := congrArg Prod.fst hzcat
    have hf : scale z0.2=c.2 := congrArg Prod.snd hzcat
    simpa only [he,hf] using hscale z0.2
  have hr : 0 < radius c.2 := (hradius c.2 (hallowed c.1 hj)).1
  have hp : 0 < (radius c.2)^(eta c.1) := Real.rpow_pos_of_pos hr _
  have hden : 0 < 3*(menu.card:ℝ) := by
    have hm : (0:ℝ) < menu.card := by exact_mod_cast card_pos.mpr hmenu
    positivity
  let F := J.filter (fun z => Metric.infDist (slopeVector D z.1) (plane z.2:Set E4) ≤ radius c.2)
  have hFJ : F⊆J := filter_subset _ _
  have hJE : J⊆E := filter_subset _ _
  have hvalue (k : Index) (hk : k∈J.image Prod.snd) : category k=c :=
    point_category_value E category c k hk
  have hcomplete (k : Index) (hk : k∈J.image Prod.snd) : pointSet J k=pointSet E k :=
    point_category_fiber E category c k (hvalue k hk)
  have hexact (k : Index) (hk : k∈J.image Prod.snd) :
      pointSet F k=pointNear D E k (radius c.2) (plane k) := by
    rw [point_filter_near]
    unfold pointNear
    rw [hcomplete k hk]
  have hret (k : Index) (hk : k∈J.image Prod.snd) :
      (radius c.2)^(eta c.1)*((pointSet E k).card:ℝ) ≤ (pointSet F k).card := by
    rw [hexact k hk]
    have he : rank k=c.1 := congrArg Prod.fst (hvalue k hk)
    have hf : scale k=c.2 := congrArg Prod.snd (hvalue k hk)
    simpa only [he,hf] using hrich k
  have hlocal := pointwise_retention_sum E J F hFJ hcomplete _ hret
  have hcatR : (E.card:ℝ) ≤ (3*(menu.card:ℝ))*(J.card:ℝ) := by
    rw [hCcard] at hcat
    exact_mod_cast (show E.card ≤ 3*menu.card*J.card by nlinarith [hcat])
  have hcross : (radius c.2)^(eta c.1)*(E.card:ℝ) ≤ (3*(menu.card:ℝ))*(F.card:ℝ) := by
    calc
      _ ≤ (radius c.2)^(eta c.1)*((3*(menu.card:ℝ))*(J.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hcatR hp.le
      _ = (3*(menu.card:ℝ))*((radius c.2)^(eta c.1)*(J.card:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal hden.le
  have hglobal : ((radius c.2)^(eta c.1)/(3*(menu.card:ℝ)))*(E.card:ℝ) ≤ (F.card:ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcross)
  have hFn : F.Nonempty := by
    apply card_pos.mp
    have he : (0:ℝ) < E.card := by exact_mod_cast card_pos.mpr hEn
    have hf : (0:ℝ) < F.card := (mul_pos (div_pos hp hden) he).trans_le hglobal
    exact_mod_cast hf
  refine ⟨c.1,c.2,hj,F,hFJ.trans hJE,hFn,hglobal,plane,?_,?_⟩
  · intro z hz
    exact (mem_filter.mp hz).2
  · intro k hk
    have hkJ := image_subset_image hFJ hk
    have he : rank k=c.1 := congrArg Prod.fst (hvalue k hkJ)
    have hd : Module.finrank ℝ (plane k) ≤ c.1.val+1 := by simpa only [he] using hdim k
    refine ⟨hd,hexact k hkJ,hret k hkJ,?_⟩
    simpa only [he] using hearlier k

/-- Angular slabs are measured by the pushforward of the literal current
incidence mass, retaining repeated direction realizers with their true weight. -/
def pointSlab {n : ℕ} (D : FiniteScaleSource n) (I : Finset (Fin n × Index))
    (N : ℕ) (p : Parent) (P0 : Submodule ℝ E4) (hd0 : Module.finrank ℝ P0 = 2)
    (k : Index) (u : EuclideanSpace ℝ (Fin 2)) (c r : ℝ) : Finset (Fin n × Index) :=
  (pointSet I k).filter (fun z =>
    |inner ℝ u (tangentCoordinates P0 3 hd0 (localHorizontalSlope D N p z.1)) - c| ≤ r)

/-- A terminal rank-three failure at a tested physical radius bounds the
actual current weighted angular slab. The constructed rank-two plane is the
one in original_point_slab_near, and the unchanged original index realizes
each slab label. The original point denominator and (2r+e)/N are explicit. -/
theorem current_slab_of_rank_two_failure {n : ℕ} (D : FiniteScaleSource n)
    (E I : Finset (Fin n × Index)) (hIE : I ⊆ E)
    (N : ℕ) (hN : 0 < N) (p : Parent)
    (P0 : Submodule ℝ E4) (hP0 : P0 ≤ heightKernel) (hd0 : Module.finrank ℝ P0 = 2)
    (M : Index → Matrix (Fin 1) (Fin 2) ℝ) (hM : ∀k, ‖M k‖ ≤ (1/4 : ℝ))
    (xi : Index → EuclideanSpace ℝ (Fin 1)) (e : ℝ)
    (hres : ∀z ∈ E, ‖quotientMap P0 hP0 3 (by norm_num) (by norm_num) hd0 (M z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e)
    (k : Index) (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1) (c r q A : ℝ)
    (hscale : (2*r+e)/(N:ℝ) ≤ q)
    (hfailed : ∀Q : Submodule ℝ E4, Module.finrank ℝ Q ≤ 2 →
      ((pointNear D E k q Q).card : ℝ) < A*((pointSet E k).card:ℝ)) :
    ((pointSlab D I N p P0 hd0 k u c r).card : ℝ) < A*((pointSet E k).card:ℝ) := by
  let Q := originalPlane N hN p P0 hP0 3 (by norm_num) (by norm_num) hd0 (M k) (xi k) u c
  obtain ⟨hQ, hnear⟩ := original_point_slab_near D N hN p E k P0 hP0 3
    (by norm_num) (by norm_num) hd0 (M k) (hM k) (xi k) u c r e hu
    (fun i hi => hres (i,k) hi)
  have hsub : pointSlab D I N p P0 hd0 k u c r ⊆ pointNear D E k q Q := by
    intro z hz
    obtain ⟨hzI, hslab⟩ := mem_filter.mp hz
    obtain ⟨hzI, hzk⟩ := mem_filter.mp hzI
    have hzE := hIE hzI
    have hpair : (z.1,k) ∈ E := by simpa only [←hzk] using hzE
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hzE,hzk⟩,
      (hnear z.1 hpair hslab).trans hscale⟩
  have hcard : ((pointSlab D I N p P0 hd0 k u c r).card : ℝ) ≤
      (pointNear D E k q Q).card := by exact_mod_cast card_le_card hsub
  exact hcard.trans_lt (hfailed Q (by change Module.finrank ℝ Q ≤ 2; exact hQ.le))

/-- Direct application to the lower-rank failure returned by the capped
selector in its stable rank-three case. No unweighted angular count or
all-width Frostman assertion is inferred from a finite scale menu. -/
theorem terminal_current_slab {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E I : Finset (Fin n × Index)) (hIE : I ⊆ E)
    (N : ℕ) (hN : 0 < N) (p : Parent)
    (P0 : Submodule ℝ E4) (hP0 : P0 ≤ heightKernel) (hd0 : Module.finrank ℝ P0 = 2)
    (M : Index → Matrix (Fin 1) (Fin 2) ℝ) (hM : ∀k, ‖M k‖ ≤ (1/4 : ℝ))
    (xi : Index → EuclideanSpace ℝ (Fin 1)) (e : ℝ)
    (hres : ∀z ∈ E, ‖quotientMap P0 hP0 3 (by norm_num) (by norm_num) hd0 (M z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e)
    (radius : ι → ℝ) (eta : Fin 3 → ℝ) (allowed : Fin 3 → Finset ι)
    (k : Index)
    (hfailed : ∀ell' : Fin 3, ell' < (2 : Fin 3) → ∀j' ∈ allowed ell',
      ∀Q : Submodule ℝ E4, Module.finrank ℝ Q ≤ ell'.val+1 →
      ((pointNear D E k (radius j') Q).card : ℝ) <
        (radius j')^(eta ell')*((pointSet E k).card:ℝ))
    (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1) (c r : ℝ)
    (test : ι) (htest : test ∈ allowed (1 : Fin 3))
    (hscale : (2*r+e)/(N:ℝ) ≤ radius test) :
    ((pointSlab D I N p P0 hd0 k u c r).card : ℝ) <
      (radius test)^(eta (1 : Fin 3))*((pointSet E k).card:ℝ) := by
  apply current_slab_of_rank_two_failure D E I hIE N hN p P0 hP0 hd0 M hM xi e hres
    k u hu c r (radius test) ((radius test)^(eta (1 : Fin 3))) hscale
  intro Q hQ
  exact hfailed 1 (by decide) test htest Q hQ

/-- The menu failure can be normalized by the retained CURRENT fiber after
paying precisely its pointwise retention factor. This is weighted angular
mass, without any reversal of a one-way angular realizer map. -/
lemma retained_slab_normalization {n : ℕ} (D : FiniteScaleSource n)
    (E I : Finset (Fin n × Index)) (N : ℕ) (p : Parent)
    (P0 : Submodule ℝ E4) (hd0 : Module.finrank ℝ P0 = 2) (k : Index)
    (u : EuclideanSpace ℝ (Fin 2)) (c r A lambda : ℝ)
    (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hret : lambda*((pointSet E k).card:ℝ) ≤ (pointSet I k).card)
    (hslab : ((pointSlab D I N p P0 hd0 k u c r).card:ℝ) <
      A*((pointSet E k).card:ℝ)) :
    ((pointSlab D I N p P0 hd0 k u c r).card:ℝ) <
      (A/lambda)*((pointSet I k).card:ℝ) := by
  apply hslab.trans_le
  have hh := mul_le_mul_of_nonneg_left hret (div_nonneg hA hlambda.le)
  calc
    A*((pointSet E k).card:ℝ) = (A/lambda)*(lambda*((pointSet E k).card:ℝ)) := by
      field_simp [hlambda.ne']
    _ ≤ _ := hh

/-- The exact price of passing from a tested menu radius q to angular width
r is displayed, including a lower-endpoint gap. In particular this lemma
does not claim the interpolation factor is bounded independently of r. -/
lemma paid_radius_interpolation {count degree q r beta : ℝ}
    (hq : 0 ≤ q) (hr : 0 < r) (H : count < q^beta*degree) :
    count < (q/r)^beta*r^beta*degree := by
  rw [Real.div_rpow hq hr.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hr beta).ne']
  exact H

/-- A selected rank cap is an exact physical rank once the actual preceding
menu radius covers the selected radius and its threshold is no larger.
This keeps the quantitative menu prerequisite visible: finite minimality at
unrelated radii alone does not prove an exact-rank assertion. -/
theorem selected_plane_rank_eq {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E I : Finset (Fin n × Index))
    (k : Index) (Q : Submodule ℝ E4) (ell previous : Fin 3)
    (hprev : previous.val+1 = ell.val)
    (radius : ι → ℝ) (eta : Fin 3 → ℝ) (allowed : Fin 3 → Finset ι)
    (j test : ι) (htest : test ∈ allowed previous)
    (hcover : radius j ≤ radius test)
    (hbudget : (radius test)^(eta previous) ≤ (radius j)^(eta ell))
    (hdim : Module.finrank ℝ Q ≤ ell.val+1)
    (hexact : pointSet I k = pointNear D E k (radius j) Q)
    (hret : (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointSet I k).card)
    (hfailed : ∀ell' : Fin 3, ell' < ell → ∀j' ∈ allowed ell',
      ∀R : Submodule ℝ E4, Module.finrank ℝ R ≤ ell'.val+1 →
      ((pointNear D E k (radius j') R).card:ℝ) <
        (radius j')^(eta ell')*((pointSet E k).card:ℝ)) :
    Module.finrank ℝ Q = ell.val+1 := by
  by_contra hne
  have hdim' : Module.finrank ℝ Q ≤ previous.val+1 := by omega
  have hp : previous < ell := by change previous.val < ell.val; omega
  have hsmall := hfailed previous hp test htest Q hdim'
  have hsub : pointNear D E k (radius j) Q ⊆ pointNear D E k (radius test) Q := by
    intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1, (mem_filter.mp hz).2.trans hcover⟩
  have hcard : ((pointSet I k).card:ℝ) ≤ (pointNear D E k (radius test) Q).card := by
    rw [hexact]
    exact_mod_cast card_le_card hsub
  have hthreshold := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (pointSet E k).card)
  exact (not_lt_of_ge (hthreshold.trans (hret.trans hcard))) hsmall

/-- Combined same-source entrance: an actual physical matrix graph creates
the rank-three fallback, selection returns the retained current incidence
mass and exact point fibers, and the stable rank-three branch immediately
returns its weighted angular slab bound at every admissible tested radius.
A rank-two outcome retains original physical near-plane fibers for the
strict branch; rank one and the stable Section20 consumer remain separate. -/
theorem exists_current_graph_rank_slab_retention {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E : Finset (Fin n × Index)) (hEn : E.Nonempty)
    (N : ℕ) (hN : 0 < N) (p : Parent)
    (P0 : Submodule ℝ E4) (hP0 : P0 ≤ heightKernel) (hd0 : Module.finrank ℝ P0 = 2)
    (M : Index → Matrix (Fin 1) (Fin 2) ℝ) (hM : ∀k, ‖M k‖ ≤ (1/4 : ℝ))
    (xi : Index → EuclideanSpace ℝ (Fin 1)) (e : ℝ)
    (hres : ∀z ∈ E, ‖quotientMap P0 hP0 3 (by norm_num) (by norm_num) hd0 (M z.2)
      (localHorizontalSlope D N p z.1) - xi z.2‖ ≤ e)
    (menu : Finset ι) (radius : ι → ℝ) (eta : Fin 3 → ℝ)
    (allowed : Fin 3 → Finset ι) (hallowed : ∀ell,allowed ell⊆menu)
    (heta : ∀ell,0 < eta ell) (hradius : ∀j∈menu,0 < radius j ∧ radius j ≤ 1)
    (top : ι) (htop : top ∈ allowed (2 : Fin 3))
    (hcover : e/(N:ℝ) ≤ radius top) :
    ∃ell : Fin 3,∃j∈allowed ell,∃F⊆E,F.Nonempty ∧
      ((radius j)^(eta ell)/(3*(menu.card:ℝ)))*(E.card:ℝ) ≤ (F.card:ℝ) ∧
      ∃P : Index → Submodule ℝ E4,
        (∀z∈F,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ radius j) ∧
        ∀k∈F.image Prod.snd,
          Module.finrank ℝ (P k) ≤ ell.val+1 ∧
          pointSet F k=pointNear D E k (radius j) (P k) ∧
          (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointSet F k).card ∧
          (∀ell' : Fin 3,ell' < ell → ∀j'∈allowed ell',∀Q : Submodule ℝ E4,
            Module.finrank ℝ Q ≤ ell'.val+1 →
            ((pointNear D E k (radius j') Q).card:ℝ) <
              (radius j')^(eta ell')*((pointSet E k).card:ℝ)) ∧
          (ell = (2 : Fin 3) →
            ∀u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀c r : ℝ,
            ∀test ∈ allowed (1 : Fin 3), (2*r+e)/(N:ℝ) ≤ radius test →
              ((pointSlab D F N p P0 hd0 k u c r).card:ℝ) <
                (radius test)^(eta (1 : Fin 3))*((pointSet E k).card:ℝ)) := by
  obtain ⟨ell,j,hj,F,hFE,hFn,hMass,Q,hNear,hPoint⟩ :=
    exists_current_graph_rank_retention D E hEn N hN p P0 hP0 hd0 M hM xi e hres
      menu radius eta allowed hallowed heta hradius top htop hcover
  refine ⟨ell,j,hj,F,hFE,hFn,hMass,Q,hNear,?_⟩
  intro k hk
  obtain ⟨hDim,hExact,hRet,hFailed⟩ := hPoint k hk
  refine ⟨hDim,hExact,hRet,hFailed,?_⟩
  intro hell u hu c r test htest hscale
  subst ell
  exact terminal_current_slab D E F hFE N hN p P0 hP0 hd0 M hM xi e hres
    radius eta allowed k hFailed u hu c r test htest hscale

end NativeCurrentGraphRankCap
