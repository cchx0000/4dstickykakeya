/- Original-edge retention through the reserved literal coarse-Y relation. -/
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_finite_coarse_y_threshold_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeConfiguredYWeightedRetention
open Classical Finset StickyKakeya4 NativeJointUniformCoarseRelations
open NativeFiniteSliceHomogeneity FiniteCoarseYThresholdSelection
open NativeConfiguredThirdRelation NativeThirdXYSourceData NativeThirdXYData
open NativeReferenceXYGridField NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeCommonCubicalMesh NativeGrainQuotientFibers NativeSquaredGrainQueries
open NativeOriginalParentSelection CanonicalConfiguredE4Bridge
open scoped BigOperators Matrix.Norms.Elementwise

/-- A fraction of occupied comparable labels retains the same fraction
of original mass with the one existing Q squared loss. -/
theorem uniform_subset_retention {A B : Type*} [DecidableEq A] [DecidableEq B]
    (I : Finset A) (f : A → B) (Q : ℕ) (HU : HasUniformFibers I Q f)
    (G : Finset B) (hG : G⊆I.image f) (theta : ℝ) (_htheta : 0≤theta)
    (hret : theta*(I.image f).card≤(G.card:ℝ)) :
    theta*(I.card:ℝ)≤(Q:ℝ)^2*(liftEdges I f G).card := by
  have hCrossN : I.card*G.card≤Q^2*(liftEdges I f G).card*(I.image f).card := by
    calc
      _ = ∑_b∈G,I.card := by simp [Nat.mul_comm]
      _ ≤ ∑b∈G,Q^2*(I.filter (fun z => f z=b)).card*(I.image f).card :=
        sum_le_sum (fun b hb => (fiber_card_average_cross I f (Q^2) HU b (hG hb)).2)
      _ = _ := by rw [liftEdges_card,mul_sum,sum_mul]
  by_cases hn : I.Nonempty
  · have hL : (0:ℝ)<(I.image f).card := Nat.cast_pos.mpr (hn.image f).card_pos
    have hCross : (I.card:ℝ)*(G.card:ℝ)≤(Q:ℝ)^2*(liftEdges I f G).card*(I.image f).card := by
      exact_mod_cast hCrossN
    apply (mul_le_mul_iff_left₀ hL).mp
    calc
      _ = (theta*(I.image f).card)*(I.card:ℝ) := by ring
      _ ≤ (G.card:ℝ)*(I.card:ℝ) := mul_le_mul_of_nonneg_right hret (Nat.cast_nonneg _)
      _ = (I.card:ℝ)*(G.card:ℝ) := mul_comm _ _
      _ ≤ (Q:ℝ)^2*(liftEdges I f G).card*(I.image f).card := hCross
      _ = _ := by ring
  · simp only [not_nonempty_iff_eq_empty.mp hn,liftEdges,filter_empty,card_empty,Nat.cast_zero,mul_zero,le_refl]

/-- The subset is tested on the literal physical midpoint realization of
the actual normal-Y key. Same-height key uniformity is decoded from the full
key comparison. Every surviving original point keeps all its current edges. -/
theorem select_literal_Y {A P : Type*} [DecidableEq A] [DecidableEq P] {l : ℕ}
    (T : Finset A) (point : A → P) (key : P → ℤ × (Fin l → ℤ)) (Q : ℕ)
    (HU : HasUniformFibers T Q (key∘point))
    (base : ℝ) (hbase : 0<base) (height : ℤ)
    (selected : Finset (Fin l → ℝ)) (theta : ℝ) (htheta : 0≤theta) :
    let I := T.filter (fun z => (key (point z)).1=height)
    let y := fun z => NativeQuotientGridCenters.center base (key (point z)).2
    selected⊆I.image y → theta*(I.image y).card≤(selected.card:ℝ) →
    let U := liftEdges I y selected
    U⊆T ∧ theta*(I.card:ℝ)≤(Q:ℝ)^2*U.card ∧ U.image y=selected ∧
      (∀p∈U.image point,U.filter (fun z => point z=p)=T.filter (fun z => point z=p)) ∧
      (∀x∈U,U.filter (fun z => key (point z)=key (point x))=
        T.filter (fun z => key (point z)=key (point x))) := by
  intro I y hselected hret U
  have hI : I⊆T := filter_subset _ _
  have hFiber (x : A) (hx : x∈I) :
      I.filter (fun z => y z=y x)=T.filter (fun z => key (point z)=key (point x)) := by
    have hh := (mem_filter.mp hx).2
    ext z
    simp only [I,mem_filter]
    constructor
    · rintro ⟨⟨hz,hzheight⟩,hy⟩
      have hykey : (key (point z)).2=(key (point x)).2 :=
        NativeQuotientGridCenters.center_injective hbase hy
      exact ⟨hz,Prod.ext (hzheight.trans hh.symm) hykey⟩
    · rintro ⟨hz,hkey⟩
      refine ⟨⟨hz,(congrArg Prod.fst hkey).trans hh⟩,?_⟩
      exact congrArg (NativeQuotientGridCenters.center base) (congrArg Prod.snd hkey)
  have Hlocal : HasUniformFibers I Q y := by
    intro x hx z hz
    rw [hFiber x hx,hFiber z hz]
    exact HU x (hI hx) z (hI hz)
  have hUT : U⊆T := (liftEdges_subset I y selected).trans hI
  refine ⟨hUT,uniform_subset_retention I y Q Hlocal selected hselected theta htheta hret,
    liftEdges_image I y selected hselected,?_,?_⟩
  · intro p hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    have hxI := (mem_filter.mp hx).1
    have hxheight := (mem_filter.mp hxI).2
    have hxsel := (mem_filter.mp hx).2
    ext z
    simp only [U,liftEdges,I,mem_filter]
    constructor
    · exact fun h => ⟨h.1.1.1,h.2⟩
    · rintro ⟨hz,hpoint⟩
      exact ⟨⟨⟨hz,by simpa only [hpoint] using hxheight⟩,
        by simpa only [y,hpoint] using hxsel⟩,hpoint⟩
  · intro x hx
    have hxI := (mem_filter.mp hx).1
    have hxheight := (mem_filter.mp hxI).2
    have hxsel := (mem_filter.mp hx).2
    ext z
    simp only [U,liftEdges,I,mem_filter]
    constructor
    · exact fun h => ⟨h.1.1.1,h.2⟩
    · rintro ⟨hz,hkey⟩
      exact ⟨⟨⟨hz,by simpa only [hkey] using hxheight⟩,
        by simpa only [y,hkey] using hxsel⟩,hkey⟩

/-- Actual rank-two source caller. The coarse-Y relation was installed
before this T was chosen. The existing third record supplies the comparison;
the chosen planar subset supplies only its own literal cardinal retention.
The physical base is mu*R/512; no fine-base alignment is substituted. -/
theorem from_source_data {n d J : ℕ} (D : FiniteScaleSource n) (zeta a : ℝ) (m : ℕ)
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (p : Parent)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre t : ℝ) (L3 : ℕ)
    (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (R : ℕ) (hR : 0<R)
    (Hdata :
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
        (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
      let F := fixedField D a m 2 plane Sq Fraw
      HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP
        (by norm_num : 1≤2) (by norm_num : 2≤4) hd Fraw p
        population PL PU Qref lambda G Cpre t L3
        (NativeConfiguredThirdRelation.relations D a m p .oneTwo P hP hd F Fcfg R extra) CX) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    let key := coarseYKey D a m p .oneTwo P hP hd F Fcfg R
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let base := (mu m*(R:ℝ))/512
    ∀height : ℤ,∀selected : Finset (Fin 2 → ℝ),∀theta : ℝ,0≤theta →
    let I := T.filter (fun z => (key z.2).1=height)
    let y := fun z : Fin n × Index => NativeQuotientGridCenters.center base (key z.2).2
    selected⊆I.image y → theta*(I.image y).card≤(selected.card:ℝ) →
    let U := liftEdges I y selected
    U⊆T ∧ theta*(I.card:ℝ)≤(Q3:ℝ)^2*U.card ∧ U.image y=selected ∧
      (∀k∈U.image Prod.snd,U.filter (fun z => z.2=k)=T.filter (fun z => z.2=k)) ∧
      (∀x∈U,U.filter (fun z => key z.2=key x.2)=T.filter (fun z => key z.2=key x.2)) := by
  intro Sq F key Q3 base height selected theta htheta I y hselected hret U
  have Hrel := Hdata.1.2.2.2.2.2.1
  have HU := caller_coarseY_uniformity D a m p .oneTwo P hP hd F Fcfg R extra T Q3 Hrel
  have hbase : 0<base := by
    dsimp only [base]
    exact div_pos (mul_pos (mu_pos m) (by exact_mod_cast hR)) (by norm_num)
  exact select_literal_Y T Prod.snd key Q3 HU base hbase height selected theta htheta hselected hret

end NativeConfiguredYWeightedRetention
