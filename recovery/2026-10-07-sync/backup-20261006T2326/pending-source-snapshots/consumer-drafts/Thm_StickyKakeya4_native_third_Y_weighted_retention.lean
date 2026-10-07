/- UNVERIFIED draft, 2026-10-06. Awaiting the fresh third-source closure. -/
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_finite_coarse_y_threshold_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeThirdYWeightedRetention
open Classical Finset StickyKakeya4 NativeJointUniformCoarseRelations
open NativeFiniteSliceHomogeneity FiniteCoarseYThresholdSelection
open NativeThirdXYSourceData NativeThirdXYData NativeActualQuotientDensity
open NativeActualQuotientSupport NativeQuotientLatticeTransport
open NativeReferenceXYGridField NativeReferenceXYGridMaps NativeReferenceXYGridPoints
open NativeReferenceXYGridSupport NativeTwoMapRetainedSliceLabels
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightFibers
open NativeHorizontalGrainSlice NativeHeightSlopeCoordinates NativeOriginalParentSelection
open NativeSpatialAngularGeometry NativeCommonCubicalMesh NativeSquaredGrainQueries NativeCubicalIncidenceCounts
open NativeGrainQuotientFibers GridQuotientAD
open scoped BigOperators Matrix.Norms.Elementwise

/-- The existing fine-label comparison converts any distinct-label selection
to an exact cross inequality for original edge mass. -/
theorem fine_label_mass_cross {A B : Type*} [DecidableEq A] [DecidableEq B]
    (I : Finset A) (f : A → B) (Q : ℕ) (HU : HasUniformFibers I Q f)
    (G : Finset B) (hG : G⊆I.image f) :
    I.card*G.card≤Q^2*(liftEdges I f G).card*(I.image f).card := by
  calc
    _ = ∑_b∈G,I.card := by simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ ∑b∈G,Q^2*(I.filter (fun z => f z=b)).card*(I.image f).card := by
      exact sum_le_sum (fun b hb => (fiber_card_average_cross I f (Q^2) HU b (hG hb)).2)
    _ = Q^2*(liftEdges I f G).card*(I.image f).card := by
      rw [liftEdges_card, mul_sum, sum_mul]

/-- An arbitrary whole-coarse-label selection. The lower and upper bounds
here concern old DISTINCT fine labels; the source theorem below derives them
from reference_cross_dense and the original tangent grid support. -/
theorem grouped_label_retention {A B Y : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq Y]
    (I : Finset A) (f : A → B) (g : B → Y) (Q : ℕ)
    (HU : HasUniformFibers I Q f) (selected : Finset Y)
    (hselected : selected⊆(I.image f).image g)
    (theta lower upper : ℝ) (htheta : 0≤theta) (hlower : 0<lower) (hupper : 0≤upper)
    (hcounts : ∀y∈(I.image f).image g,
      lower≤(((I.image f).filter (fun b => g b=y)).card:ℝ) ∧
        (((I.image f).filter (fun b => g b=y)).card:ℝ)≤upper)
    (hret : theta*((I.image f).image g).card≤(selected.card:ℝ)) :
    theta*lower*(I.card:ℝ)≤upper*(Q:ℝ)^2*(I.filter (fun a => g (f a)∈selected)).card := by
  let L := I.image f
  let G := L.filter (fun b => g b∈selected)
  have hGL : G⊆L := filter_subset _ _
  have hUpper : (L.card:ℝ)≤(L.image g).card*upper :=
    FinePointSlabGeometry.card_le_real_mul_of_fibers L (L.image g) g upper
      (fun b hb => mem_image_of_mem _ hb) (fun y hy => (hcounts y hy).2)
  have hpart : G.card=∑y∈selected,(G.filter (fun b => g b=y)).card :=
    card_eq_sum_card_fiberwise (fun b hb => (mem_filter.mp hb).2)
  have hFiber (y : Y) (hy : y∈selected) :
      G.filter (fun b => g b=y)=L.filter (fun b => g b=y) := by
    ext b
    simp only [G,mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · rintro ⟨hb,hby⟩
      exact ⟨⟨hb,by simpa only [hby] using hy⟩,hby⟩
  have hLower : lower*(selected.card:ℝ)≤(G.card:ℝ) := by
    rw [hpart,Nat.cast_sum]
    calc
      _ = ∑_y∈selected,lower := by simp only [sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro y hy
        rw [hFiber y hy]
        exact (hcounts y (hselected hy)).1
  have hFraction : theta*lower*(L.card:ℝ)≤upper*(G.card:ℝ) := by
    calc
      _ ≤ theta*lower*((L.image g).card*upper) :=
        mul_le_mul_of_nonneg_left hUpper (mul_nonneg htheta hlower.le)
      _ = upper*lower*(theta*(L.image g).card) := by ring
      _ ≤ upper*lower*(selected.card:ℝ) :=
        mul_le_mul_of_nonneg_left hret (mul_nonneg hupper hlower.le)
      _ = upper*(lower*(selected.card:ℝ)) := by ring
      _ ≤ upper*(G.card:ℝ) := mul_le_mul_of_nonneg_left hLower hupper
  have hLift : liftEdges I f G=I.filter (fun a => g (f a)∈selected) := by
    ext a
    simp only [liftEdges,G,L,mem_filter,mem_image]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · rintro ⟨ha,hg⟩
      exact ⟨ha,⟨a,ha,rfl⟩,hg⟩
  have hCross : (I.card:ℝ)*(G.card:ℝ)≤
      (Q:ℝ)^2*(I.filter (fun a => g (f a)∈selected)).card*(L.card:ℝ) := by
    have hh := fine_label_mass_cross I f Q HU G hGL
    rw [hLift] at hh
    exact_mod_cast hh
  by_cases hn : I.Nonempty
  · have hLpos : (0:ℝ)<L.card := Nat.cast_pos.mpr (hn.image f).card_pos
    apply (mul_le_mul_iff_left₀ hLpos).mp
    calc
      _ = (theta*lower*(L.card:ℝ))*(I.card:ℝ) := by ring
      _ ≤ (upper*(G.card:ℝ))*(I.card:ℝ) :=
        mul_le_mul_of_nonneg_right hFraction (Nat.cast_nonneg _)
      _ = upper*((I.card:ℝ)*(G.card:ℝ)) := by ring
      _ ≤ upper*((Q:ℝ)^2*(I.filter (fun a => g (f a)∈selected)).card*(L.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hCross hupper
      _ = _ := by ring
  · simp only [not_nonempty_iff_eq_empty.mp hn,filter_empty,card_empty,Nat.cast_zero,mul_zero]

/-- Fixing the literal height preserves complete fine-XY fibers. -/
lemma horizontal_fiber_at_height {A X Y : Type*} (T : Finset A)
    (f : A → ℤ × (X × Y)) (height : ℤ) (x : A) (hx : (f x).1=height) :
    (T.filter (fun z => (f z).1=height)).filter (fun z => (f z).2=(f x).2)=
      T.filter (fun z => f z=f x) := by
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hz,hh⟩,hxy⟩
    exact ⟨hz,Prod.ext (hh.trans hx.symm) hxy⟩
  · rintro ⟨hz,he⟩
    exact ⟨⟨hz,(congrArg Prod.fst he).trans hx⟩,congrArg Prod.snd he⟩

lemma horizontal_image_at_height {A : Type*} {k l : ℕ} (T : Finset A)
    (f : A → NativeTwoMapRetainedSliceLabels.XY k l) (height : ℤ) :
    (T.filter (fun z => (f z).1=height)).image (fun z => (f z).2)=
      productSlice (T.image f) height := by
  ext z
  simp only [productSlice,mem_image,mem_filter]
  constructor
  · rintro ⟨a,⟨ha,hh⟩,he⟩
    exact ⟨f a,⟨⟨a,ha,rfl⟩,hh⟩,he⟩
  · rintro ⟨u,⟨⟨a,ha,rfl⟩,hh⟩,he⟩
    exact ⟨a,⟨ha,hh⟩,he⟩

/-- Exact one-dimensional fine tangent capacity: N=halfWidth, not 1/rho. -/
lemma one_X_fiber_capacity {l : ℕ} (A : Finset (GridQuotientAD.Point 1 l)) (N : ℕ)
    (H : ∀z∈A,∀j,|z.1 j|≤(N:ℤ)) (y : GridQuotientAD.Lattice l) :
    (GridQuotientAD.fiber A y).card≤2*N+1 := by
  have hc : (GridQuotientAD.fiber A y).card≤(GridQuotientAD.box (0 : GridQuotientAD.Lattice 1) N).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro z hz
      apply (GridQuotientAD.mem_box_iff _ _ _).mpr
      intro j
      simpa only [Pi.zero_apply,sub_zero] using H z (mem_filter.mp hz).1 j
    · intro z hz w hw hzw
      exact Prod.ext hzw ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm)
  simpa only [GridQuotientAD.box_card,pow_one] using hc

/-- A subset supplied by the planar theorem on the literal midpoint set
pulls back to its unique old integer labels, with exactly the same counts.
No rounding or arbitrary representative is introduced by this adapter. -/
theorem literal_Y_subset {l : ℕ} (L : Finset (GridQuotientAD.Lattice l))
    (mu : ℝ) (hmu : 0<mu) (A : Finset (Fin l → ℝ))
    (hA : A⊆L.image (NativeQuotientGridCenters.center mu)) (theta : ℝ)
    (hret : theta*(L.image (NativeQuotientGridCenters.center mu)).card≤(A.card:ℝ)) :
    let selected := L.filter (fun y => NativeQuotientGridCenters.center mu y∈A)
    selected⊆L ∧ selected.image (NativeQuotientGridCenters.center mu)=A ∧
      selected.card=A.card ∧ theta*(L.card:ℝ)≤(selected.card:ℝ) := by
  intro selected
  have hImage : selected.image (NativeQuotientGridCenters.center mu)=A := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp hz).2
    · intro y hy
      obtain ⟨z,hz,hzy⟩ := mem_image.mp (hA hy)
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,by simpa only [hzy] using hy⟩,hzy⟩
  have hCard : selected.card=A.card := by
    rw [←hImage,card_image_of_injective _ (NativeQuotientGridCenters.center_injective hmu)]
  refine ⟨filter_subset _ _,hImage,hCard,?_⟩
  simpa only [card_image_of_injective _ (NativeQuotientGridCenters.center_injective hmu),hCard] using hret

/-- A chosen subset of the actual Y alphabet lifts to unchanged original
incidences. The sharp factor96 derives from N/(32 CX)≤#X≤2N+1≤3N.
The full T comparison supplies Q3², hence in particular comparison at one
height. No new core, direction selection, or resampling is performed. -/
theorem from_third_source {n d J : ℕ} (D : FiniteScaleSource n) (eta zeta a : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m level : ℕ) (hm : 12≤m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m≤level) (plane : Index → Submodule ℝ E4)
    (E Hgraph S T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (p : Parent)
    (population profileLower profileUpper : ℝ) (Qref : ℕ)
    (lambda G Cpre t : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (Hdata : HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP
      (by norm_num : 1≤2) (by norm_num : 2≤4) hd Fraw p
      population profileLower profileUpper Qref lambda G Cpre t L3 Rel CX)
    (hTI : T⊆incidences original) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let Fold := fixedField D a m 2 plane Sq Fraw
    S⊆second D a m 2 plane Sq →
    (∀x∈second D a m 2 plane Sq,Fraw (rawHeight D m x.2)=
      nodeSlope P hP 2 (by norm_num) (by norm_num) hd
        (sliceSpace (plane (spatialLabel D (2^m) x.2)))
        (slice_horizontal (plane (spatialLabel D (2^m) x.2)))) →
    (∀x∈Hgraph,parentLabel D a (2^m) x.1=p) →
    let xy := pxy D a m 2 p P hP (by norm_num) (by norm_num) hd Fold
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    ∀height : ℤ,∀selected : Finset (Fin 2 → ℤ),∀theta : ℝ,0≤theta →
    selected⊆(productSlice (T.image (fun x => xy x.2)) height).image Prod.snd →
    theta*((productSlice (T.image (fun x => xy x.2)) height).image Prod.snd).card≤selected.card →
    let Tz := T.filter (fun x => (xy x.2).1=height)
    let U := T.filter (fun x => (xy x.2).1=height ∧ (xy x.2).2.2∈selected)
    U⊆T ∧ theta*(Tz.card:ℝ)≤96*CX*(Q3:ℝ)^2*U.card ∧
      (U.image (fun x => (xy x.2).2.2)=selected) ∧
      (∀k∈U.image Prod.snd,U.filter (fun x => x.2=k)=T.filter (fun x => x.2=k)) ∧
      (∀x∈U,U.filter (fun y => xy y.2=xy x.2)=T.filter (fun y => xy y.2=xy x.2)) := by
  intro Sq Fold hpre Hread hparent xy Q3 height selected theta htheta hselected hret Tz U
  rcases Hdata.1 with ⟨hTS,hTn,_hret,hTH,_hpaid,_hcaller,_hpoint,Hxy,
    _hcoarse,_hgrain,_hkey,_hgrainLower,_href,_hAD,_hraw,hFnorm⟩
  have hpT : ∀x∈T,parentLabel D a (2^m) x.1=p := fun x hx => hparent x (hTH hx)
  have hTpre : T⊆second D a m 2 plane Sq := hTS.trans hpre
  have HX : ∀x∈T,(rho m)^(-(2-1:ℝ))≤CX*
      (referenceX D a m 2 plane T P hP (by norm_num) (by norm_num) hd (mu m)
        (referenceKey D a m 2 plane P hP (by norm_num) (by norm_num) hd (mu m) x)).card := by
    simpa only [mu_phase m (by omega)] using Hdata.2.2.1
  have hDense := reference_cross_dense D a m 2 (by omega) p plane Sq T hTpre hTn hpT
    P hP (by norm_num) (by norm_num) hd Fraw Hread CX HX
  have hC : 0<CX := hDense.1
  let N := halfWidth m
  have hN : 1≤N := halfWidth_pos m
  have hNp : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hSupport := product_support h original horiginal ha m level 2 hm hdy hf p T hTI hpT
    P hP (by norm_num) (by norm_num) hd Fold hFnorm height
  have Hfull : HasUniformFibers T Q3 (fun x => xy x.2) := by
    intro x hx y hy
    have hh := Hxy x hx y hy
    change (T.filter (fun z => encode (by norm_num : 1+2=3) (xy z.2)=encode (by norm_num) (xy x.2))).card≤
      Q3^2*(T.filter (fun z => encode (by norm_num : 1+2=3) (xy z.2)=encode (by norm_num) (xy y.2))).card at hh
    simpa only [encoded_fiber_eq] using hh
  have Hlocal : HasUniformFibers Tz Q3 (fun x => (xy x.2).2) := by
    intro x hx y hy
    rw [horizontal_fiber_at_height T (fun z => xy z.2) height x (mem_filter.mp hx).2,
      horizontal_fiber_at_height T (fun z => xy z.2) height y (mem_filter.mp hy).2]
    exact Hfull x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
  have hImage : Tz.image (fun x => (xy x.2).2)=productSlice (T.image (fun x => xy x.2)) height :=
    horizontal_image_at_height T (fun x => xy x.2) height
  have hCounts : ∀y∈(Tz.image (fun x => (xy x.2).2)).image Prod.snd,
      (N:ℝ)/(32*CX)≤(((Tz.image (fun x => (xy x.2).2)).filter (fun z => z.2=y)).card:ℝ) ∧
      (((Tz.image (fun x => (xy x.2).2)).filter (fun z => z.2=y)).card:ℝ)≤2*(N:ℝ)+1 := by
    rw [hImage]
    intro y hy
    constructor
    · have hh := hDense.2 height y hy
      have he : (1/((32:ℝ)^(2-1)*CX))*(halfWidth m:ℝ)^(2-1)=(N:ℝ)/(32*CX) := by
        dsimp only [N]
        norm_num only [pow_one]
        ring
      rw [he] at hh
      exact hh
    · exact_mod_cast one_X_fiber_capacity _ N hSupport.1 y
  have hselected' : selected⊆(Tz.image (fun x => (xy x.2).2)).image Prod.snd := by rwa [hImage]
  have hret' : theta*((Tz.image (fun x => (xy x.2).2)).image Prod.snd).card≤(selected.card:ℝ) := by
    rwa [hImage]
  have hLower : 0<(N:ℝ)/(32*CX) := div_pos hNp (by positivity)
  have hmass := grouped_label_retention Tz (fun x => (xy x.2).2) Prod.snd Q3 Hlocal selected
    hselected' theta ((N:ℝ)/(32*CX)) (2*(N:ℝ)+1) htheta hLower (by positivity) hCounts hret'
  have hUeq : Tz.filter (fun x => (xy x.2).2.2∈selected)=U := by
    ext x
    simp only [Tz,U,mem_filter,and_assoc]
  rw [hUeq] at hmass
  have hRatio : 2*(N:ℝ)+1≤96*CX*((N:ℝ)/(32*CX)) := by
    have hNr : (1:ℝ)≤N := by exact_mod_cast hN
    have he : 96*CX*((N:ℝ)/(32*CX))=3*(N:ℝ) := by field_simp [hC.ne']; ring
    rw [he]
    linarith
  have hretMass : theta*(Tz.card:ℝ)≤96*CX*(Q3:ℝ)^2*U.card := by
    apply (mul_le_mul_iff_right₀ hLower).mp
    calc
      _ = theta*((N:ℝ)/(32*CX))*(Tz.card:ℝ) := by ring
      _ ≤ (2*(N:ℝ)+1)*(Q3:ℝ)^2*U.card := hmass
      _ ≤ (96*CX*((N:ℝ)/(32*CX)))*(Q3:ℝ)^2*U.card := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRatio (sq_nonneg _)) (Nat.cast_nonneg _)
      _ = _ := by ring
  refine ⟨filter_subset _ _,hretMass,?_,?_,?_⟩
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp hx).2.2
    · intro y hy
      have hyS := hselected' hy
      obtain ⟨u,⟨x,hx,rfl⟩,hxy⟩ := mem_image.mp hyS
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨(mem_filter.mp hx).1,
        (mem_filter.mp hx).2,by simpa only [hxy] using hy⟩,hxy⟩
  · intro k hk
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    have hgood := (mem_filter.mp hz).2
    ext x
    simp only [U,mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · rintro ⟨hx,hxk⟩
      exact ⟨⟨hx,by simpa only [hxk] using hgood⟩,hxk⟩
  · intro x hx
    have hgood := (mem_filter.mp hx).2
    ext y
    simp only [U,mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · rintro ⟨hy,hyx⟩
      exact ⟨⟨hy,by simpa only [hyx] using hgood⟩,hyx⟩

end NativeThirdYWeightedRetention
