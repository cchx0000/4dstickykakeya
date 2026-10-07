/- UNVERIFIED raw original-incidence alternative. No compiler run.
This source is separate from the checked baseline and frozen89.
The raw mass is delta*r^3 times the cardinal of ORIGINAL (tube,cell)
incidences. Neither epsilon^4 graph mass nor deduplicated sourceCells mass
is substituted. Fixed original k3 is finer than translatedHeight.
-/
import Theorems.Thm_StickyKakeya4_native_padded_cell_fiber_count
import Theorems.Thm_StickyKakeya4_native_relative_coarse_point_menu
import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
import Theorems.Thm_StickyKakeya4_native_active_phase_population
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRawIncidenceHeightPopulationDraft2123
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativePaddedCellFiberCount NativeRelativeParentProfiles NativeLocalParentSource
open NativeRelativeParentLabels NativeRelativeCoarsePointMenu NativeRelativeCoarseGeometry
open NativeSameReferenceChartBounds NativeMiddleWindowBalance NativeActivePhasePopulation
open NativeTangentGridCoarsening
open scoped ENNReal BigOperators

/-- The actual original-height alphabet incurs the established fixed row
capacity; translating a height index does not change its fiber. -/
theorem original_height_row_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i : Fin n) (t : ℤ) : ((original i).filter (fun k => k 3=t)).card≤21952 := by
  have he : (original i).filter (fun k => k 3=t)=
      (original i).filter (fun k => k 3-shift D a=t-shift D a) := by
    ext k
    simp only [mem_filter]
    constructor <;> rintro ⟨hk,ht⟩ <;> exact ⟨hk,by omega⟩
  rw [he]
  exact original_row_card_le h original horiginal ha i (t-shift D a)

/-- The first literal local-cell floor inside the actual coarse shadow. -/
theorem rounded_height_readback {n : ℕ} {D : FiniteScaleSource n}
    (hdelta : 0<D.thickness) (a : ℝ) (N : ℕ) (hN : 0<N) (p : Parent)
    (i : Fin n) (k : Index) :
    roundedHeight D a N p i k=((N:ℝ)*D.thickness/128)*
      ((((k 3-shift D a)/(8*N:ℕ):ℤ):ℝ)+1/2) := by
  unfold roundedHeight cellCenter localMesh
  rw [NativeLocalParentCells.cellLabel_height hdelta a N hN p i k]

/-- Exact height of the same doubleLabel used by actualRows. -/
theorem double_label_height {n : ℕ} {D : FiniteScaleSource n}
    (hdelta : 0<D.thickness) (a : ℝ) (N M : ℕ) (hN : 0<N) (hM : 0<M)
    (p : Parent) (j i : Fin n) (k : Index) :
    doubleLabel D a N M p j i k 3=
      ⌊((((N:ℝ)*D.thickness/64)/(512*(64/(M:ℝ))))*
        ((((k 3-shift D a)/(8*N:ℕ):ℤ):ℝ)+1/2)⌋ := by
  change ⌊doubleFront D a N p j i k 3/(32/(M:ℝ))⌋=_
  change ⌊(roundedHeight D a N p i k/512)/(32/(M:ℝ))⌋=_
  rw [rounded_height_readback hdelta a N hN p i k]
  have hMr : (M:ℝ)≠0 := by exact_mod_cast hM.ne'
  congr 1
  field_simp [hMr]
  <;> ring

/-- The actual shadow time differs from the original integer center time
only by the proved first local-cell rounding, not by a new point choice. -/
theorem double_front_time_error {n : ℕ} {D : FiniteScaleSource n}
    (hdelta : 0<D.thickness) (a : ℝ) (N : ℕ) (hN : 0<N)
    (p : Parent) (j i : Fin n) (k : Index) :
    |doubleFront D a N p j i k 3-
      D.thickness*((k 3:ℝ)-(shift D a:ℝ)+1/2)/524288|≤
        (((N:ℝ)*D.thickness/64)/2048) := by
  have hh := rounded_height_error hdelta a N hN p i k
  have hFront : NativeLocalParentCells.frontPoint D a N p i k 3=
      D.thickness*((k 3:ℝ)-(shift D a:ℝ)+1/2)/1024 := by
    rw [NativeLocalParentCells.frontPoint_height]
    dsimp [NativeOriginalPaddedCells.oldTime,ShearBinFibers.oldCenter,chartIndex,mesh]
    push_cast
    ring
  rw [hFront] at hh
  have he : doubleFront D a N p j i k 3-
      D.thickness*((k 3:ℝ)-(shift D a:ℝ)+1/2)/524288=
    (roundedHeight D a N p i k-
      D.thickness*((k 3:ℝ)-(shift D a:ℝ)+1/2)/1024)/512 := by
    change roundedHeight D a N p i k/512-_= _
    ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ)≤512)).trans_eq (by
    unfold localMesh
    ring)

/-- Integer-time population from a literal scalar interval and an actual
forward error. This counts ORIGINAL height labels, not configured times. -/
theorem integer_time_interval_card {X : Type*} (V : Finset X) (height : X → ℤ)
    (time : X → ℝ) (scale offset error left width : ℝ)
    (hs : 0<scale) (hE : 0≤error) (hW : 0≤width)
    (hNear : ∀v∈V,|scale*(height v:ℝ)+offset-time v|≤error)
    (hWindow : ∀v∈V,left≤time v ∧ time v≤left+width) :
    ((V.image height).card:ℝ)≤(width+2*error)/scale+2 := by
  have hInterval : ∀v∈V,(left-error-offset)/scale≤(height v:ℝ) ∧
      (height v:ℝ)≤(left-error-offset)/scale+(width+2*error)/scale := by
    intro v hv
    have he := abs_le.mp (hNear v hv)
    have hw := hWindow v hv
    constructor
    · apply (div_le_iff₀ hs).mpr
      nlinarith only [he.1,hw.1]
    · rw [←add_div]
      apply (le_div_iff₀ hs).mpr
      nlinarith only [he.2,hw.2]
  have hc := scalar_interval_grid_card V (fun v => (height v:ℝ))
    (r:=1) (by norm_num) (show 0≤(width+2*error)/scale by positivity) hInterval
  simpa only [scalarCells,div_one,Int.floor_intCast] using hc


/-- Per coarse shadow time-cell, count original k3 directly through the
actual doubleFront formula. The original tube/representative maps may vary;
there is no separated configured-point premise. -/
theorem coarse_shadow_original_height_count {X : Type*} {n : ℕ} {D : FiniteScaleSource n}
    (hdelta : 0<D.thickness) (a : ℝ) (N M : ℕ) (hN : 0<N) (hM : 0<M)
    (p : Parent) (V : Finset X) (cell : X → Index) (tube rep : X → Fin n)
    (hFine : D.thickness≤(N:ℝ)*D.thickness/64)
    (hScale : (N:ℝ)*D.thickness/64≤64/(M:ℝ))
    (q : ℤ) (hShadow : ∀v∈V,doubleLabel D a N M p (rep v) (tube v) (cell v) 3=q) :
    ((V.image (fun v => cell v 3)).card:ℝ)≤1048576*(64/(M:ℝ))/D.thickness := by
  let r := (N:ℝ)*D.thickness/64
  let d := 64/(M:ℝ)
  let time := fun v => doubleFront D a N p (rep v) (tube v) (cell v) 3
  have hd : 0<d := by dsimp [d]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hNear : ∀v∈V,|(D.thickness/524288)*(cell v 3:ℝ)+
      D.thickness*(-(shift D a:ℝ)+1/2)/524288-time v|≤r/2048 := by
    intro v _hv
    have hh := double_front_time_error hdelta a N hN p (rep v) (tube v) (cell v)
    rw [abs_sub_comm] at hh
    convert hh using 1 <;> dsimp only [r,time] <;> ring
  have hWindow : ∀v∈V,(d/2)*(q:ℝ)≤time v ∧ time v≤(d/2)*(q:ℝ)+d/2 := by
    intro v hv
    apply coarse_floor_interval (half_pos hd)
    change ⌊time v/(d/2)⌋=q
    have hh := hShadow v hv
    change ⌊time v/(32/(M:ℝ))⌋=q at hh
    convert hh using 1 <;> dsimp only [d] <;> ring
  have hh := integer_time_interval_card V (fun v => cell v 3) time
    (D.thickness/524288) (D.thickness*(-(shift D a:ℝ)+1/2)/524288)
    (r/2048) ((d/2)*(q:ℝ)) (d/2) (by positivity) (by positivity) (by positivity) hNear hWindow
  have he : ((d/2+2*(r/2048))/(D.thickness/524288)+2)*D.thickness=
      262144*d+512*r+2*D.thickness := by field_simp [hdelta.ne'] <;> ring
  have hc := mul_le_mul_of_nonneg_right hh hdelta.le
  rw [he] at hc
  apply (le_div_iff₀ hdelta).mpr
  change _≤1048576*d
  nlinarith only [hc,hFine,hScale,hd]

/-- The FINAL local time label retains its exact actual integer division.
The third coordinate of the coarse shadow is not renamed an old height. -/
theorem final_time_original_height_count {X : Type*} {n nC : ℕ} {D : FiniteScaleSource n}
    (hdelta : 0<D.thickness) (a : ℝ) (N M L : ℕ) (hN : 0<N) (hM : 0<M) (hL : 0<L)
    (p : Parent) (C : FiniteScaleSource nC) (hC : C.thickness=64/(M:ℝ)) (pA : Parent)
    (V : Finset X) (cell : X → Index) (tube rep : X → Fin n) (midTube : X → Fin nC)
    (hFine : D.thickness≤(N:ℝ)*D.thickness/64)
    (hScale : (N:ℝ)*D.thickness/64≤64/(M:ℝ))
    (hSigma : 64/(M:ℝ)≤(L:ℝ)*(64/(M:ℝ))/64)
    (q : ℤ) (hFinal : ∀v∈V,NativeLocalParentCells.cellLabel C 0 L pA (midTube v)
      (doubleLabel D a N M p (rep v) (tube v) (cell v)) 3=q) :
    ((V.image (fun v => cell v 3)).card:ℝ)≤
      268435456*((L:ℝ)*(64/(M:ℝ))/64)/D.thickness := by
  let r := (N:ℝ)*D.thickness/64
  let d := 64/(M:ℝ)
  let sigma := (L:ℝ)*d/64
  let time := fun v => doubleFront D a N p (rep v) (tube v) (cell v) 3
  have hd : 0<d := by dsimp [d]; positivity
  have hr : 0<r := by dsimp [r]; positivity
  have hs : 0<sigma := by dsimp [sigma]; positivity
  have hCpos : 0<C.thickness := by rw [hC]; exact hd
  have hNear : ∀v∈V,|(D.thickness/524288)*(cell v 3:ℝ)+
      D.thickness*(-(shift D a:ℝ)+1/2)/524288-time v|≤r/2048 := by
    intro v _hv
    have hh := double_front_time_error hdelta a N hN p (rep v) (tube v) (cell v)
    rw [abs_sub_comm] at hh
    convert hh using 1 <;> dsimp only [r,time] <;> ring
  have hWindow : ∀v∈V,256*sigma*(q:ℝ)≤time v ∧ time v≤256*sigma*(q:ℝ)+256*sigma := by
    intro v hv
    let k := doubleLabel D a N M p (rep v) (tube v) (cell v)
    have hq := hFinal v hv
    rw [NativeLocalParentCells.cellLabel_height hCpos 0 L hL pA (midTube v) k] at hq
    simp only [shift,zero_div,Int.floor_zero,sub_zero] at hq
    have hLz : (0:ℤ)<(8*L:ℕ) := by positivity
    have hlo := (Int.le_ediv_iff_mul_le hLz).mp hq.ge
    have hhi := (Int.ediv_lt_iff_lt_mul hLz).mp (show k 3/(8*L:ℕ)<q+1 by omega)
    have hloR : (q:ℝ)*(8*(L:ℝ))≤(k 3:ℝ) := by exact_mod_cast hlo
    have hhiR : (k 3:ℝ)+1≤8*(L:ℝ)*((q:ℝ)+1) := by
      have hh' : k 3+1≤(q+1)*(8*L:ℕ) := by omega
      have hh : k 3+1≤(8*L:ℕ)*(q+1) := by simpa only [mul_comm] using hh'
      exact_mod_cast hh
    have hfloor : ⌊time v/(d/2)⌋=k 3 := by
      change ⌊time v/(d/2)⌋=⌊time v/(32/(M:ℝ))⌋
      congr 2
      dsimp only [d]
      ring
    have htime := coarse_floor_interval (half_pos hd) hfloor
    have hloTime := mul_le_mul_of_nonneg_left hloR (half_pos hd).le
    have hhiTime := mul_le_mul_of_nonneg_left hhiR (half_pos hd).le
    dsimp only [sigma]
    constructor <;> nlinarith only [htime.1,htime.2,hloTime,hhiTime]
  have hh := integer_time_interval_card V (fun v => cell v 3) time
    (D.thickness/524288) (D.thickness*(-(shift D a:ℝ)+1/2)/524288)
    (r/2048) (256*sigma*(q:ℝ)) (256*sigma) (by positivity) (by positivity) (by positivity) hNear hWindow
  have he : ((256*sigma+2*(r/2048))/(D.thickness/524288)+2)*D.thickness=
      134217728*sigma+512*r+2*D.thickness := by field_simp [hdelta.ne'] <;> ring
  have hc := mul_le_mul_of_nonneg_right hh hdelta.le
  rw [he] at hc
  apply (le_div_iff₀ hdelta).mpr
  change _≤268435456*sigma
  nlinarith only [hc,hFine,hScale,hSigma,hs]

/-- HB is read at the original product depth m+b before the admitted local
source's native exponent p is used. Empty atoms need no occupancy premise. -/
theorem relative_atom_population_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta a zeta pExp : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hmb : m+b≤level) (p q : Parent)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp≤D.thickness^zeta) :
    ((relativeAtom D R a (2^m) p (2^b) q).card:ℝ)≤
      (source h R Eref a m p).thickness^(-pExp)*
        ((64/((2^b:ℕ):ℝ))/(64*(source h R Eref a m p).thickness))^3 := by
  let Sref := source h R Eref a m p
  rw [←source_parent_population h R Eref a m p (2^b) q]
  by_cases hq : (NativeOriginalParentSelection.backbone Sref 0 (2^b) q).Nonempty
  · have H := population_through h original R level HB Eref m b hmb p hbudget
    have hu := (H ⟨b,by omega⟩ q hq).2
    convert hu using 1 <;> ring
  · rw [not_nonempty_iff_eq_empty.mp hq,card_empty,Nat.cast_zero]
    positivity

/-- This is a count of unchanged ORIGINAL incidences at a true original
height and in a true old tube atom. No geometric pair quotient is taken. -/
theorem original_height_atom_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (tubes : Finset (Fin n)) (hTube : ∀z∈A,z.1∈tubes)
    (t : ℤ) (hHeight : ∀z∈A,z.2 3=t) : A.card≤21952*tubes.card := by
  have hFiber : ∀i∈tubes,(A.filter (fun z => z.1=i)).card≤21952 := by
    intro i _hi
    let F := A.filter (fun z => z.1=i)
    have hInj : Set.InjOn Prod.snd (F:Set (Fin n × Index)) := by
      intro x hx y hy hxy
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hxy
    have hSub : F.image Prod.snd⊆(original i).filter (fun k => k 3=t) := by
      intro k hk
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
      obtain ⟨hzA,hzi⟩ := mem_filter.mp hz
      have ho := (mem_incidences original z.1 z.2).mp (hA hzA)
      rw [hzi] at ho
      exact mem_filter.mpr ⟨ho,hHeight z hzA⟩
    rw [←card_image_iff.mpr hInj]
    exact (card_le_card hSub).trans (original_height_row_card h original horiginal ha i t)
  have hh := card_le_mul_card_image_of_maps_to hTube 21952 hFiber
  simpa only [Nat.mul_comm] using hh

/-- Actual original incidences mapping to one coarse shadow cell are
bounded by tube count times the derived original time-row interval. Even
only equality of the third shadow coordinate suffices for this upper. -/
theorem coarse_shadow_original_incidence_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N M : ℕ) (hN : 0<N) (hM : 0<M) (p : Parent)
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (tubes : Finset (Fin n)) (hTube : ∀z∈A,z.1∈tubes) (rep : (Fin n × Index) → Fin n)
    (hFine : D.thickness≤(N:ℝ)*D.thickness/64)
    (hScale : (N:ℝ)*D.thickness/64≤64/(M:ℝ))
    (q : ℤ) (hShadow : ∀z∈A,doubleLabel D a N M p (rep z) z.1 z.2 3=q) :
    D.thickness*(A.card:ℝ)≤(21952*1048576:ℝ)*(64/(M:ℝ))*(tubes.card:ℝ) := by
  have hEach : ∀t∈A.image (fun z => z.2 3),
      (((A.filter (fun z => z.2 3=t)).image id).card:ℝ)≤21952*(tubes.card:ℝ) := by
    intro t _ht
    have hh := original_height_atom_capacity h original horiginal ha
      (A.filter (fun z => z.2 3=t)) ((filter_subset _ _).trans hA)
      tubes (fun z hz => hTube z (mem_filter.mp hz).1) t (fun z hz => (mem_filter.mp hz).2)
    simpa only [image_id',Nat.cast_mul,Nat.cast_ofNat] using (Nat.cast_le.mpr hh :
      ((A.filter (fun z => z.2 3=t)).card:ℝ)≤((21952*tubes.card:ℕ):ℝ))
  have hCount := image_card_le_real_mul_of_fiber_images A id (fun z => z.2 3)
    (21952*(tubes.card:ℝ)) hEach
  simp only [image_id'] at hCount
  have hHeights := coarse_shadow_original_height_count h.1.2.1 a N M hN hM p A
    Prod.snd Prod.fst rep hFine hScale q hShadow
  have hh := hCount.trans (mul_le_mul_of_nonneg_left hHeights (by positivity))
  have hscale := mul_le_mul_of_nonneg_left hh h.1.2.1.le
  have he : D.thickness*((21952*(tubes.card:ℝ))*(1048576*(64/(M:ℝ))/D.thickness))=
      (21952*1048576:ℝ)*(64/(M:ℝ))*(tubes.card:ℝ) := by field_simp [h.1.2.1.ne'] <;> ring
  exact hscale.trans_eq he

/-- Full tube-volume upper bounds supply raw W(q), with no per-tube density
lower and no packing assertion about retained point labels. -/
theorem raw_atom_mass_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (tubes : Finset (Fin n)) (hTube : ∀z∈A,z.1∈tubes) :
    D.thickness*A.card≤rowConstant*tubes.card := by
  have hs : A⊆retained original tubes := fun z hz => mem_filter.mpr ⟨hA hz,hTube z hz⟩
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hs)) h.1.2.1.le).trans
    (retained_incidence_capacity h original horiginal tubes)

/-- Source-facing joins for all three raw capacities. The same original
A is used throughout. nu=delta*r^3, d=64/2^b, and the HB power is paid before
these formulas. In particular87808 is an actual coarse-shadow capacity. -/
theorem actual_relative_raw_capacities {n : ℕ} {D : FiniteScaleSource n}
    {eta a zeta pExp : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hm : 6≤m) (hmb : m+b≤level) (p q : Parent)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp≤D.thickness^zeta) :
    let r := (source h R Eref a m p).thickness
    let d := 64/((2^b:ℕ):ℝ)
    let tubes := relativeAtom D R a (2^m) p (2^b) q
    let nu := D.thickness*r^3
    (∀(A : Finset (Fin n × Index)),A⊆incidences original →
      (∀z∈A,z.1∈tubes) → ∀t : ℤ,(∀z∈A,z.2 3=t) →
      (A.card:ℝ)≤r^(-pExp)*(d/r)^3) ∧
    (∀(A : Finset (Fin n × Index)),A⊆incidences original →
      (∀z∈A,z.1∈tubes) →
      nu*(A.card:ℝ)≤(rowConstant/64^3)*r^(-pExp)*d^3) ∧
    (∀(A : Finset (Fin n × Index)),A⊆incidences original →
      (∀z∈A,z.1∈tubes) → ∀rep : (Fin n × Index) → Fin n,∀t : ℤ,
      (∀z∈A,doubleLabel D a (2^m) (2^b) p (rep z) z.1 z.2 3=t) →
      nu*(A.card:ℝ)≤87808*r^(-pExp)*d^4) := by
  intro r d tubes nu
  have hr : 0<r := by change 0<((2^m:ℕ):ℝ)*D.thickness/64; have hh:=h.1.2.1; positivity
  have hd : 0<d := by dsimp only [d]; positivity
  have hUpper := relative_atom_population_upper h original R level HB Eref m b hmb p q hbudget
  have hN64 : (64:ℝ)≤((2^m:ℕ):ℝ) := by
    have hh := Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hm
    norm_num at hh
    exact_mod_cast hh
  have hFine : D.thickness≤((2^m:ℕ):ℝ)*D.thickness/64 := by
    have hh := mul_le_mul_of_nonneg_right hN64 h.1.2.1.le
    linarith only [hh]
  have hGuard := source_scale_guard (a:=a) h R Eref level m b p HB.2.1 hmb
  have hScale : ((2^m:ℕ):ℝ)*D.thickness/64≤64/((2^b:ℕ):ℝ) := by
    apply (le_div_iff₀ (show (0:ℝ)<((2^b:ℕ):ℝ) by positivity)).mpr
    change ((2^b:ℕ):ℝ)*r≤1 at hGuard
    change r*((2^b:ℕ):ℝ)≤64
    nlinarith only [hGuard]
  constructor
  · intro A hA hTube t hHeight
    have hh := original_height_atom_capacity h original HB.1 HB.2.2.1 A hA tubes hTube t hHeight
    have hc : (A.card:ℝ)≤21952*(tubes.card:ℝ) := by exact_mod_cast hh
    have hu := hc.trans (mul_le_mul_of_nonneg_left hUpper (by norm_num : (0:ℝ)≤21952))
    have he : 21952*(r^(-pExp)*(d/(64*r))^3)=
        ((21952:ℝ)/64^3)*(r^(-pExp)*(d/r)^3) := by field_simp [hr.ne'] <;> ring
    rw [he] at hu
    exact hu.trans (by
      have hz : 0≤r^(-pExp)*(d/r)^3 := by positivity
      exact (mul_le_mul_of_nonneg_right (by norm_num : (21952:ℝ)/64^3≤1) hz).trans_eq (one_mul _))
  · constructor
    · intro A hA hTube
      have hh := raw_atom_mass_upper h original HB.1 A hA tubes hTube
      have hc := mul_le_mul_of_nonneg_left hh (pow_nonneg hr.le 3)
      have hu := mul_le_mul_of_nonneg_left hUpper (show 0≤r^3*rowConstant by
        exact mul_nonneg (pow_nonneg hr.le 3) rowConstant_pos.le)
      calc
        nu*(A.card:ℝ) = r^3*(D.thickness*A.card) := by dsimp only [nu]; ring
        _ ≤ r^3*(rowConstant*tubes.card) := hc
        _ = (r^3*rowConstant)*(tubes.card:ℝ) := by ring
        _ ≤ (r^3*rowConstant)*(r^(-pExp)*(d/(64*r))^3) := hu
        _ = (rowConstant/64^3)*r^(-pExp)*d^3 := by field_simp [hr.ne'] <;> ring
    · intro A hA hTube rep t hShadow
      have hh := coarse_shadow_original_incidence_capacity h original HB.1 HB.2.2.1
        (2^m) (2^b) (by positivity) (by positivity) p A hA tubes hTube rep hFine hScale t hShadow
      have hc := mul_le_mul_of_nonneg_left hh (pow_nonneg hr.le 3)
      have hu := mul_le_mul_of_nonneg_left hUpper (show 0≤r^3*(21952*1048576:ℝ)*d by positivity)
      calc
        nu*(A.card:ℝ) = r^3*(D.thickness*A.card) := by dsimp only [nu]; ring
        _ ≤ r^3*((21952*1048576:ℝ)*d*tubes.card) := hc
        _ = (r^3*(21952*1048576:ℝ)*d)*(tubes.card:ℝ) := by ring
        _ ≤ (r^3*(21952*1048576:ℝ)*d)*(r^(-pExp)*(d/(64*r))^3) := hu
        _ = 87808*r^(-pExp)*d^4 := by field_simp [hr.ne'] <;> ring

end NativeRawIncidenceHeightPopulationDraft2123
