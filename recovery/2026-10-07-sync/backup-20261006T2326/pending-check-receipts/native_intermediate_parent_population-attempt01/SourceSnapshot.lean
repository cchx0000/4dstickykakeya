/- UNVERIFIED actual second-source population and geometric fields.
The intermediate source is the literal same-Q coarse constructor. Its terminal
old-ancestor population is transferred through the actual intercept/512 map.
No second-source population, density, or native-input certificate is assumed. -/
import Theorems.Thm_StickyKakeya4_native_coarse_source_parent_readback
import Theorems.Thm_StickyKakeya4_native_actual_local_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeIntermediateParentPopulation
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeDyadicParentCells NativeCoarseSourceParentReadback
open NativeCoarseCellSource NativeUnitParentNormalization NativeLocalParentSource
open scoped ENNReal

section Coarse
variable {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
  (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
  (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
  (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^b:ℕ):ℝ) ≤
    dist (direction (D.line (rep p))) (direction (D.line (rep q))))

/-- The actual current source parent is the projected OLD ancestor of its
unchanged selected Q label. The contraction of intercepts is retained. -/
theorem parent_from_ancestor
    (hrep : ∀q∈Q,parentLabel D a (2^b) (rep q)=q)
    (ell : ℕ) (hell : ell ≤ b) (i : Fin Q.card) :
    parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 (2^ell) i =
      zeroProjection (ancestor b ell (parentIndex Q i)) := by
  rw [NativeCoarseSourceParentReadback.source_parentLabel]
  have hr := parent_ancestor_eq D a hell (rep (parentIndex Q i))
  rw [hrep _ (parentIndex_mem Q i)] at hr
  rw [hr]

/-- One complete old ancestor fiber lies in the actual current parent of
any witness in it. This compares finite indices, not just distinct old labels. -/
theorem old_fiber_card_le_current
    (hrep : ∀q∈Q,parentLabel D a (2^b) (rep q)=q)
    (ell : ℕ) (hell : ell ≤ b) (p : Parent) (i : Fin Q.card)
    (hi : parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 (2^ell) i=p) :
    (Q.filter (fun q => ancestor b ell q=ancestor b ell (parentIndex Q i))).card ≤
      ((univ : Finset (Fin Q.card)).filter (fun j =>
        parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 (2^ell) j=p)).card := by
  let I := (univ : Finset (Fin Q.card)).filter (fun j =>
    parentLabel (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 (2^ell) j=p)
  have hsub : Q.filter (fun q => ancestor b ell q=ancestor b ell (parentIndex Q i)) ⊆
      I.image (parentIndex Q) := by
    intro q hq
    have hqQ := (mem_filter.mp hq).1
    have hqr : q∈Set.range (parentIndex Q) := by rw [parentIndex_range]; exact hqQ
    obtain ⟨j,hj⟩ := hqr
    refine mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,hj⟩
    rw [parent_from_ancestor h a level b Q rep E hsep hrep ell hell j,hj,(mem_filter.mp hq).2]
    exact (parent_from_ancestor h a level b Q rep E hsep hrep ell hell i).symm.trans hi
  exact (card_le_card hsub).trans (card_image_le)

/-- The actual coarse thickness has dyadic level b-6. -/
lemma intermediate_dyadic (hb : 6 ≤ b) :
    (NativeCoarseCellSource.source h a level b Q rep E hsep).thickness=(2:ℝ)⁻¹^(b-6) := by
  rw [NativeCoarseCellSource.source_thickness,Nat.cast_pow,Nat.cast_ofNat,inv_pow]
  have hp : (2:ℝ)^b=64*(2:ℝ)^(b-6) := by
    calc
      _ = (2:ℝ)^(6+(b-6)) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num
  rw [hp]
  field_simp

/-- Q's terminal count gives every actual current parent lower population.
The target ratio includes the genuine thickness64/2^b, hence gains64 cubed. -/
theorem actual_population_lower {z1 z2 : ℝ}
    (hrep : ∀q∈Q,parentLabel D a (2^b) (rep q)=q)
    (Hterminal : ∀ell : Fin (b+1),∀q : Parent,
      (Q.filter (fun q' => ancestor b ell.val q'=q)).Nonempty →
        D.thickness^(8*z1)*(((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q' => ancestor b ell.val q'=q)).card:ℝ))
    (hpower : (64/((2^b:ℕ):ℝ))^z2 ≤ D.thickness^(8*z1)) :
    let C := NativeCoarseCellSource.source h a level b Q rep E hsep
    ∀ell : Fin ((b-6)+1),∀p : Parent,
      ((univ : Finset (Fin Q.card)).filter (fun i => parentLabel C 0 (2^ell.val) i=p)).Nonempty →
      C.thickness^z2*((1/((2^ell.val:ℕ):ℝ))/C.thickness)^3 ≤
        (((univ : Finset (Fin Q.card)).filter (fun i => parentLabel C 0 (2^ell.val) i=p)).card:ℝ) := by
  intro C ell p hp
  obtain ⟨i,hi⟩ := hp
  have hell : ell.val ≤ b := by omega
  have hq : (Q.filter (fun q => ancestor b ell.val q=ancestor b ell.val (parentIndex Q i))).Nonempty :=
    ⟨parentIndex Q i,mem_filter.mpr ⟨parentIndex_mem Q i,rfl⟩⟩
  have ht := Hterminal ⟨ell.val,by omega⟩ (ancestor b ell.val (parentIndex Q i)) hq
  have hc := old_fiber_card_le_current h a level b Q rep E hsep hrep ell.val hell p i (mem_filter.mp hi).2
  have hratio : ((1/((2^ell.val:ℕ):ℝ))/C.thickness)^3 ≤
      (((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 := by
    have he : (1/((2^ell.val:ℕ):ℝ))/C.thickness=
        (((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))/64 := by
      change (1/((2^ell.val:ℕ):ℝ))/(64/((2^b:ℕ):ℝ))= _
      field_simp
    rw [he]
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_self (by positivity) (by norm_num : (1:ℝ) ≤ 64)
  have hbase : C.thickness^z2 ≤ D.thickness^(8*z1) := hpower
  exact (mul_le_mul hbase hratio (by positivity) (Real.rpow_nonneg h.1.2.1.le _)).trans
    (ht.trans (Nat.cast_le.mpr hc))

/-- The matching upper comes directly from the intermediate native input's
actual separated directions. It does not sum a512-cubed label menu. -/
theorem actual_population_upper {etaA z2 : ℝ}
    (hb : 6 ≤ b)
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (hsmall : 5832*(64/((2^b:ℕ):ℝ))^z2 ≤ 1) :
    let C := NativeCoarseCellSource.source h a level b Q rep E hsep
    ∀ell : Fin ((b-6)+1),∀p : Parent,
      (((univ : Finset (Fin Q.card)).filter (fun i => parentLabel C 0 (2^ell.val) i=p)).card:ℝ) ≤
      C.thickness^(-z2)*((1/((2^ell.val:ℕ):ℝ))/C.thickness)^3 := by
  intro C ell p
  have hdy := intermediate_dyadic h a level b Q rep E hsep hb
  have hs : ((2^ell.val:ℕ):ℝ)*C.thickness ≤ 1 := by
    have hp : ((2^ell.val:ℕ):ℝ) ≤ ((2^(b-6):ℕ):ℝ) := by
      norm_num only [Nat.cast_pow,Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : ell.val ≤ b-6)
    exact (mul_le_mul_of_nonneg_right hp hA.1.2.1.le).trans_eq (dyadic_fine_scale hdy)
  have hh := NativeOriginalSlopeCubePacking.native_retained_parent_card_le hA univ 0 (2^ell.val)
    (by positivity) hs p
  have hcoeff : (5832:ℝ) ≤ C.thickness^(-z2) := by
    rw [Real.rpow_neg hA.1.2.1.le,←one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hA.1.2.1 z2)).mpr
    exact hsmall
  have he : 1/(((2^ell.val:ℕ):ℝ)*C.thickness)=(1/((2^ell.val:ℕ):ℝ))/C.thickness := by rw [div_div]
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

/-- Actual cubical cells of the intermediate same-Q source. -/
def intermediateCells : Fin Q.card → Finset Index := fun i =>
  NativeCoarseShadingCapacity.rows D a (2^b) (NativeCoarseDyadicShading.block level b)
    rep E (parentIndex Q i)

lemma intermediate_common_mesh (i : Fin Q.card) :
    (NativeCoarseCellSource.source h a level b Q rep E hsep).shading i =
      wzCellShading (mesh (NativeCoarseCellSource.source h a level b Q rep E hsep))
        (intermediateCells (D:=D) a level b Q rep E) i := by
  rw [NativeCoarseCellSource.source_shading]
  have hm : mesh (NativeCoarseCellSource.source h a level b Q rep E hsep)=32/((2^b:ℕ):ℝ) := by
    change (64/((2^b:ℕ):ℝ))/2=32/((2^b:ℕ):ℝ)
    ring
  rw [hm]
  rfl

/-- The literal mark of every intermediate representative has height zero. -/
lemma intermediate_common_height {etaA : ℝ}
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (i : Fin Q.card) :
    wzGraphTime ((NativeCoarseCellSource.source h a level b Q rep E hsep).line i) 0-
      mark ((NativeCoarseCellSource.source h a level b Q rep E hsep).line i) ∈
        Set.Icc (-(1/2:ℝ)) (1/2:ℝ) := by
  have hn : direction ((NativeCoarseCellSource.source h a level b Q rep E hsep).line i) (3:Fin 4) ≠ 0 := by
    have hh := hA.2.1.1 i
    linarith
  rw [wzGraphTime_sub_mark_eq _ _ hn,NativeCoarseCellSource.source_line,
    NativeContractedUnitParent.line,NativeContractedUnitParent.contractLine_center_height,
    NativeUnitParentNormalization.newLine,NativeGraphMarkedLine.center_height,zero_div]
  norm_num

/-- AD of the second source is read from the SAME intermediate native
source and Q's actual old terminal counts. No current population is an input. -/
theorem second_source_AD {etaA z1 z2 e : ℝ} (hb : 6 ≤ b) (hz2 : 0 ≤ z2)
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (hrep : ∀q∈Q,parentLabel D a (2^b) (rep q)=q)
    (Hterminal : ∀ell : Fin (b+1),∀q : Parent,
      (Q.filter (fun q' => ancestor b ell.val q'=q)).Nonempty →
        D.thickness^(8*z1)*(((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q' => ancestor b ell.val q'=q)).card:ℝ))
    (hpower : (64/((2^b:ℕ):ℝ))^z2 ≤ D.thickness^(8*z1))
    (selected : Finset (Fin Q.card × Index)) (c : ℕ) (p : Parent)
    (hbudget : (2048:ℝ)^3*(((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)^e ≤
      (64/((2^b:ℕ):ℝ))^z2) :
    let C := NativeCoarseCellSource.source h a level b Q rep E hsep
    let S := NativeLocalParentSource.source hA univ selected 0 c p
    ∀i : Fin (parentLabels C univ 0 (2^c) p).card,∀r : ℝ,
      S.thickness ≤ r → r ≤ 1 →
      (ENNReal.ofReal S.thickness).rpow e*(ENNReal.ofReal (r/S.thickness))^3 ≤
          (wzCarrierBallCount S i r:ℝ≥0∞) ∧
        (wzCarrierBallCount S i r:ℝ≥0∞) ≤
          (ENNReal.ofReal S.thickness).rpow (-e)*(ENNReal.ofReal (r/S.thickness))^3 := by
  intro C S i r hr hr1
  have H := actual_population_lower h a level b Q rep E hsep hrep Hterminal hpower
  exact NativeActualLocalAdmission.source_AD hA hz2 univ selected (b-6) c
    (intermediate_dyadic h a level b Q rep E hsep hb) p H hbudget i r hr hr1

/-- CW for the same full current parent, including infinite-volume convex
sets. Shading may occupy only one old phase component of that parent. -/
theorem second_source_CW {etaA z1 z2 e : ℝ}
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (hrep : ∀q∈Q,parentLabel D a (2^b) (rep q)=q)
    (Hterminal : ∀ell : Fin (b+1),∀q : Parent,
      (Q.filter (fun q' => ancestor b ell.val q'=q)).Nonempty →
        D.thickness^(8*z1)*(((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q' => ancestor b ell.val q'=q)).card:ℝ))
    (hpower : (64/((2^b:ℕ):ℝ))^z2 ≤ D.thickness^(8*z1))
    (selected : Finset (Fin Q.card × Index)) (c : ℕ) (hc : c ≤ b-6) (p : Parent)
    (hne : (parentLabels (NativeCoarseCellSource.source h a level b Q rep E hsep) univ 0 (2^c) p).Nonempty)
    (hbudget : (373248*512^4:ℝ)*(((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)^e ≤
      (64/((2^b:ℕ):ℝ))^(etaA+z2)) :
    let C := NativeCoarseCellSource.source h a level b Q rep E hsep
    let S := NativeLocalParentSource.source hA univ selected 0 c p
    ∀U : Set E4,Convex ℝ U →
      (wzContainedTubeCount S U:ℝ≥0∞) ≤
        (ENNReal.ofReal S.thickness).rpow (-e)*volume U*(parentLabels C univ 0 (2^c) p).card := by
  intro C S U hU
  have H := actual_population_lower h a level b Q rep E hsep hrep Hterminal hpower
  have hpop : C.thickness^z2*((1/((2^c:ℕ):ℝ))/C.thickness)^3 ≤
      ((parentLabels C univ 0 (2^c) p).card:ℝ) := by
    exact H ⟨c,by omega⟩ p hne
  exact NativeActualLocalAdmission.source_CW hA
    (intermediate_common_height h a level b Q rep E hsep hA) univ selected c p hpop hbudget U hU

/-- All geometric and cubical fields are derived for the literal second
constructor, using its actual intermediate shadow cells. Density is separate. -/
theorem second_source_geometry {etaA : ℝ} (hb : 6 ≤ b)
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (selected : Finset (Fin Q.card × Index))
    (hselected : selected⊆NativeCubicalIncidenceCounts.incidences
      (intermediateCells (D:=D) a level b Q rep E))
    (c : ℕ) (hc : c ≤ b-6) (p : Parent) :
    let S := NativeLocalParentSource.source hA univ selected 0 c p
    0 < S.thickness ∧ S.thickness ≤ 1 ∧ IsWZDyadicScale S.thickness ∧
      (∀i,IsValidLine (S.line i)) ∧ (∀i,S.line i∈fixedCompactClass) ∧
      (∀i,S.weight i=1) ∧ (∀i,S.fibreMark i=mark (S.line i)) ∧
      (∀i,MeasurableSet (S.shading i)) ∧
      (∀i,IsWZComparableCubicalShading S.thickness (S.shading i)) ∧
      (∀i,S.shading i⊆markedUnitTube (S.line i) S.thickness) ∧
      (∀i j,i≠j → S.thickness ≤ dist (direction (S.line i)) (direction (S.line j))) ∧
      HasNormalizedWZGraphSlab S ∧ HasFixedWZGraphNormalization S := by
  exact NativeLocalParentSource.source_geometric_fields hA
    (intermediateCells (D:=D) a level b Q rep E)
    (intermediate_common_mesh h a level b Q rep E hsep)
    (intermediate_common_height h a level b Q rep E hsep hA)
    univ selected hselected (b-6) c
    (intermediate_dyadic h a level b Q rep E hsep hb) hc p


/-- The full actual parent has a fixed normalized tube-count upper. The
intermediate native direction separation supplies this without a Q tax. -/
theorem second_parent_normalized_count {etaA : ℝ} (hb : 6 ≤ b)
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (c : ℕ) (hc : c ≤ b-6) (p : Parent) :
    let C := NativeCoarseCellSource.source h a level b Q rep E hsep
    ((parentLabels C univ 0 (2^c) p).card:ℝ)*(((2^c:ℕ):ℝ)*C.thickness/64)^3 ≤ 5832/64^3 := by
  intro C
  have hdy := intermediate_dyadic h a level b Q rep E hsep hb
  have hdC := hA.1.2.1
  have hN : (0:ℝ) < ((2^c:ℕ):ℝ) := by positivity
  have hs : ((2^c:ℕ):ℝ)*C.thickness ≤ 1 := by
    have hp : ((2^c:ℕ):ℝ) ≤ ((2^(b-6):ℕ):ℝ) := by
      norm_num only [Nat.cast_pow,Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hc
    exact (mul_le_mul_of_nonneg_right hp hdC.le).trans_eq (dyadic_fine_scale hdy)
  have hh := NativeOriginalSlopeCubePacking.native_retained_parent_card_le hA univ 0 (2^c)
    (by positivity) hs p
  have hscaled := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ (((2^c:ℕ):ℝ)*C.thickness/64)^3 by positivity)
  have he : (5832*(1/(((2^c:ℕ):ℝ)*C.thickness))^3)*
      (((2^c:ℕ):ℝ)*C.thickness/64)^3 = (5832:ℝ)/64^3 := by
    field_simp [hN.ne',hdC.ne']
  exact hscaled.trans_eq he

/-- Density is obtained from the remembered-height count in the ACTUAL
second cubical incidence image. No lower bound on retained old fine-edge mass
is required. The full parent remains the tube-volume denominator. -/
theorem second_source_density_from_count {etaA e L : ℝ} (hb : 6 ≤ b)
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (selected : Finset (Fin Q.card × Index))
    (hselected : selected⊆NativeCubicalIncidenceCounts.incidences
      (intermediateCells (D:=D) a level b Q rep E))
    (c : ℕ) (hc : c ≤ b-6) (p : Parent)
    (hparent : ∀z∈selected,z.1∈parentLabels
      (NativeCoarseCellSource.source h a level b Q rep E hsep) univ 0 (2^c) p)
    (hlower : L ≤
      ((selected.image (NativeLocalCellCoherence.localPair
        (NativeCoarseCellSource.source h a level b Q rep E hsep) 0 (2^c) p)).card:ℝ)*
      (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/128)^4)
    (hbudget : NativeOriginalPrunedMass.volumeConstant*(5832/64^3)*
      (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)^e ≤ L) :
    let S := NativeLocalParentSource.source hA univ selected 0 c p
    (ENNReal.ofReal S.thickness).rpow e*wzTotalTubeVolume S ≤ wzTotalShadingVolume S := by
  intro S
  let C := NativeCoarseCellSource.source h a level b Q rep E hsep
  have hg := second_source_geometry h a level b Q rep E hsep hb hA selected hselected c hc p
  have hspos : 0 < S.thickness := hg.1
  have ht := NativeActualLocalDensity.total_tube_upper S hspos hg.2.1 hg.2.2.2.1
  have htn : wzTotalTubeVolume S ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) ht
  have htr0 : (wzTotalTubeVolume S).toReal ≤
      (parentLabels C univ 0 (2^c) p).card*
        (NativeOriginalPrunedMass.volumeConstant*S.thickness^3) := by
    have hh := ENNReal.toReal_mono (by finiteness) ht
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal NativeOriginalPrunedMass.volumeConstant_pos.le,
      ENNReal.toReal_ofReal hspos.le] using hh
  have hn := second_parent_normalized_count h a level b Q rep E hsep hb hA c hc p
  have htr : (wzTotalTubeVolume S).toReal ≤ NativeOriginalPrunedMass.volumeConstant*(5832/64^3) := by
    have hh := mul_le_mul_of_nonneg_left hn NativeOriginalPrunedMass.volumeConstant_pos.le
    exact htr0.trans (by simpa only [S,C,NativeLocalParentSource.source_thickness,mul_assoc,mul_left_comm] using hh)
  have hmass := NativeLocalParentSource.source_total_shading hA univ selected 0 c p hparent
  have hsn : wzTotalShadingVolume S ≠ ⊤ := by rw [hmass]; finiteness
  have hmassReal : (wzTotalShadingVolume S).toReal =
      ((selected.image (NativeLocalCellCoherence.localPair C 0 (2^c) p)).card:ℝ)*
        (((2^c:ℕ):ℝ)*C.thickness/128)^4 := by
    rw [hmass]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (show 0 ≤ ((2^c:ℕ):ℝ)*C.thickness/128 from by
        have hdC := hA.1.2.1; positivity)]
  have hL : L ≤ (wzTotalShadingVolume S).toReal := by rw [hmassReal]; exact hlower
  have hbReal : NativeOriginalPrunedMass.volumeConstant*(5832/64^3)*S.thickness^e ≤ L := hbudget
  have hreal : S.thickness^e*(wzTotalTubeVolume S).toReal ≤ (wzTotalShadingVolume S).toReal := by
    have hh := mul_le_mul_of_nonneg_left htr (Real.rpow_pos_of_pos hspos e).le
    exact hh.trans (by simpa only [mul_comm] using hbReal.trans hL)
  have hln : (ENNReal.ofReal S.thickness).rpow e*wzTotalTubeVolume S ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · rw [ENNReal.rpow_eq_pow,ENNReal.ofReal_rpow_of_pos hspos]
      finiteness
    · exact htn
  apply (ENNReal.toReal_le_toReal hln hsn).mp
  simpa only [ENNReal.toReal_mul,ENNReal.rpow_eq_pow,ENNReal.ofReal_rpow_of_pos hspos,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hspos e).le] using hreal


end Coarse
end NativeIntermediateParentPopulation
