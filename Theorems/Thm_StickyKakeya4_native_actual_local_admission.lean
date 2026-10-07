import Theorems.Thm_StickyKakeya4_native_local_parent_source_counts
import Theorems.Thm_StickyKakeya4_native_local_parent_cw
import Theorems.Thm_StickyKakeya4_native_original_parent_density_core
import Theorems.Thm_StickyKakeya4_native_local_admission_budget
import Theorems.Thm_StickyKakeya4_native_actual_local_density
import Theorems.Thm_StickyKakeya4_native_local_parent_multiplicity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeActualLocalAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeOriginalParentDensityCore
open NativeUnitParentNormalization
open scoped ENNReal BigOperators

lemma real_AD_to_enn {eps r e : ℝ} (heps : 0 < eps) (hr : 0 ≤ r) (k : ℕ)
    (hl : eps^e*(r/eps)^3 ≤ (k:ℝ)) (hu : (k:ℝ) ≤ eps^(-e)*(r/eps)^3) :
    (ENNReal.ofReal eps).rpow e*(ENNReal.ofReal (r/eps))^3 ≤ (k:ℝ≥0∞) ∧
      (k:ℝ≥0∞) ≤ (ENNReal.ofReal eps).rpow (-e)*(ENNReal.ofReal (r/eps))^3 := by
  constructor
  · simpa only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos heps e).le,
      ENNReal.ofReal_rpow_of_pos heps,ENNReal.rpow_eq_pow,
      ENNReal.ofReal_pow (div_nonneg hr heps.le),ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hl
  · simpa only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos heps (-e)).le,
      ENNReal.ofReal_rpow_of_pos heps,ENNReal.rpow_eq_pow,
      ENNReal.ofReal_pow (div_nonneg hr heps.le),ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hu

/-- Scalar inversion used only after a source-derived budget is available. -/
lemma negative_coefficient {delta eps e beta C : ℝ}
    (hd : 0 < delta) (heps : 0 < eps)
    (hb : C * eps^e ≤ delta^beta) :
    C * delta^(-beta) ≤ eps^(-e) := by
  rw [Real.rpow_neg hd.le, Real.rpow_neg heps.le, ←div_eq_mul_inv, ←one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos heps e)).mpr
  rw [div_mul_eq_mul_div]
  exact (div_le_one (Real.rpow_pos_of_pos hd beta)).mpr hb

/-- Native AD for the actual source on every full original R-parent.
The selected shading E has no role in altering this full tube backbone. -/
theorem source_AD {n : ℕ} {D : FiniteScaleSource n} {eta zeta a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (level m : ℕ) (hdy : D.thickness = (2:ℝ)⁻¹^level) (p : Parent)
    (H : ∀ell : Fin (level+1),∀q : Parent,
      (R.filter (fun j => parentLabel D a (2^ell.val) j=q)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun j => parentLabel D a (2^ell.val) j=q)).card:ℝ))
    (hbudget : (2048:ℝ)^3 * (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^zeta)
    (i : Fin (parentLabels D R a (2^m) p).card) (r : ℝ)
    (hr : (source h R E a m p).thickness ≤ r) (hr1 : r ≤ 1) :
    let S := source h R E a m p
    (ENNReal.ofReal S.thickness).rpow e * (ENNReal.ofReal (r/S.thickness))^3 ≤
        (wzCarrierBallCount S i r : ℝ≥0∞) ∧
      (wzCarrierBallCount S i r : ℝ≥0∞) ≤
        (ENNReal.ofReal S.thickness).rpow (-e) * (ENNReal.ofReal (r/S.thickness))^3 := by
  let S := source h R E a m p
  let Q := parentLabels D R a (2^m) p
  let j := NativePaddedCellSource.originalLabel Q i
  have hd := h.1.2.1
  have heps : 0 < S.thickness := by change 0 < ((2^m:ℕ):ℝ)*D.thickness/64; positivity
  have hj : j ∈ Q := NativePaddedCellSource.originalLabel_mem Q i
  have hlo := NativeLocalParentAD.ball_card_lower h hzeta R level hdy H m p j hj hr hr1
  have hu := NativeLocalParentAD.ball_card_upper h (2^m) (by positivity) p Q
    (fun k hk => (mem_parentLabels D R a (2^m) p k).mp hk |>.2) j
    ((mem_parentLabels D R a (2^m) p j).mp hj).2 hr
  have hcount : wzCarrierBallCount S i r =
      (NativeLocalParentAD.ballLabels D Q a (2^m) p j r).card :=
    NativeLocalParentSourceCounts.source_carrierBallCount h R E a m p i r
  have hcoeff : S.thickness^e ≤ D.thickness^zeta/(2048:ℝ)^3 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < (2048:ℝ)^3)).mpr
    change ((((2^m:ℕ):ℝ)*D.thickness/64)^e)*(2048:ℝ)^3 ≤ D.thickness^zeta
    simpa only [mul_comm] using hbudget
  have hupper : (125:ℝ) ≤ S.thickness^(-e) := by
    rw [Real.rpow_neg heps.le, ←one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos heps e)).mpr
    calc
      _ ≤ (2048:ℝ)^3*S.thickness^e :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_pos_of_pos heps e).le
      _ ≤ D.thickness^zeta := hbudget
      _ ≤ 1 := Real.rpow_le_one hd.le h.1.2.2.1 hzeta
  apply real_AD_to_enn heps (heps.trans_le hr).le
  · rw [hcount]
    exact (mul_le_mul_of_nonneg_right hcoeff
      (pow_nonneg (div_nonneg (heps.trans_le hr).le heps.le) 3)).trans hlo
  · rw [hcount]
    exact hu.trans (mul_le_mul_of_nonneg_right hupper
      (pow_nonneg (div_nonneg (heps.trans_le hr).le heps.le) 3))

/-- Native CW for the actual physical local tubes, including convex sets of
infinite volume. The lower occupancy is the original ancestor law. -/
theorem source_CW {n : ℕ} {D : FiniteScaleSource n} {eta zeta a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (H : D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
      ((parentLabels D R a (2^m) p).card:ℝ))
    (hbudget : (373248*512^4:ℝ) * (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤
      D.thickness^(eta+zeta)) (U : Set E4) (hU : Convex ℝ U) :
    (wzContainedTubeCount (source h R E a m p) U : ℝ≥0∞) ≤
      (ENNReal.ofReal (source h R E a m p).thickness).rpow (-e) * volume U *
        (parentLabels D R a (2^m) p).card := by
  let S := source h R E a m p
  let Q := parentLabels D R a (2^m) p
  have hd := h.1.2.1
  have heps : 0 < S.thickness := by change 0 < ((2^m:ℕ):ℝ)*D.thickness/64; positivity
  have hc := negative_coefficient hd heps hbudget
  have hcnn : (373248*512^4:ℝ≥0∞) * (ENNReal.ofReal D.thickness).rpow (-eta-zeta) ≤
      (ENNReal.ofReal S.thickness).rpow (-e) := by
    have hexp : -(eta+zeta) = -eta-zeta := by ring
    simpa only [hexp, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 373248*512^4),
      ENNReal.ofReal_rpow_of_pos hd, ENNReal.ofReal_rpow_of_pos heps,
      ENNReal.ofReal_ofNat, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 373248),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 512), ENNReal.rpow_eq_pow] using ENNReal.ofReal_le_ofReal hc
  have hw := NativeLocalParentCW.original_local_CW h ha (2^m) (by positivity) p Q
    (fun i hi => ((mem_parentLabels D R a (2^m) p i).mp hi).2) H U hU
  rw [NativeLocalParentSourceCounts.source_containedTubeCount]
  exact hw.trans (mul_le_mul' (mul_le_mul' hcnn le_rfl) le_rfl)

/-- All native conditions are derived for the literal source constructor.
Its density premise is the old-incidence average-parent inequality, not an
output density certificate. The source-facing endpoint below derives every
scalar budget and this average inequality internally. -/
theorem native_input {n : ℕ} {D : FiniteScaleSource n} {eta zeta a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (level m : ℕ) (hdy : D.thickness = (2:ℝ)⁻¹^level) (hm : m ≤ level) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a (2^m) p)
    (hne : (parentLabels D R a (2^m) p).Nonempty)
    (H : ∀ell : Fin (level+1),∀q : Parent,
      (R.filter (fun j => parentLabel D a (2^ell.val) j=q)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun j => parentLabel D a (2^ell.val) j=q)).card:ℝ))
    (F Qrad : ℝ) (hF : 0 < F) (hQrad : 0 < Qrad)
    (hparent : D.thickness^(eta+2*zeta)*(parentLabels D R a (2^m) p).card ≤
      D.thickness*F*Qrad^2*E.card)
    (had : (2048:ℝ)^3 * (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^zeta)
    (hcw : (373248*512^4:ℝ) * (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^(eta+zeta))
    (hden : (1024*175616*NativeOriginalPrunedMass.volumeConstant)*F*Qrad^2*
      (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^(eta+2*zeta)) :
    IsWangZakharovNativeFiniteInput (source h R E a m p) e ∧
      (∀i,(source h R E a m p).line i ∈ fixedCompactClass) := by
  obtain ⟨hdS,hdS1,hdyS,hvalid,hSK,hweights,_hfibre,hmeas,hcub,hsub,hsep,hslab,hfixed⟩ :=
    source_geometric_fields h original horiginal ha R E hE level m hdy hm p
  refine ⟨⟨⟨card_pos.mpr hne,hdS,hdS1,hdyS,hvalid,hweights,hmeas,hcub,hsub,hsep,?_,?_,?_⟩,
    hslab,hfixed⟩,hSK⟩
  · exact source_AD h hzeta R E level m hdy p H had
  · exact source_CW h ha R E m p (H ⟨m,by omega⟩ p hne) hcw
  · exact NativeActualLocalDensity.source_density h original horiginal ha R E hE
      level m hdy hm p hQ F Qrad hF hQrad hparent hden

/-- Exact original-label, incidence, mass, support and multiplicity readbacks
of the same actual source used in native admission. -/
def HasExactTrace {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) : Prop :=
  let S := source h R E a m p
  let Q := parentLabels D R a (2^m) p
  S.thickness = ((2^m:ℕ):ℝ)*D.thickness/64 ∧
  Set.range (NativePaddedCellSource.originalLabel Q) = (Q : Set (Fin n)) ∧
  (incidences (sourceCells D R E a (2^m) p)).image (originalPair Q) =
    E.image (NativeLocalCellCoherence.localPair D a (2^m) p) ∧
  wzTotalShadingVolume S = (E.image (NativeLocalCellCoherence.localPair D a (2^m) p)).card *
    (ENNReal.ofReal (((2^m:ℕ):ℝ)*D.thickness/128))^4 ∧
  volume (sourceUnion S) = (E.image (NativeLocalCellCoherence.localCellLabel D a (2^m) p)).card *
    (ENNReal.ofReal (((2^m:ℕ):ℝ)*D.thickness/128))^4 ∧
  NativeFiniteKakeyaCounts.multiplicity S =
    (E.image (NativeLocalCellCoherence.localPair D a (2^m) p)).card /
      ((E.image (NativeLocalCellCoherence.localCellLabel D a (2^m) p)).card:ℝ≥0∞)

theorem source_exact_trace {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a (2^m) p) : HasExactTrace h R E a m p :=
  ⟨rfl,source_original_labels D R a m p,source_incidences_readback D R E a (2^m) p hQ,
    source_total_shading h R E a m p hQ,source_union_volume h R E a m p hQ,
    source_multiplicity h R E a m p hQ⟩

/-- The source readback turns the already proved geometric parent transfer
into a comparison with the multiplicity of the actual admitted source. -/
theorem source_parent_multiplicity_transfer {n : ℕ} {D : FiniteScaleSource n}
    {eta a F Qrad : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (m : ℕ) (p : Parent) (hF : 0 < F) (hQrad : 0 < Qrad)
    (hL : ∀z∈E,D.thickness^eta*(2^m:ℕ)/(16384*F*Qrad^2) ≤
      (NativeLocalPairFibers.pairFiber D a (2^m) E (NativeLocalPairFibers.localPair D a (2^m) z)).card)
    (hp : (parentEdges D a (2^m) E p).Nonempty)
    (hQ : ∀z∈parentEdges D a (2^m) E p,z.1 ∈ parentLabels D R a (2^m) p) :
    let Ep := parentEdges D a (2^m) E p
    (Ep.card:ℝ)/(Ep.image Prod.snd).card ≤
      (125*175616*16384:ℝ)*F*Qrad^2*D.thickness^(-eta)*
        (NativeFiniteKakeyaCounts.multiplicity (source h R Ep a m p)).toReal := by
  dsimp only
  rw [source_multiplicity h R (parentEdges D a (2^m) E p) a m p hQ]
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast]
  rw [←mul_div_assoc]
  exact NativeLocalParentMultiplicity.native_parent_multiplicity_transfer h original horiginal ha
    (2^m) (by positivity) p E hE hF hQrad hL hp

/-- Source-facing finite-menu native admission. The exponent and relative
window, together with the finite menu sizes, are fixed before D, R and E.
Canonical compact regularization is invoked once; one literal E preserves
every old relation and gives actual native local sources on every active
full R-parent at every scheduled scale in the window. -/
theorem compact_original_scheduled_native_admission
    (K : Set MarkedLine) (hK : IsCompact K) (e alpha : ℝ)
    (he : 0 < e) (halpha : 0 < alpha) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < zeta ∧ 0 < L ∧ 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i ∈ K) → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)) (original : Fin n → Finset Index),
          (∀i,D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ n ≤ 2*R.card ∧
          wzTotalShadingVolume D ≤ 2*NativeOriginalPrunedMass.shadingMass D R ∧
          (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R ≤
            NativeOriginalPrunedMass.shadingMass D R ∧
          (∀ U : Set E4, Convex ℝ U →
            ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ≥0∞) ≤
              (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
          (∀ (ell : Fin (level+1)) (p : Parent),
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
          ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
            (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
            ∀ schedule : Fin g → Fin (level+1),
              (∀j,((2^(schedule j).val:ℕ):ℝ)*D.thickness ≤ D.thickness^alpha) →
              ∃ E, IsCore D original R a eta zeta d g L Rel
                (fun j => 2^(schedule j).val) E ∧
                ∀j p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
                  let Ep := parentEdges D a (2^(schedule j).val) E p
                  let S := source h R Ep a (schedule j).val p
                  IsWangZakharovNativeFiniteInput S e ∧
                    (∀i,S.line i ∈ fixedCompactClass) ∧
                    HasExactTrace h R Ep a (schedule j).val p ∧
                    (Ep.card:ℝ)/(Ep.image Prod.snd).card ≤
                      (125*175616*16384:ℝ)*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2*
                        D.thickness^(-eta)*(NativeFiniteKakeyaCounts.multiplicity S).toReal := by
  obtain ⟨zeta,L,eta0,db,_hzdef,hzeta,hL,_hLlarge,heta0,hetaz,hdb,_hdbsmall,hbudget⟩ :=
    NativeLocalAdmissionBudget.exists_uniform_source_budget e alpha he halpha d g
  obtain ⟨dc,hdc,hbase⟩ := compact_original_scheduled_parent_density_core K hK hzeta
  refine ⟨zeta,L,eta0,min db dc,hzeta,hL,heta0,lt_min hdb hdc,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hDK (hsmall.trans (min_le_right _ _)) (heta.trans hetaz)
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro Rel hrefl hsym schedule hwindow
  obtain ⟨E,hEcore⟩ := hcore d g L hdg hL Rel hrefl hsym schedule
  refine ⟨E,hEcore,?_⟩
  have hEA : E ⊆ retained original R := hEcore.1
  have hEne : E.Nonempty := hEcore.2.1
  have hA : retained original R ⊆ incidences original := filter_subset _ _
  have hAne : (retained original R).Nonempty := hEne.mono hEA
  have hE : E ⊆ incidences original := hEA.trans hA
  have hF : (0:ℝ) < factor d g L := by
    have hbasepos : 0 < d+g+g := by omega
    unfold factor NativeLocalPairUniformCore.retentionCost
    positivity
  have hQrad : (0:ℝ) < coreRadix original R L := by
    have hh := NativeSourceSizeBounds.radix_four_le (retained original R).card L
    exact_mod_cast (show 0 < coreRadix original R L by dsimp [coreRadix]; omega)
  intro j p hp
  let Ep := parentEdges D a (2^(schedule j).val) E p
  have hEp : Ep ⊆ incidences original := (filter_subset _ _).trans hE
  have hQ : ∀z∈Ep,z.1 ∈ parentLabels D R a (2^(schedule j).val) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp (hEA hzE)).2,hzp⟩
  have hQne : (parentLabels D R a (2^(schedule j).val) p).Nonempty := by
    obtain ⟨z,hz⟩ := hp
    exact ⟨z.1,hQ z hz⟩
  obtain ⟨had,hcw,hden⟩ := hbudget n D eta h (hsmall.trans (min_le_left _ _)) heta
    original horiginal (retained original R) hA hAne (2^(schedule j).val) (by positivity) (hwindow j)
  obtain ⟨hnative,hfixed⟩ := native_input h hzeta.le original horiginal ha R Ep hEp
    level (schedule j).val hdy (Nat.le_of_lt_succ (schedule j).isLt) p hQ hQne
    (fun ell q hq => (H ell q hq).1) (factor d g L) (coreRadix original R L) hF hQrad
    (hEcore.2.2.2.2.2.1 j p hp) had hcw hden
  exact ⟨hnative,hfixed,source_exact_trace h R Ep a (schedule j).val p hQ,
    source_parent_multiplicity_transfer h original horiginal ha R E hE (schedule j).val p
      hF hQrad (hEcore.2.2.2.2.2.2 j) hp hQ⟩

end NativeActualLocalAdmission
