import Theorems.Thm_StickyKakeya4_native_remembered_source_mass_construction

/- UNVERIFIED admission of the actual remembered local source. The
shading lower is supplied by exists_same_Q_source on this literal selected
set; native admission of the output is derived from checked field readers.
Scalar AD/CW/density payments remain explicit for the pre-source cutoff. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeRememberedSourceAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeDyadicParentCells NativeCoarseSourceParentReadback
open NativeCoarseCellSource NativeUnitParentNormalization NativeLocalParentSource
open NativeIntermediateParentPopulation NativeCubicalIncidenceCounts
open scoped ENNReal

/-- Assemble native fields on the exact remembered source. Only the
intermediate C has a native-input premise. The selected old-height output
has actual mass, original-cell inclusion and parent membership from the
preceding producer, and its density is rebuilt from that mass. -/
theorem native_of_selected_shading {n : ℕ} {D : FiniteScaleSource n}
    {eta etaA z1 z2 e L : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^b:ℕ):ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (hb : 6 ≤ b) (hz2 : 0 ≤ z2)
    (hA : IsWangZakharovNativeFiniteInput (NativeCoarseCellSource.source h a level b Q rep E hsep) etaA)
    (hrep : ∀q∈Q,parentLabel D a (2^b) (rep q)=q)
    (Hterminal : ∀ell : Fin (b+1),∀q : Parent,
      (Q.filter (fun q' => ancestor b ell.val q'=q)).Nonempty →
        D.thickness^(8*z1)*(((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q' => ancestor b ell.val q'=q)).card:ℝ))
    (hpower : (64/((2^b:ℕ):ℝ))^z2 ≤ D.thickness^(8*z1))
    (selected : Finset (Fin Q.card × Index)) (hselectedNe : selected.Nonempty)
    (hselected : selected ⊆ incidences (intermediateCells (D:=D) a level b Q rep E))
    (c : ℕ) (hc : c ≤ b-6) (p : Parent)
    (hparent : ∀z∈selected,z.1∈parentLabels
      (NativeCoarseCellSource.source h a level b Q rep E hsep) univ 0 (2^c) p)
    (hL : 0 ≤ L)
    (hshade : ENNReal.ofReal L ≤ wzTotalShadingVolume (source hA univ selected 0 c p))
    (had : (2048:ℝ)^3*(((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)^e ≤
      (64/((2^b:ℕ):ℝ))^z2)
    (hcw : (373248*512^4:ℝ)*(((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)^e ≤
      (64/((2^b:ℕ):ℝ))^(etaA+z2))
    (hden : NativeOriginalPrunedMass.volumeConstant*(5832/64^3)*
      (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)^e ≤ L) :
    IsWangZakharovNativeFiniteInput (source hA univ selected 0 c p) e ∧
      (∀i,(source hA univ selected 0 c p).line i∈fixedCompactClass) ∧
      NativeActualLocalAdmission.HasExactTrace hA univ selected 0 c p := by
  let C := NativeCoarseCellSource.source h a level b Q rep E hsep
  have hne : (parentLabels C univ 0 (2^c) p).Nonempty := by
    obtain ⟨z,hz⟩ := hselectedNe
    exact ⟨z.1,hparent z hz⟩
  obtain ⟨hdS,hdS1,hdyS,hvalid,hSK,hweights,_hfibre,hmeas,hcub,hsub,hseparated,hslab,hfixed⟩ :=
    second_source_geometry h a level b Q rep E hsep hb hA selected hselected c hc p
  have hAD := second_source_AD h a level b Q rep E hsep hb hz2 hA hrep Hterminal hpower
    selected c p had
  have hCW := second_source_CW h a level b Q rep E hsep hA hrep Hterminal hpower
    selected c hc p hne hcw
  have hmass := source_total_shading hA univ selected 0 c p hparent
  have hmeshPos : 0 < ((2^c:ℕ):ℝ)*C.thickness/128 := by
    have hCpos : 0 < C.thickness := hA.1.2.1
    positivity
  have hCount : L ≤
      ((selected.image (NativeLocalCellCoherence.localPair C 0 (2^c) p)).card:ℝ)*
        (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/128)^4 := by
    rw [hmass] at hshade
    have hh := ENNReal.toReal_mono (by finiteness) hshade
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hL,ENNReal.toReal_ofReal hmeshPos.le] at hh
    exact hh
  have hDensity := second_source_density_from_count h a level b Q rep E hsep hb hA
    selected hselected c hc p hparent hCount hden
  refine ⟨⟨⟨card_pos.mpr hne,hdS,hdS1,hdyS,hvalid,hweights,hmeas,hcub,hsub,hseparated,hAD,hCW,hDensity⟩,
    hslab,hfixed⟩,hSK,?_⟩
  exact NativeActualLocalAdmission.source_exact_trace hA univ selected 0 c p hparent

end NativeRememberedSourceAdmission
