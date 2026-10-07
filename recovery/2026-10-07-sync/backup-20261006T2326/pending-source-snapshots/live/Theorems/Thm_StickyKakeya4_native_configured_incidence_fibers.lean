import Theorems.Thm_StickyKakeya4_native_configured_pref_fibers
import Theorems.Thm_StickyKakeya4_native_configured_output_pairs

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeConfiguredIncidenceFibers
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeLocalParentSource NativeRelativeParentProfiles NativeRelativeParentLabels
open NativeCoarseDirectionThinning NativeConfiguredPhaseFibers NativeConfiguredPrefFibers
open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge
open scoped Matrix.Norms.Elementwise

theorem outputTube_phase_fiber_card {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m ell f : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R E a m p) etaS)
    (A : Finset (Fin n)) (hA : A ⊆ parentLabels D R a (2^m) p)
    (j : OutputIndex h R E a m ell p) :
    ((A.filter (fun i => outputTube h R E a m ell p hS i=j)).image
      (parentLabel D a (2^f))).card ≤ 512^3*(2^(f-(m+ell)))^6 := by
  let q := NativeCoarseCellSource.parentIndex
    ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R E a m p) 0 (2^ell))) j
  have hs : A.filter (fun i => outputTube h R E a m ell p hS i=j) ⊆
      A.filter (fun i => relativeLabel D a (2^m) p (2^ell) i=q) := by
    intro i hi
    have hir := hA (mem_filter.mp hi).1
    have hphase := congrArg
      (NativeCoarseCellSource.parentIndex
        ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
          (parentLabel (source h R E a m p) 0 (2^ell)))) (mem_filter.mp hi).2
    change NativeCoarseCellSource.parentIndex _
      (NativeActualConfiguredTube.fullIndex (source h R E a m p) ell
        (localIndex h R E a m p hS i)) = q at hphase
    rw [NativeActualConfiguredTube.fullIndex_readback, source_parentLabel,
      localIndex_readback h R E a m p hS i hir] at hphase
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hphase⟩
  exact (card_le_card (image_subset_image hs)).trans (relative_phase_fiber_card D A a m ell f p q)

/-- The pair image is the deduplicated geometric incidence graph. Its
capacity is the product of the actual mixed point grid and old phase
capacities, with no comparison to the original edge cardinality. -/
theorem configured_incidence_card {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (Rold : Finset (Fin n))
    (E : Finset (Fin n × Index)) (m : ℕ) (hm : 6 ≤ m) (ell f : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h Rold E a m p) etaS)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t, ‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀ t, ‖Fcfg t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (hbase : rho m ≤ mu m*(R:ℝ))
    (H : Finset (Fin n × Index)) (hH : ∀ z ∈ H, z.1 ∈ parentLabels D Rold a (2^m) p) :
    (H.image (fun z => (pref D a m p z.2, parentLabel D a (2^f) z.1))).card ≤
      (pointCost R*(512^3*(2^(f-(m+ell)))^6)) *
        (H.image (fun z => (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2,
          outputTube h Rold E a m ell p hS z.1))).card := by
  let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R
  let tube := outputTube h Rold E a m ell p hS
  have hA : H.image Prod.fst ⊆ parentLabels D Rold a (2^m) p := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := mem_image.mp ht
    exact hH z hz
  have hfiber (b : E4 × OutputIndex h Rold E a m ell p) :
      ((H.filter (fun z => (cfg z.2, tube z.1)=b)).image
        (fun z => (pref D a m p z.2, parentLabel D a (2^f) z.1))).card ≤
          pointCost R*(512^3*(2^(f-(m+ell)))^6) := by
    let X := ((H.image Prod.snd).filter (fun k => cfg k=b.1)).image (pref D a m p)
    let T := ((H.image Prod.fst).filter (fun t => tube t=b.2)).image (parentLabel D a (2^f))
    have hs : (H.filter (fun z => (cfg z.2, tube z.1)=b)).image
        (fun z => (pref D a m p z.2, parentLabel D a (2^f) z.1)) ⊆ X.product T := by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
      have he := (mem_filter.mp hz).2
      apply mem_product.mpr
      constructor
      · exact mem_image.mpr ⟨z.2, mem_filter.mpr
          ⟨mem_image_of_mem _ (mem_filter.mp hz).1, congrArg Prod.fst he⟩, rfl⟩
      · exact mem_image.mpr ⟨z.1, mem_filter.mpr
          ⟨mem_image_of_mem _ (mem_filter.mp hz).1, congrArg Prod.snd he⟩, rfl⟩
    have hx : X.card ≤ pointCost R := configured_pref_fiber_card h m hm p i hi s P hP hd
      F Fcfg hF hCfg R hR hbase (H.image Prod.snd) b.1
    have ht : T.card ≤ 512^3*(2^(f-(m+ell)))^6 :=
      outputTube_phase_fiber_card h Rold E a m ell f p hS (H.image Prod.fst) hA b.2
    exact (card_le_card hs).trans (by simpa only [card_product] using Nat.mul_le_mul hx ht)
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images H
    (fun z => (pref D a m p z.2, parentLabel D a (2^f) z.1))
    (fun z => (cfg z.2, tube z.1)) (pointCost R*(512^3*(2^(f-(m+ell)))^6):ℕ)
    (fun b _ => Nat.cast_le.mpr (hfiber b))
  exact_mod_cast hh

/-- The actual old reference average degree transfers to distinct
configured point/representative incidences. All three fiber costs remain
visible; no original edge count is substituted for either geometric image. -/
theorem configured_degree_transfer {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (Rold : Finset (Fin n))
    (E : Finset (Fin n × Index)) (m : ℕ) (hm : 6 ≤ m) (ell f : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h Rold E a m p) etaS)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t, ‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀ t, ‖Fcfg t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (hbase : rho m ≤ mu m*(R:ℝ))
    (H : Finset (Fin n × Index)) (hH : ∀ z ∈ H, z.1 ∈ parentLabels D Rold a (2^m) p)
    (d : ℝ) (hd0 : 0 ≤ d)
    (hdegree : d*((H.image Prod.snd).image (pref D a m p)).card ≤
      (H.image (fun z => (pref D a m p z.2, parentLabel D a (2^f) z.1))).card) :
    d*((H.image Prod.snd).image
      (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R)).card ≤
      (1201^3:ℝ)*(pointCost R:ℝ)*(512^3*(2^(f-(m+ell)))^6:ℕ)*
        (H.image (fun z => (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2,
          outputTube h Rold E a m ell p hS z.1))).card := by
  have hpoints : (((H.image Prod.snd).image
      (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R)).card:ℝ) ≤
      (1201^3:ℝ)*((H.image Prod.snd).image (pref D a m p)).card := by
    exact_mod_cast configured_point_image_card h m hm p i hi s P hP hd F Fcfg hF R (H.image Prod.snd)
  have hpairs : ((H.image (fun z => (pref D a m p z.2, parentLabel D a (2^f) z.1))).card:ℝ) ≤
      (pointCost R:ℝ)*(512^3*(2^(f-(m+ell)))^6:ℕ)*
        (H.image (fun z => (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2,
          outputTube h Rold E a m ell p hS z.1))).card := by
    exact_mod_cast configured_incidence_card h Rold E m hm ell f p hS i hi s P hP hd F Fcfg
      hF hCfg R hR hbase H hH
  calc
    _ ≤ d*((1201^3:ℝ)*((H.image Prod.snd).image (pref D a m p)).card) :=
      mul_le_mul_of_nonneg_left hpoints hd0
    _ = (1201^3:ℝ)*(d*((H.image Prod.snd).image (pref D a m p)).card) := by ring
    _ ≤ (1201^3:ℝ)*(H.image (fun z => (pref D a m p z.2, parentLabel D a (2^f) z.1))).card :=
      mul_le_mul_of_nonneg_left hdegree (by positivity)
    _ ≤ (1201^3:ℝ)*((pointCost R:ℝ)*(512^3*(2^(f-(m+ell)))^6:ℕ)*
        (H.image (fun z => (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2,
          outputTube h Rold E a m ell p hS z.1))).card) :=
      mul_le_mul_of_nonneg_left hpairs (by positivity)
    _ = _ := by ring

/-- The deduplicated graph counted above has genuine incidences with the
SAME configured full source. This reads each witness back to its original
edge and uses the actual geometric constructor, not a new incidence law. -/
theorem configured_incidence_geometry {n : ℕ} {D : FiniteScaleSource n} {eta etaS a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i, D.shading i=wzCellShading (mesh D) cells i)
    (ha : ∀ i, wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Rold : Finset (Fin n)) (E : Finset (Fin n × Index)) (m : ℕ) (hm : 6 ≤ m)
    (hscale : D.thickness ≤ (rho m)^2) (ell level : ℕ) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h Rold E a m p) etaS)
    (selected : Finset (Fin (parentLabels D Rold a (2^m) p).card × Index))
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀ t u v, |F t u v| ≤ 1/4) (hCfg : ∀ t u v, |Fcfg t u v| ≤ 1/4)
    (R : ℕ) (hR : 0 < R) (hbase : rho m ≤ mu m*(R:ℝ))
    (hmatch : mu m*(R:ℝ) ≤ 4096/((2^ell:ℕ):ℝ))
    (H : Finset (Fin n × Index)) (hH : ∀ z∈H, z.1∈parentLabels D Rold a (2^m) p)
    (hedges : H ⊆ NativeCubicalIncidenceCounts.incidences cells) :
    let C := MarkedIsometricFiniteTransport.source
      (NativeFullCoarseShadow.fullSource hS univ 0 level ell selected)
      (NativePackedFrameIsometry.frame s P hP hd) 0
    ∀ v∈H.image (fun z => (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2,
      outputTube h Rold E a m ell p hS z.1)),
        v.1∈markedUnitTube (C.line v.2) C.thickness := by
  intro C v hv
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
  have hk : (NativePaddedCellSource.originalLabel (parentLabels D Rold a (2^m) p)
      (localIndex h Rold E a m p hS z.1), z.2)∈NativeCubicalIncidenceCounts.incidences cells := by
    rw [localIndex_readback h Rold E a m p hS z.1 (hH z hz)]
    exact hedges hz
  exact NativeActualConfiguredTube.point_mem_full_tube h cells hcells ha Rold E m hm hscale p
    hS level ell selected (localIndex h Rold E a m p hS z.1) z.2 hk s P hP hd F Fcfg
    hF hCfg R hR hbase hmatch

end NativeConfiguredIncidenceFibers
