import Theorems.Thm_StickyKakeya4_native_saturated_ancestor_angular_lower
import Theorems.Thm_StickyKakeya4_native_trimmed_angular_class_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeRichAngularImageLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativeOriginalPointAngularLower NativeIncidenceMultiplicityTower NativeOriginalCoarseTupleMenu
open NativeIncidentRankSelection NativePointAngularParentFibers NativeJointUniformCoarseRelations
open NativeSaturatedAncestorAngularLower NativeNormalizedCellAngularMenu RichDirectionalLayers

/-- Any literal original point fiber has at most343 times its ancestor
multiplicity bound per distinct fine angular label. No later point-uniformity
or unweighted incidence/direction identification is used. -/
theorem point_fiber_le_angular_image {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 S : Finset (Fin n × Index)) (hS1 : S⊆E1) (hS : S⊆incidences original)
    (m fine c : ℕ) (hfine : 3 ≤ fine) (hcf : c ≤ m+fine-3)
    (hscale : ((2^(m+fine-3):ℕ):ℝ)*D.thickness ≤ 1) (p : Parent) (Q1 : ℕ)
    (HRef : HasUniformFibers E1 Q1 (formalPair D a c))
    (U : ℝ) (hU : 0 ≤ U)
    (hUpper : ∀t,(parentEdges D a (2^c) E1 t).Nonempty →
      multiplicity (parentEdges D a (2^c) E1 t) ≤ U) (k : Index) :
    ((pointSet S k).card:ℝ) ≤
      343*(Q1:ℝ)^2*U*(pointMenu D m fine p S k).card := by
  have hFib (t : Parent) := ancestor_point_fiber_upper D E1 S hS1 a c
    (m+fine-3) Q1 hcf HRef U hU hUpper k t
  have hCount : ((pointSet S k).card:ℝ) ≤
      (Q1:ℝ)^2*U*(pointParents D a (2^(m+fine-3)) S k).card := by
    have hh := FinePointSlabGeometry.card_le_real_mul_of_fibers (pointSet S k)
      (pointParents D a (2^(m+fine-3)) S k)
      (fun z => parentLabel D a (2^(m+fine-3)) z.1) ((Q1:ℝ)^2*U)
      (fun z hz => mem_image_of_mem _ hz) (fun t _ht => hFib t)
    simpa only [mul_comm] using hh
  have hAngular := pointParents_card_le_angular h original horiginal ha
    (2^(m+fine-3)) hscale S hS k
  have hAngularR : ((pointParents D a (2^(m+fine-3)) S k).card:ℝ) ≤
      343*(pointMenu D m fine p S k).card := by
    rw [pointMenu_card D a m fine hfine p S k]
    exact_mod_cast hAngular
  calc
    _ ≤ (Q1:ℝ)^2*U*(pointParents D a (2^(m+fine-3)) S k).card := hCount
    _ ≤ (Q1:ℝ)^2*U*(343*(pointMenu D m fine p S k).card) :=
      mul_le_mul_of_nonneg_left hAngularR (mul_nonneg (sq_nonneg _) hU)
    _ = _ := by ring

/-- Apply the actual original-parent bound to one rich class of an already
selected pointwise angular trim. The set T is unchanged, so its original
point support and per-point half-mass conclusions remain available. -/
theorem rich_class_angular_lower {n J : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 I T : Finset (Fin n × Index)) (hTI : T⊆I) (hI1 : I⊆E1)
    (hI : I⊆incidences original) (m fine c : ℕ) (hfine : 3 ≤ fine)
    (hcf : c ≤ m+fine-3) (hscale : ((2^(m+fine-3):ℕ):ℝ)*D.thickness ≤ 1)
    (p : Parent) (Q1 : ℕ) (HRef : HasUniformFibers E1 Q1 (formalPair D a c))
    (U : ℝ) (hU : 0 ≤ U)
    (hUpper : ∀t,(parentEdges D a (2^c) E1 t).Nonempty →
      multiplicity (parentEdges D a (2^c) E1 t) ≤ U)
    (sigmaDepth : Fin J → ℕ) (j : Fin J) (k : Index) (q : Fin 3 → ℤ)
    (hRich : ((I.filter (fun z => z.2=k)).card:ℝ)/
        (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ)) <
      ((classFiber (T.filter (fun z => z.2=k))
        (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).card:ℝ)) :
    ((I.filter (fun z => z.2=k)).card:ℝ)/
        (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ)) <
      343*(Q1:ℝ)^2*U*
        (((classFiber (T.filter (fun z => z.2=k))
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).image
            (fun z => angularCell D (2^m) (2^fine) p z.1)).card:ℝ) := by
  let H := classFiber (T.filter (fun z => z.2=k))
    (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q
  have hHI : H⊆I := by
    intro z hz
    simp only [H,classFiber,mem_filter] at hz
    exact hTI hz.1.1
  have hpoint : pointSet H k=H := by
    apply filter_eq_self.mpr
    intro z hz
    simp only [H,classFiber,mem_filter] at hz
    exact hz.1.2
  have hh := point_fiber_le_angular_image h original horiginal ha E1 H (hHI.trans hI1)
    (hHI.trans hI) m fine c hfine hcf hscale p Q1 HRef U hU hUpper k
  change ((pointSet H k).card:ℝ) ≤
    343*(Q1:ℝ)^2*U*((pointSet H k).image
      (fun z => angularCell D (2^m) (2^fine) p z.1)).card at hh
  rw [hpoint] at hh
  exact hRich.trans_le hh

end NativeRichAngularImageLower
