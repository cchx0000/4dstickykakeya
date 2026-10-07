import Theorems.Thm_StickyKakeya4_native_normalized_cell_angular_menu
import Theorems.Thm_StickyKakeya4_native_actual_angular_menu_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeOriginalPointAngularLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeLocalParentGeometry
open NativePointAngularParentFibers NativeNormalizedCellAngularMenu NativeJointUniformCoarseRelations
open NativeOriginalCoarseTupleMenu NativeActualAngularMenuLower NativeDirectionRankDichotomy
open NativeIncidenceMultiplicityTower
open NativeOriginalParentDensityCore NativeIncidentRankSelection

def translateAngle (p : Parent) (ell : ℕ) (q : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun j => q j-(2^(ell-3):ℕ)*p.1 j

lemma translateAngle_injective (p : Parent) (ell : ℕ) : Function.Injective (translateAngle p ell) := by
  intro q r he
  funext j
  have hh := congrFun he j
  change q j-(2^(ell-3):ℕ)*p.1 j=r j-(2^(ell-3):ℕ)*p.1 j at hh
  omega

/-- Actual normalized angular width8/M is the global slope depthm+ell-3,
followed by a fixed integer translation. This preserves cardinality exactly. -/
theorem angular_global_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m ell : ℕ) (hell : 3≤ell) (p : Parent) (i : Fin n) :
    angularCell D (2^m) (2^ell) p i=
      translateAngle p ell (parentLabel D a (2^(m+ell-3)) i).1 := by
  funext j
  have hp : ((2^ell:ℕ):ℝ)=8*((2^(ell-3):ℕ):ℝ) := by
    have he : ell=3+(ell-3) := by omega
    calc
      _ = ((2^(3+(ell-3)):ℕ):ℝ) := by rw [←he]
      _ = _ := by rw [pow_add]; norm_num
  have hg : ((2^(ell-3):ℕ):ℝ)*((2^m:ℕ):ℝ)=((2^(m+ell-3):ℕ):ℝ) := by
    rw [←Nat.cast_mul,←pow_add]
    congr 2
    omega
  have he : (((2^ell:ℕ):ℝ)*localSlope D (2^m) p i j)/8=
      ((2^(ell-3):ℕ):ℝ)*(((2^m:ℕ):ℝ)*NativeOriginalCellChartGeometry.slope (D.line i) j-(p.1 j:ℝ)) := by
    rw [hp]
    change (8*((2^(ell-3):ℕ):ℝ)*(((2^m:ℕ):ℝ)*NativeOriginalCellChartGeometry.slope (D.line i) j-(p.1 j:ℝ)))/8=_
    ring
  change ⌊(((2^ell:ℕ):ℝ)*localSlope D (2^m) p i j)/8⌋=
    ⌊((2^(m+ell-3):ℕ):ℝ)*NativeOriginalCellChartGeometry.slope (D.line i) j⌋-(2^(ell-3):ℕ)*p.1 j
  rw [he,NativeUnitParentDyadic.floor_sub_integer_mul,←mul_assoc,hg]

def pointMenu {n : ℕ} (D : FiniteScaleSource n) (m ell : ℕ) (p : Parent)
    (T : Finset (Fin n × Index)) (k : Index) : Finset (Fin 3 → ℤ) :=
  (T.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) (2^ell) p z.1)

lemma pointMenu_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m ell : ℕ) (hell : 3≤ell) (p : Parent) (T : Finset (Fin n × Index)) (k : Index) :
    (pointMenu D m ell p T k).card=(pointAngular D a (2^(m+ell-3)) T k).card := by
  have he : pointMenu D m ell p T k=
      (pointAngular D a (2^(m+ell-3)) T k).image (translateAngle p ell) := by
    rw [pointAngular_readback,image_image]
    apply image_congr
    intro z _hz
    exact angular_global_readback D a m ell hell p z.1
  rw [he]
  exact card_image_of_injective _ (translateAngle_injective p ell)

/-- Every ORIGINAL retained point has many actual normalized angular cells.
The upper multiplicity of each angular fiber is derived from E1 parent
averages and the343 geometric phase/angle cap, never from total degree alone. -/
theorem original_point_angular_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 T : Finset (Fin n × Index)) (hT1 : T⊆E1) (hT : T⊆incidences original)
    (m ell : ℕ) (hell : 3≤ell) (hscale : ((2^(m+ell-3):ℕ):ℝ)*D.thickness≤1)
    (p : Parent) (Q1 Q3 : ℕ)
    (HRef : HasUniformFibers E1 Q1 (formalPair D a (m+ell-3)))
    (HPoint : HasUniformFibers T Q3 Prod.snd)
    (U : ℝ) (hU : 0≤U)
    (hUpper : ∀t,(parentEdges D a (2^(m+ell-3)) E1 t).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^(m+ell-3)) E1 t)≤U)
    (k : Index) (hk : k∈T.image Prod.snd) :
    NativeIncidenceMultiplicityTower.multiplicity T≤
      343*(Q1:ℝ)^2*(Q3:ℝ)^2*U*(pointMenu D m ell p T k).card := by
  have hMean := mean_le_point_fiber T Q3 HPoint k hk
  have hFib (t : Parent) : (((pointSet T k).filter (fun z => parentLabel D a (2^(m+ell-3)) z.1=t)).card:ℝ)≤
      (Q1:ℝ)^2*U := retained_point_parent_fiber_upper D E1 T hT1 a (m+ell-3) Q1 HRef U hU hUpper k t
  have hCount : ((pointSet T k).card:ℝ)≤(Q1:ℝ)^2*U*(pointParents D a (2^(m+ell-3)) T k).card := by
    have hh := FinePointSlabGeometry.card_le_real_mul_of_fibers (pointSet T k)
      (pointParents D a (2^(m+ell-3)) T k) (fun z => parentLabel D a (2^(m+ell-3)) z.1)
      ((Q1:ℝ)^2*U) (fun z hz => mem_image_of_mem _ hz) (fun t _ht => hFib t)
    simpa only [mul_comm] using hh
  have hAngular := pointParents_card_le_angular h original horiginal ha (2^(m+ell-3)) hscale T hT k
  have hAngularR : ((pointParents D a (2^(m+ell-3)) T k).card:ℝ)≤
      343*(pointMenu D m ell p T k).card := by
    rw [pointMenu_card D a m ell hell p T k]
    exact_mod_cast hAngular
  calc
    _ ≤ (Q3:ℝ)^2*(pointSet T k).card := hMean
    _ ≤ (Q3:ℝ)^2*((Q1:ℝ)^2*U*(pointParents D a (2^(m+ell-3)) T k).card) :=
      mul_le_mul_of_nonneg_left hCount (sq_nonneg _)
    _ ≤ (Q3:ℝ)^2*((Q1:ℝ)^2*U*(343*(pointMenu D m ell p T k).card)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAngularR (mul_nonneg (sq_nonneg _) hU)) (sq_nonneg _)
    _ = _ := by ring

end NativeOriginalPointAngularLower
