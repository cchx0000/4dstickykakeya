import Theorems.Thm_StickyKakeya4_native_nested_parent_physical_menu
import Theorems.Thm_StickyKakeya4_native_common_direction_phase_menu
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

noncomputable section
namespace NativeConditionalAngularCountTransfer
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeOriginalCellChartGeometry
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeNestedParentPhysicalMenu
open NativeCommonDirectionPhaseGeometry NativeCommonDirectionPhaseMenu NativeTangentGridCoarsening
open NativeReferenceXYGridAngularCap

lemma nested_parent_power (m t : ℕ) (ht : 6≤ t) :
    (2^(t-6):ℕ)*2^m=2^(m+t-6) := by
  rw [←pow_add]
  congr 1
  omega

lemma nested_relative_width (s t : ℕ) (ht : 6≤ t) (hts : t≤ s) :
    (64:ℝ)/((2^(s-t+6):ℕ):ℝ)=((2^(t-6):ℕ):ℝ)*(64/((2^s:ℕ):ℝ)) := by
  have hp : (2^s:ℕ)=2^(t-6)*2^(s-t+6) := by
    rw [←pow_add]
    congr 1
    omega
  rw [hp,Nat.cast_mul]
  have hR : ((2^(t-6):ℕ):ℝ)≠0 := by positivity
  have hM : ((2^(s-t+6):ℕ):ℝ)≠0 := by positivity
  field_simp

/-- One occupied sigma-phase parent: count the actual rho angular labels
by the fixed inner spatial menu and the unchanged reference angular unions. -/
theorem nested_angular_count {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m s t : ℕ) (ht : 6≤ t) (hts : t≤ s) (p q : Parent)
    (E Ref : Finset (Fin n × Index)) (hER : E⊆ Ref)
    (hOuter : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (hInner : ∀z∈E,parentLabel D a (2^(m+t-6)) z.1=q)
    (cell : Index) (hCell : ∀z∈E,physicalCell D a (2^m) (2^s) p z.2=cell)
    (B : ℝ) (hB : 0≤ B)
    (H : ∀v : Index,((angularMenu D a (m+t-6) (2^(s-t+6)) q Ref v).card:ℝ)≤ B) :
    ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤ (7:ℝ)^4*B := by
  have hLabels : E.image (fun z => physicalCell D a (2^(m+t-6)) (2^(s-t+6)) q z.2)⊆ 
      innerMenu (2^(t-6)) (2^s) (2^(s-t+6)) p q cell := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    have hh := physical_cell_mem_innerMenu D a (2^m) (2^(t-6)) (2^s) (2^(s-t+6))
      (by positivity) (by positivity) (by positivity) (nested_relative_width s t ht hts)
      p q z.1 (hOuter z hz) (by simpa only [nested_parent_power m t ht] using hInner z hz) z.2
    simpa only [nested_parent_power m t ht,hCell z hz] using hh
  have hCard : ((E.image (fun z => physicalCell D a (2^(m+t-6)) (2^(s-t+6)) q z.2)).card:ℝ)≤ (7:ℝ)^4 := by
    exact_mod_cast (card_le_card hLabels).trans_eq (innerMenu_card _ _ _ _ _ _)
  rw [nested_angular_image_card D a m s t ht hts p q E]
  have hCount := image_card_le_real_mul_of_fiber_images E
    (fun z => angularCell D (2^(m+t-6)) (2^(s-t+6)) q z.1)
    (fun z => physicalCell D a (2^(m+t-6)) (2^(s-t+6)) q z.2) B (fun v _hv => by
      have hsub : angularMenu D a (m+t-6) (2^(s-t+6)) q E v⊆ 
          angularMenu D a (m+t-6) (2^(s-t+6)) q Ref v :=
        image_subset_image (filter_subset_filter _ hER)
      exact (Nat.cast_le.mpr (card_le_card hsub)).trans (H v))
  exact hCount.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hCard hB)

/-- Geometric conditioning in both variables: one outer rho spatial cell
and one standard sigma angular cell split into only2049^3 original phase
parents, then into7^4 relative spatial cells in each such parent. -/
theorem conditional_angular_count {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m s t : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (ht : 6≤ t) (hts : t≤ s) (hms : m+s-6≤ level)
    (p : Parent) (E E1 : Finset (Fin n × Index)) (hE1 : E1⊆ incidences original) (hEE1 : E⊆ E1)
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) (cell : Index) (angle : Fin 3 → ℤ)
    (hcell : ∀z∈E,physicalCell D a (2^m) (2^s) p z.2=cell)
    (hangle : ∀z∈E,localAngle D (2^m) p (64/((2^t:ℕ):ℝ)) z.1=angle)
    (B : ℝ) (hB : 0≤ B)
    (H : ∀q∈E.image (fun z => parentLabel D a (2^(m+t-6)) z.1),∀v : Index,
      ((angularMenu D a (m+t-6) (2^(s-t+6)) q (parentEdges D a (2^(m+t-6)) E1 q) v).card:ℝ)≤ B) :
    ((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤ (2049:ℝ)^3*7^4*B := by
  have hPhases := dyadic_phase_cap h original horiginal ha level m s t hdy ht hts hms
    p E (hEE1.trans hE1) hparent cell angle hcell hangle
  have hCount := image_card_le_real_mul_of_fiber_images E
    (fun z => angularCell D (2^m) (2^s) p z.1)
    (fun z => parentLabel D a (2^(m+t-6)) z.1) ((7:ℝ)^4*B) (fun q hq => by
      apply nested_angular_count D a m s t ht hts p q _ (parentEdges D a (2^(m+t-6)) E1 q)
      · intro z hz
        obtain ⟨hz,hzq⟩ := mem_filter.mp hz
        exact mem_filter.mpr ⟨hEE1 hz,hzq⟩
      · exact fun z hz => hparent z (mem_filter.mp hz).1
      · exact fun z hz => (mem_filter.mp hz).2
      · exact fun z hz => hcell z (mem_filter.mp hz).1
      · exact hB
      · exact H q hq)
  have hpR : ((E.image (fun z => parentLabel D a (2^(m+t-6)) z.1)).card:ℝ)≤ (2049:ℝ)^3 := by
    exact_mod_cast hPhases
  exact hCount.trans (by
    have hh := mul_le_mul_of_nonneg_left hpR (show 0≤ (7:ℝ)^4*B by positivity)
    convert hh using 1
    ring)

end NativeConditionalAngularCountTransfer
