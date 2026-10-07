import Theorems.Thm_StickyKakeya4_native_common_direction_phase_geometry
import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeCommonDirectionPhaseMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentGeometry NativeRelativeParentLabels
open NativeNormalizedCellRelativeMenu NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeReferenceXYGridMaps NativeReferenceXYGridMenus NativeReferenceXYGridAngularCap
open NativeCommonDirectionPhaseGeometry NativeSpatialAngularGeometry

/-- Exact original slope parent, with a fixed intercept menu. -/
def phaseMenu (q : Parent) : Finset Parent := {q.1} ×ˢ vectorBox q.2 1024

lemma phaseMenu_card (q : Parent) : (phaseMenu q).card=2049^3 := by
  simp only [phaseMenu,card_product,card_singleton,one_mul,vectorBox_card]

lemma same_angle_original_slope {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N R : ℕ) (p : Parent) (i j : Fin n)
    (he : localAngle D N p (1/(R:ℝ)) i=localAngle D N p (1/(R:ℝ)) j) :
    (parentLabel D a (N*R) i).1=(parentLabel D a (N*R) j).1 := by
  rw [localAngle_inverse,localAngle_inverse] at he
  funext v
  have hh := congrFun he v
  change angularLabel D (N*R) i v=angularLabel D (N*R) j v
  omega

/-- Every actual original phase parent of this two-scale cell lies in a
fixed2049^3 menu. The exact128 contraction factor is paid in the radius. -/
theorem original_parent_mem_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N R M : ℕ) (hR : 0 < R) (hM : 0 < M) (hRM : 64*R ≤ M)
    (hscale : (N:ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (i j : Fin n) (k l : Index) (hk : k∈original i) (hl : l∈original j)
    (hj : parentLabel D a N j=p)
    (hcell : physicalCell D a N M p k=physicalCell D a N M p l)
    (hangle : localAngle D N p (1/(R:ℝ)) i=localAngle D N p (1/(R:ℝ)) j) :
    parentLabel D a (N*R) i∈phaseMenu (parentLabel D a (N*R) j) := by
  have hRr : (0:ℝ)<R := by exact_mod_cast hR
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hrs : 64/(M:ℝ) ≤ 1/(R:ℝ) := by
    apply (div_le_div_iff₀ hMr hRr).mpr
    simpa only [one_mul,Nat.cast_mul,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr hRM
  apply mem_product.mpr
  refine ⟨mem_singleton.mpr (same_angle_original_slope D a N R p i j hangle),?_⟩
  apply Fintype.mem_piFinset.mpr
  intro v
  have hi := physical_intercept_spread h original horiginal ha N M hM hscale (1/(R:ℝ))
    (by positivity) hrs p i j k l hk hl hj hcell hangle v
  have hcoord : |((N*R:ℕ):ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) v-
      ((N*R:ℕ):ℝ)*shiftedIntercept (D.line j) (mesh D) (shift D a) v| ≤ 1024 := by
    rw [original_intercept_difference D a N R p i j v,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤128*R)]
    calc
      _ ≤ (128*(R:ℝ))*(5*(1/(R:ℝ))) := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = 640 := by field_simp; ring
      _ ≤ _ := by norm_num
  have hh := floor_neighbor (by norm_num : (0:ℝ)<1) 1024
    (show |((N*R:ℕ):ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) v-
      ((N*R:ℕ):ℝ)*shiftedIntercept (D.line j) (mesh D) (shift D a) v| ≤ (1024:ℝ)*1 by simpa only [mul_one] using hcoord)
  simpa only [div_one,parentLabel] using hh

/-- Finite cap on the original phase-parent image. All source edges remain
literal; the nonempty case only chooses a center for the bounding menu. -/
theorem original_phase_cap {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N R M : ℕ) (hR : 0 < R) (hM : 0 < M) (hRM : 64*R ≤ M)
    (hscale : (N:ℝ)*D.thickness*(M:ℝ) ≤ 64)
    (p : Parent) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hp : ∀z∈E,parentLabel D a N z.1=p) (q : Index) (v : Fin 3 → ℤ)
    (hcell : ∀z∈E,physicalCell D a N M p z.2=q)
    (hangle : ∀z∈E,localAngle D N p (1/(R:ℝ)) z.1=v) :
    (E.image (fun z => parentLabel D a (N*R) z.1)).card ≤ 2049^3 := by
  by_cases hn : E.Nonempty
  · obtain ⟨z,hz⟩ := hn
    have hsub : E.image (fun z => parentLabel D a (N*R) z.1)⊆phaseMenu (parentLabel D a (N*R) z.1) := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact original_parent_mem_menu h original horiginal ha N R M hR hM hRM hscale p y.1 z.1 y.2 z.2
        ((mem_incidences original _ _).mp (hE hy)) ((mem_incidences original _ _).mp (hE hz))
        (hp z hz) ((hcell y hy).trans (hcell z hz).symm) ((hangle y hy).trans (hangle z hz).symm)
    exact (card_le_card hsub).trans_eq (phaseMenu_card _)
  · simp only [not_nonempty_iff_eq_empty.mp hn,image_empty,card_empty]
    positivity

/-- The physical sigma width and its reciprocal original-parent factor
match exactly, with the mandatory six-level shift. -/
lemma dyadic_sigma (t : ℕ) (ht : 6 ≤ t) :
    (64:ℝ)/((2^t:ℕ):ℝ)=1/((2^(t-6):ℕ):ℝ) := by
  have hp : (2^t:ℕ)=64*2^(t-6) := by
    conv_lhs => rw [show t=6+(t-6) by omega]
    rw [pow_add]
    norm_num
  rw [hp]
  push_cast
  ring

/-- Original source thickness pays the preserved old error at rho. -/
lemma dyadic_source_error {delta : ℝ} (level m s : ℕ) (hdy : delta=(2:ℝ)⁻¹^level)
    (hs : 6 ≤ s) (hms : m+s-6 ≤ level) :
    ((2^m:ℕ):ℝ)*delta*((2^s:ℕ):ℝ) ≤ 64 := by
  have hscale : ((2^(m+s-6):ℕ):ℝ)*delta ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hms]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hp : ((2^m:ℕ):ℝ)*((2^s:ℕ):ℝ)=64*((2^(m+s-6):ℕ):ℝ) := by
    rw [←Nat.cast_mul,←pow_add]
    have he : m+s=6+(m+s-6) := by omega
    rw [he,pow_add]
    push_cast
    norm_num
  have hh := mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ)≤64)
  calc
    _ = (((2^m:ℕ):ℝ)*((2^s:ℕ):ℝ))*delta := by ring
    _ = 64*(((2^(m+s-6):ℕ):ℝ)*delta) := by rw [hp]; ring
    _ ≤ 64 := by simpa only [mul_one] using hh

/-- The exact source-facing count required by the conditional angular
upper: outer physicalrho cell, standard sigmaslope cell, original phase
depth b=m+t-6. There is no local mass or angular-AD input. -/
theorem dyadic_phase_cap {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m s t : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (ht : 6 ≤ t) (hts : t ≤ s) (hms : m+s-6 ≤ level)
    (p : Parent) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hp : ∀z∈E,parentLabel D a (2^m) z.1=p) (q : Index) (v : Fin 3 → ℤ)
    (hcell : ∀z∈E,physicalCell D a (2^m) (2^s) p z.2=q)
    (hangle : ∀z∈E,localAngle D (2^m) p (64/((2^t:ℕ):ℝ)) z.1=v) :
    (E.image (fun z => parentLabel D a (2^(m+t-6)) z.1)).card ≤ 2049^3 := by
  have hRM : 64*(2^(t-6):ℕ) ≤ 2^s := by
    have he : 64*(2^(t-6):ℕ)=2^t := by
      rw [show (64:ℕ)=2^6 by norm_num,←pow_add]
      congr 1
      omega
    rw [he]
    exact Nat.pow_le_pow_right (by norm_num) hts
  have hh := original_phase_cap h original horiginal ha (2^m) (2^(t-6)) (2^s)
    (by positivity) (by positivity) hRM (dyadic_source_error level m s hdy (by omega) hms)
    p E hE hp q v hcell (fun z hz => by simpa only [dyadic_sigma t ht] using hangle z hz)
  have he : (2^m:ℕ)*2^(t-6)=2^(m+t-6) := by
    rw [←pow_add]
    congr 1
    omega
  simpa only [he] using hh

/-- Full-R representatives are read from the same original phase parents.
Their phase labels agree exactly, so no new source indexing is introduced. -/
lemma full_R_representative_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (B : ℕ)
    (i : Fin n) (hi : i∈R) :
    NativeCoarseDirectionThinning.representative h R a B (parentLabel D a B i)∈R ∧
      parentLabel D a B (NativeCoarseDirectionThinning.representative h R a B (parentLabel D a B i))=
        parentLabel D a B i :=
  NativeCoarseDirectionThinning.representative_spec h R a B (mem_image_of_mem _ hi)

end NativeCommonDirectionPhaseMenu
