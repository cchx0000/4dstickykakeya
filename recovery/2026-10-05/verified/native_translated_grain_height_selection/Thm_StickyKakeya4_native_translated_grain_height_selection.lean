import Theorems.Thm_StickyKakeya4_native_translated_grain_height_overlap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeTranslatedGrainHeightSelection
open Classical Finset StickyKakeya4 NativeTranslatedGrainHeightOverlap
open NativeWeightedGrainQuotientSelection NativeWeightedGrainQuotientGeometry
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeParentGrainIncidenceCleanup
open NativeSpatialAngularGeometry RichDirectionalLayers SelfUniform

/-- Stage1 retains the maximum ORIGINAL EDGE-weight translated-height class
inside each OLD mixed grain, before the height alphabets are aligned. -/
def first {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) : Finset (Fin n × Index) :=
  selected (fun _ => 1) S (mixedLabel D a m plane ell) (fun z => translatedHeight D a m z.2)

/-- Stage2 retains one raw height by ORIGINAL EDGE weight in each translated
height. Because of stage1 it cuts whole surviving old-grain fibers. -/
def second {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) : Finset (Fin n × Index) :=
  selected (fun _ => 1) (first D a m ell plane S)
    (fun z => translatedHeight D a m z.2) (fun z => rawHeight D m z.2)

lemma first_subset {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) : first D a m ell plane S⊆S := selected_subset _ _ _ _

lemma second_subset_first {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) :
    second D a m ell plane S⊆first D a m ell plane S := selected_subset _ _ _ _

lemma second_subset {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) : second D a m ell plane S⊆S :=
  (second_subset_first D a m ell plane S).trans (first_subset D a m ell plane S)

lemma rawHeight_of_mixed_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (x y : Fin n × Index)
    (hxy : mixedLabel D a m plane ell x=mixedLabel D a m plane ell y) : rawHeight D m x.2=rawHeight D m y.2 :=
  congrArg (fun c : Parent × (Index × Index) => c.2.1 (3:Fin 4)) hxy

lemma first_menu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) (c : Parent × (Index × Index)) :
    ((grain S (mixedLabel D a m plane ell) c).image (fun z => translatedHeight D a m z.2)).card ≤ 2 := by
  apply actual_raw_cell_card D a m _ (c.2.1 (3:Fin 4))
  intro z hz
  exact congrArg (fun c : Parent × (Index × Index) => c.2.1 (3:Fin 4)) (mem_filter.mp hz).2

lemma second_menu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) (t : ℤ) :
    ((grain (first D a m ell plane S) (fun z => translatedHeight D a m z.2) t).image
      (fun z => rawHeight D m z.2)).card ≤ 2 := by
  apply actual_translated_cell_card D a m _ t
  exact fun z hz => (mem_filter.mp hz).2

lemma first_card_retention {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) : S.card ≤ 2*(first D a m ell plane S).card := by
  have hh := mass_retention (fun _ => 1) S (mixedLabel D a m plane ell)
    (fun z => translatedHeight D a m z.2) 2 (first_menu D a m ell plane S)
  simpa [mass,first] using hh

lemma second_card_retention {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) :
    (first D a m ell plane S).card ≤ 2*(second D a m ell plane S).card := by
  have hh := mass_retention (fun _ => 1) (first D a m ell plane S)
    (fun z => translatedHeight D a m z.2) (fun z => rawHeight D m z.2) 2 (second_menu D a m ell plane S)
  simpa [mass,second] using hh

/-- Total fixed original-edge loss4. -/
theorem card_retention_four {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) : S.card ≤ 4*(second D a m ell plane S).card := by
  have h1 := first_card_retention D a m ell plane S
  have h2 := second_card_retention D a m ell plane S
  omega

lemma selected_uniform {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A  →  ℕ) (S : Finset A) (g : A  →  G) (f : A  →  B) (x y : A)
    (hx : x∈selected w S g f) (hy : y∈selected w S g f) (hxy : g x=g y) : f x=f y := by
  simp only [selected,mem_filter] at hx hy
  exact hx.2.trans ((congrArg (chosen w S g f) hxy).trans hy.2.symm)

lemma first_translated_constant {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) (x y : Fin n × Index)
    (hx : x∈first D a m ell plane S) (hy : y∈first D a m ell plane S)
    (hxy : mixedLabel D a m plane ell x=mixedLabel D a m plane ell y) :
    translatedHeight D a m x.2=translatedHeight D a m y.2 :=
  selected_uniform (fun _ => 1) S (mixedLabel D a m plane ell) (fun z => translatedHeight D a m z.2) x y hx hy hxy

/-- The actual translated reference height now determines the old raw height. -/
theorem translated_determines_raw {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) (x y : Fin n × Index)
    (hx : x∈second D a m ell plane S) (hy : y∈second D a m ell plane S)
    (hxy : translatedHeight D a m x.2=translatedHeight D a m y.2) :
    rawHeight D m x.2=rawHeight D m y.2 :=
  selected_uniform (fun _ => 1) (first D a m ell plane S)
    (fun z => translatedHeight D a m z.2) (fun z => rawHeight D m z.2) x y hx hy hxy

/-- Stage2 keeps a whole stage1 old-grain fiber whenever it keeps one edge. -/
theorem second_saturated {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index)) (x y : Fin n × Index)
    (hx : x∈first D a m ell plane S) (hy : y∈second D a m ell plane S)
    (hxy : mixedLabel D a m plane ell x=mixedLabel D a m plane ell y) :
    x∈second D a m ell plane S := by
  have hyt := second_subset_first D a m ell plane S hy
  have ht := first_translated_constant D a m ell plane S x y hx hyt hxy
  have hr := rawHeight_of_mixed_eq D a m ell plane x y hxy
  have hy' := hy
  simp only [second,selected,mem_filter] at hy'
  change x∈(first D a m ell plane S).filter _
  apply mem_filter.mpr
  exact ⟨hx,by simpa only [ht,hr] using hy'.2⟩

lemma surviving_grain_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index))
    (x : Fin n × Index) (hx : x∈second D a m ell plane S) :
    mixedFiber D a m plane ell (second D a m ell plane S) (mixedLabel D a m plane ell x)=
      mixedFiber D a m plane ell (first D a m ell plane S) (mixedLabel D a m plane ell x) := by
  ext y
  simp only [mixedFiber,classFiber,mem_filter]
  constructor
  · exact fun hy => ⟨second_subset_first D a m ell plane S hy.1,hy.2⟩
  · exact fun hy => ⟨second_saturated D a m ell plane S y x hy.1 hx hy.2,hy.2⟩

/-- A surviving old grain loses only the first factor2 locally. The second
factor2 is paid globally by choosing entire old-grain fibers. -/
theorem surviving_local_retention {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S : Finset (Fin n × Index))
    (x : Fin n × Index) (hx : x∈second D a m ell plane S) :
    ((mixedFiber D a m plane ell S (mixedLabel D a m plane ell x)).card:ℝ) ≤
      2*(mixedFiber D a m plane ell (second D a m ell plane S) (mixedLabel D a m plane ell x)).card := by
  rw [surviving_grain_eq D a m ell plane S x hx]
  have hh := local_card_retention S (mixedLabel D a m plane ell) (fun z => translatedHeight D a m z.2)
    (mixedLabel D a m plane ell x) 2 (by exact_mod_cast first_menu D a m ell plane S (mixedLabel D a m plane ell x))
  simpa only [grain_mixed_eq,first] using hh

/-- Both constants pass to arbitrary later incidence subsets. -/
theorem hereditary_alignment {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index  →  Submodule ℝ E4) (S H3 : Finset (Fin n × Index))
    (h3 : H3⊆second D a m ell plane S) :
    (∀x y,x∈H3 → y∈H3 → translatedHeight D a m x.2=translatedHeight D a m y.2 → rawHeight D m x.2=rawHeight D m y.2) ∧
    (∀x y,x∈H3 → y∈H3 → mixedLabel D a m plane ell x=mixedLabel D a m plane ell y → 
      translatedHeight D a m x.2=translatedHeight D a m y.2) := by
  refine ⟨fun x y hx hy he => translated_determines_raw D a m ell plane S x y (h3 hx) (h3 hy) he,?_⟩
  intro x y hx hy he
  exact first_translated_constant D a m ell plane S x y
    (second_subset_first D a m ell plane S (h3 hx)) (second_subset_first D a m ell plane S (h3 hy)) he

end NativeTranslatedGrainHeightSelection
