import Theorems.Thm_StickyKakeya4_native_retained_query_menu
import Theorems.Thm_StickyKakeya4_weighted_rich_directional_layers
import Theorems.Thm_StickyKakeya4_native_approximate_fiber_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeQueriedVertexWeights
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeJointUniformCoarseRelations NativeSpatialAngularGeometry
open RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

/-- The unchanged E2 incidence weight of an original microcell. -/
def pointWeight {T X : Type*} [DecidableEq T] [DecidableEq X]
    (E : Finset (T × X)) (k : X) : ℕ := (E.filter (fun z => z.2=k)).card

/-- Physical vertices are an image of original microcells, without identifying
these vertices with any representative-projected row cell. -/
def vertices {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) : Finset V := (E.image Prod.snd).image f

def vertexMultiplicity {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) : ℝ := (E.card:ℝ)/(vertices E f).card

/-- A computed integer cap, derived below from installed reference uniformity. -/
def vertexCap {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ) : ℕ := Q^2*E.card/(vertices E f).card

lemma mass_pointWeight {T X : Type*} [DecidableEq T] [DecidableEq X]
    (E : Finset (T × X)) (B : Finset X) :
    mass B (pointWeight E)=(E.filter (fun z => z.2∈B)).card :=
  sum_card_fiberwise_eq_card_filter E B Prod.snd

lemma reference_mass {T X : Type*} [DecidableEq T] [DecidableEq X]
    (E : Finset (T × X)) : mass (E.image Prod.snd) (pointWeight E)=E.card := by
  rw [mass_pointWeight,filter_eq_self.mpr (fun z hz => mem_image_of_mem Prod.snd hz)]

lemma vertex_mass_eq {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (v : V) :
    mass (classFiber (E.image Prod.snd) f v) (pointWeight E)=
      (E.filter (fun z => f z.2=v)).card := by
  rw [mass_pointWeight]
  congr 1
  ext z
  simp only [mem_filter,classFiber]
  constructor
  · exact fun hz => ⟨hz.1,hz.2.2⟩
  · exact fun hz => ⟨hz.1,mem_image_of_mem Prod.snd hz.1,hz.2⟩

lemma vertex_upper_cross {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) (v : V) :
    mass (classFiber (E.image Prod.snd) f v) (pointWeight E)*(vertices E f).card ≤
      Q^2*E.card := by
  rw [vertex_mass_eq]
  have hh := NativeCoarseUniformImageDegrees.point_fiber_card_cross E
    (fun z => ((),f z.2)) (Q^2) HU v
  simpa only [vertices,image_image,Function.comp_def] using hh

lemma vertex_lower_cross {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) (v : V) (hv : v∈vertices E f) :
    E.card ≤ Q^2*mass (classFiber (E.image Prod.snd) f v) (pointWeight E)*(vertices E f).card := by
  rw [vertex_mass_eq]
  have him : vertices E f=E.image (fun z => f z.2) := by simp only [vertices,image_image,Function.comp_def]
  rw [him] at hv ⊢
  obtain ⟨a,ha,hav⟩ := mem_image.mp hv
  calc
    _ = ∑w∈E.image (fun z => f z.2),(E.filter (fun z => f z.2=w)).card := card_eq_sum_card_image _ E
    _ ≤ ∑_w∈E.image (fun z => f z.2),Q^2*(E.filter (fun z => f z.2=v)).card := by
      apply sum_le_sum
      intro w hw
      obtain ⟨b,hb,hbw⟩ := mem_image.mp hw
      simpa only [hav,hbw] using HU b hb a ha
    _ = _ := by simp [Nat.mul_comm]

/-- Two-sided point multiplicity is derived on every occupied queried vertex. -/
theorem vertex_mass_bounds {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) (v : V) (hv : v∈vertices E f) :
    vertexMultiplicity E f ≤ (Q:ℝ)^2*mass (classFiber (E.image Prod.snd) f v) (pointWeight E) ∧
      (mass (classFiber (E.image Prod.snd) f v) (pointWeight E):ℝ) ≤
        (Q:ℝ)^2*vertexMultiplicity E f := by
  have hs : (0:ℝ)<(vertices E f).card := by exact_mod_cast card_pos.mpr ⟨v,hv⟩
  constructor
  · apply (div_le_iff₀ hs).mpr
    exact_mod_cast vertex_lower_cross E f Q HU v hv
  · unfold vertexMultiplicity
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    exact_mod_cast vertex_upper_cross E f Q HU v

/-- Every reference vertex has its computed cap; no cap certificate is an input. -/
theorem vertex_mass_le_cap {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) (v : V) :
    mass (classFiber (E.image Prod.snd) f v) (pointWeight E) ≤ vertexCap E f Q := by
  by_cases hE : E.Nonempty
  · apply (Nat.le_div_iff_mul_le (card_pos.mpr ((hE.image Prod.snd).image f))).mpr
    exact vertex_upper_cross E f Q HU v
  · rw [not_nonempty_iff_eq_empty.mp hE]
    simp [vertexCap,vertices,mass,classFiber]

lemma vertexCap_pos {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (hE : E.Nonempty) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) : 0 < vertexCap E f Q := by
  obtain ⟨a,ha⟩ := hE
  have hh := vertex_mass_le_cap E f Q HU (f a.2)
  rw [vertex_mass_eq] at hh
  have hp : 0 < (E.filter (fun z => f z.2=f a.2)).card :=
    card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,rfl⟩⟩
  exact hp.trans_le hh

lemma vertexCap_le_average {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ) :
    (vertexCap E f Q:ℝ) ≤ (Q:ℝ)^2*vertexMultiplicity E f := by
  have hh := (Nat.cast_div_le (m:=Q^2*E.card) (n:=(vertices E f).card) (α:=ℝ))
  simpa only [vertexCap,vertexMultiplicity,Nat.cast_mul,Nat.cast_pow,mul_div_assoc] using hh

/-- Arbitrary later microcell restrictions keep their original E2 weights and
inherit the computed cap, without any pointwise retention assertion. -/
theorem mass_le_vertices_mul_cap {T X V : Type*}
    [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2))
    (B : Finset X) (hB : B⊆E.image Prod.snd) :
    mass B (pointWeight E) ≤ (B.image f).card*vertexCap E f Q := by
  convert mass_le_image_card_mul (E.image Prod.snd) B hB f (pointWeight E) _
    (vertex_mass_le_cap E f Q HU) using 1
  congr
  exact Subsingleton.elim _ _

/-- Any genuinely witnessed approximate predecessor set yields distinct
physical vertices. Only its membership in the geometric fiber is supplied. -/
theorem weighted_approximate_predecessor_vertices {T : Type*} [DecidableEq T]
    (E : Finset (T × Index)) (hE : E.Nonempty) (f : Index → Index) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2))
    (A B : Finset Index) (hA : A⊆E.image Prod.snd) (hBA : B⊆A)
    (width : ℝ) (P : Submodule ℝ E4) (x : E4) (err : ℝ) (k : ℕ)
    (hpred : k≤ mass B (pointWeight E))
    (hnear : ∀b∈B,Metric.infDist (cellCenter width (f b)-x) (P:Set E4)≤err) :
    k ⌈/⌉ vertexCap E f Q ≤ (NativeApproximateFiberCount.fiber width (A.image f) P x err).card := by
  have hcap := mass_le_vertices_mul_cap E f Q HU B (hBA.trans hA)
  have him : B.image f⊆NativeApproximateFiberCount.fiber width (A.image f) P x err := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨mem_image_of_mem f (hBA hb),hnear b hb⟩
  apply (ceilDiv_le_iff_le_mul (vertexCap_pos E hE f Q HU)).mpr
  have hbound : k ≤ vertexCap E f Q*(B.image f).card := by
    simpa only [Nat.mul_comm] using hpred.trans hcap
  exact hbound.trans (Nat.mul_le_mul_left _ (card_le_card him))

lemma center_injective {width : ℝ} (hw : 0 < width) : Function.Injective (cellCenter width) := by
  intro k l hkl
  ext v
  have hh := congrArg (fun x : E4 => x v) hkl
  change width*((k v:ℝ)+1/2)=width*((l v:ℝ)+1/2) at hh
  have he : (k v:ℝ)=(l v:ℝ) := add_right_cancel (mul_left_cancel₀ hw.ne' hh)
  exact_mod_cast he

lemma embedded_vertex_cap {T X V W : Type*} [DecidableEq T] [DecidableEq X]
    [DecidableEq V] [DecidableEq W]
    (E : Finset (T × X)) (f : X → V) (g : V → W) (hg : Function.Injective g) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) (y : W) :
    mass (classFiber (E.image Prod.snd) (fun k => g (f k)) y) (pointWeight E) ≤ vertexCap E f Q := by
  by_cases hy : (classFiber (E.image Prod.snd) (fun k => g (f k)) y).Nonempty
  · obtain ⟨a,ha⟩ := hy
    simp only [classFiber,mem_filter] at ha
    have hay := ha.2
    have he : classFiber (E.image Prod.snd) (fun k => g (f k)) y=
        classFiber (E.image Prod.snd) f (f a) := by
      ext k
      simp only [classFiber,mem_filter,←hay,hg.eq_iff]
    rw [he]
    exact vertex_mass_le_cap E f Q HU (f a)
  · rw [not_nonempty_iff_eq_empty.mp hy]
    simp [mass]

/-- The exact quotient predecessor theorem, with the reference vertex-density
certificate replaced by installed raw-query uniformity. -/
theorem weighted_predecessor_vertices {T : Type*} [DecidableEq T]
    (E : Finset (T × Index)) (hE : E.Nonempty) (f : Index → Index) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2))
    (B : Finset Index) (hB : B⊆E.image Prod.snd) (width : ℝ) (hw : 0 < width)
    (P : Submodule ℝ E4) (k : ℕ) (a : Index)
    (hpred : k≤ mass (classFiber B (fun b => P.mkQ (cellCenter width (f b)))
      (P.mkQ (cellCenter width (f a)))) (pointWeight E)) :
    k ⌈/⌉ vertexCap E f Q ≤
      (BackwardFiberGrains.affineFiber (B.image (fun b => cellCenter width (f b))) P
        (cellCenter width (f a))).card := by
  convert WeightedRichDirectionalLayers.weighted_predecessor_vertices (E.image Prod.snd) B hB
    (fun b => cellCenter width (f b)) P (pointWeight E) _ (vertexCap_pos E hE f Q HU)
    (embedded_vertex_cap E f (cellCenter width) (center_injective hw) Q HU) k a hpred using 1
  congr
  exact Subsingleton.elim _ _

/-- Decode the installed RAW point relation from the query itself. In a
squared-grain application this is the separate (p,p) query. -/
theorem queried_vertex_mass_bounds {n K : ℕ} (D : FiniteScaleSource n)
    (queries : Fin K → ℕ × ℕ) (i : Fin K) (E : Finset (Fin n × Index)) (Q : ℕ)
    (HU : HasUniformFibers E Q (NativeRetainedQueryMenu.rawQueryPoint D queries i))
    (v : Index) (hv : v∈vertices E (spatialLabel D (2^(queries i).2))) :
    vertexMultiplicity E (spatialLabel D (2^(queries i).2)) ≤
      (Q:ℝ)^2*mass (classFiber (E.image Prod.snd) (spatialLabel D (2^(queries i).2)) v) (pointWeight E) ∧
      (mass (classFiber (E.image Prod.snd) (spatialLabel D (2^(queries i).2)) v) (pointWeight E):ℝ) ≤
        (Q:ℝ)^2*vertexMultiplicity E (spatialLabel D (2^(queries i).2)) :=
  vertex_mass_bounds E _ Q HU v hv

lemma squared_grain_width (m : ℕ) (hm : 6 ≤ m) :
    64/((2^(2*m-6):ℕ):ℝ)=(64/((2^m:ℕ):ℝ))^2 := by
  have hp : (2^(2*m-6):ℕ)*64=(2^m:ℕ)^2 := by
    calc
      _ = 2^((2*m-6)+6) := by rw [pow_add]; norm_num
      _ = 2^(m*2) := by congr 1; omega
      _ = _ := pow_mul 2 m 2
  have hr : ((2^(2*m-6):ℕ):ℝ)*64=(((2^m:ℕ):ℝ))^2 := by exact_mod_cast hp
  have hpos : (0:ℝ)<(2^(2*m-6):ℕ) := by positivity
  have hpos' : (0:ℝ)<(2^m:ℕ) := by positivity
  field_simp
  nlinarith

end NativeQueriedVertexWeights
