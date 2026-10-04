import Theorems.Thm_StickyKakeya4_native_fixed_compact_incidence_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeIncidenceMultiplicityTower
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeCubicalIncidenceCounts
open scoped BigOperators ENNReal

def multiplicity {T X : Type*} [DecidableEq X] (I : Finset (T × X)) : ℝ :=
  (I.card:ℝ)/(I.image Prod.snd).card

def coarse {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) : Finset (P × X) :=
  I.image (fun z => (f z.1,z.2))

def parent {T X P : Type*} [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) (p : P) : Finset (T × X) :=
  I.filter (fun z => f z.1=p)

lemma coarse_support {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) :
    (coarse I f).image Prod.snd=I.image Prod.snd := by
  simp only [coarse,image_image,Function.comp_def]

lemma coarse_parents {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) :
    (coarse I f).image Prod.fst=I.image (fun z => f z.1) := by
  simp only [coarse,image_image,Function.comp_def]

lemma parent_nonempty {T X P : Type*} [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) {p : P} (hp : p∈I.image (fun z => f z.1)) :
    (parent I f p).Nonempty := by
  obtain ⟨z,hz,hf⟩ := mem_image.mp hp
  exact ⟨z,mem_filter.mpr ⟨hz,hf⟩⟩

lemma coarse_parent_card {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) (p : P) :
    ((coarse I f).filter (fun z => z.1=p)).card=((parent I f p).image Prod.snd).card := by
  have he : (coarse I f).filter (fun z => z.1=p)=
      ((parent I f p).image Prod.snd).image (fun x => (p,x)) := by
    ext z
    simp only [coarse,parent,mem_filter,mem_image,Prod.exists]
    aesop
  rw [he,card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]

/-- Every coarse parent-point pair is counted once, so the coarse incidence
cardinality is the sum of the actual conditional support cardinalities. -/
lemma coarse_card_sum {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) :
    (coarse I f).card=∑p∈I.image (fun z => f z.1),((parent I f p).image Prod.snd).card := by
  rw [card_eq_sum_card_image Prod.fst (coarse I f),coarse_parents]
  exact sum_congr rfl (fun p _hp => coarse_parent_card I f p)

lemma fine_card_sum {T X P : Type*} [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) :
    I.card=∑p∈I.image (fun z => f z.1),(parent I f p).card :=
  card_eq_sum_card_image (fun z => f z.1) I

/-- The product inequality follows by summing the actual parent incidences
and supports. The point labels remain the SAME original support. -/
theorem multiplicity_le_parent_upper {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) (M : ℝ)
    (hupper : ∀p∈I.image (fun z => f z.1),multiplicity (parent I f p) ≤ M) :
    multiplicity I ≤ M*multiplicity (coarse I f) := by
  have hcount : (I.card:ℝ) ≤ M*(coarse I f).card := by
    have hf : (I.card:ℝ)=∑p∈I.image (fun z => f z.1),((parent I f p).card:ℝ) := by
      exact_mod_cast fine_card_sum I f
    have hc : ((coarse I f).card:ℝ)=∑p∈I.image (fun z => f z.1),(((parent I f p).image Prod.snd).card:ℝ) := by
      exact_mod_cast coarse_card_sum I f
    rw [hf,hc,mul_sum]
    apply sum_le_sum
    intro p hp
    have hu : (0:ℝ) < ((parent I f p).image Prod.snd).card := by
      exact_mod_cast card_pos.mpr ((parent_nonempty I f hp).image Prod.snd)
    exact (div_le_iff₀ hu).mp (hupper p hp)
  have hh := div_le_div_of_nonneg_right hcount (Nat.cast_nonneg (I.image Prod.snd).card)
  simpa only [multiplicity,coarse_support,mul_div_assoc] using hh

/-- A genuine occupied original parent witnesses the multiplicity product;
its relative multiplicity is its actual incidence/support ratio. There is no
supplied matching number or extremal profile in this finite selection. -/
theorem exists_parent_multiplicity_product {T X P : Type*} [DecidableEq X] [DecidableEq P]
    (I : Finset (T × X)) (f : T → P) (hne : I.Nonempty) :
    ∃p∈I.image (fun z => f z.1),(parent I f p).Nonempty ∧
      multiplicity I ≤ multiplicity (parent I f p)*multiplicity (coarse I f) := by
  obtain ⟨p,hp,hmax⟩ := exists_max_image (I.image (fun z => f z.1))
    (fun p => multiplicity (parent I f p)) (hne.image _)
  exact ⟨p,hp,parent_nonempty I f hp,multiplicity_le_parent_upper I f _ (fun q hq => hmax q hq)⟩

lemma source_multiplicity_real {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (D.thickness/2) cells i) :
    (NativeFiniteKakeyaCounts.multiplicity D).toReal=multiplicity (incidences cells) := by
  rw [multiplicity_eq_card_ratio D (half_pos h.1.2.1) cells h.1.2.2.2.2.2.1 hcells,
    ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast]
  rw [support_eq_image]
  rfl

/-- Consume the finite product on actual original cubical source incidences.
The intermediate coarse set changes only the tube parent label; it retains
the literal fine cell coordinate. Spatial coarsening requires its separate
fiber comparison and is not silently identified with this exact tower. -/
theorem actual_original_parent_product {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,D.shading i=wzCellShading (D.thickness/2) cells i)
    (hne : (incidences cells).Nonempty) (a : ℝ) (N : ℕ) :
    ∃p∈parents D a N,(parentIncidences D cells a N p).Nonempty ∧
      (NativeFiniteKakeyaCounts.multiplicity D).toReal ≤
        multiplicity (parentIncidences D cells a N p)*
          multiplicity (coarse (incidences cells) (parentLabel D a N)) := by
  obtain ⟨p,hp,hpn,hmul⟩ := exists_parent_multiplicity_product (incidences cells) (parentLabel D a N) hne
  have hpar : p∈parents D a N := by
    obtain ⟨z,_hz,hzp⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨z.1,mem_univ _,hzp⟩
  refine ⟨p,hpar,hpn,?_⟩
  rw [source_multiplicity_real h cells hcells]
  exact hmul
end NativeIncidenceMultiplicityTower
