import Theorems.Thm_StickyKakeya4_native_grain_height_projection_density
import Theorems.Thm_StickyKakeya4_compatible_tuple_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeWeightedGrainQuotientSelection
open Classical Finset SelfUniform
open scoped BigOperators

/-- An original grain before any quotient selection. -/
def grain {A G : Type*} [DecidableEq G] (H : Finset A) (g : A → G) (c : G) : Finset A :=
  H.filter (fun x => g x=c)

/-- An occupied quotient class maximizing the ORIGINAL weights in its
original grain. The default is used only for empty original grains. -/
def chosen {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) (c : G) : B :=
  if h : ((grain H g c).image f).Nonempty then
    (exists_max_image ((grain H g c).image f)
      (fun b => mass w ((grain H g c).filter (fun x => f x=b))) h).choose else default

/-- All original occurrences with the selected quotient label are retained. -/
def selected {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) : Finset A :=
  H.filter (fun x => f x=chosen w H g f (g x))

lemma chosen_spec {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) (c : G)
    (hc : (grain H g c).Nonempty) :
    chosen w H g f c∈(grain H g c).image f ∧
      ∀b∈(grain H g c).image f,
        mass w ((grain H g c).filter (fun x => f x=b)) ≤
          mass w ((grain H g c).filter (fun x => f x=chosen w H g f c)) := by
  have hh := hc.image f
  unfold chosen
  rw [dif_pos hh]
  exact (exists_max_image ((grain H g c).image f)
    (fun b => mass w ((grain H g c).filter (fun x => f x=b))) hh).choose_spec

lemma selected_subset {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) : selected w H g f⊆H := filter_subset _ _

/-- Exact per-original-grain saturation, stronger than merely uniform labels. -/
lemma selected_grain {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) (c : G) :
    grain (selected w H g f) g c=(grain H g c).filter (fun x => f x=chosen w H g f c) := by
  ext x
  simp only [grain,selected,mem_filter]
  constructor
  · rintro ⟨⟨hx,hf⟩,hg⟩
    exact ⟨⟨hx,hg⟩,by simpa only [hg] using hf⟩
  · rintro ⟨⟨hx,hg⟩,hf⟩
    exact ⟨⟨hx,by simpa only [hg] using hf⟩,hg⟩

lemma selected_grain_nonempty {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) (c : G)
    (hc : (grain H g c).Nonempty) : (grain (selected w H g f) g c).Nonempty := by
  obtain ⟨x,hx,hf⟩ := mem_image.mp (chosen_spec w H g f c hc).1
  rw [selected_grain]
  exact ⟨x,mem_filter.mpr ⟨hx,hf⟩⟩

lemma selected_grain_image {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) :
    (selected w H g f).image g=H.image g := by
  apply Subset.antisymm (image_subset_image (selected_subset w H g f))
  intro c hc
  obtain ⟨x,hx,hg⟩ := mem_image.mp hc
  have hn : (grain H g c).Nonempty := ⟨x,mem_filter.mpr ⟨hx,hg⟩⟩
  obtain ⟨y,hy⟩ := selected_grain_nonempty w H g f c hn
  exact mem_image.mpr ⟨y,(mem_filter.mp hy).1,(mem_filter.mp hy).2⟩

/-- The maximum retains the paid weight separately inside EVERY original
grain. No conclusion is inferred from unweighted vertex cardinality. -/
theorem local_mass_retention {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) (c : G) :
    mass w (grain H g c) ≤ ((grain H g c).image f).card*
      mass w (grain (selected w H g f) g c) := by
  by_cases hc : (grain H g c).Nonempty
  · have hmax := (chosen_spec w H g f c hc).2
    rw [selected_grain]
    calc
      _ = ∑b∈(grain H g c).image f,mass w ((grain H g c).filter (fun x => f x=b)) :=
        CompatibleTupleSelection.mass_eq_sum_partition w (grain H g c) f
      _ ≤ ∑_b∈(grain H g c).image f,mass w ((grain H g c).filter (fun x => f x=chosen w H g f c)) :=
        sum_le_sum (fun b hb => hmax b hb)
      _ = _ := by simp
  · rw [not_nonempty_iff_eq_empty] at hc
    simp only [hc,mass,sum_empty,image_empty,card_empty,zero_mul,le_refl]

/-- Whole-source weighted retention sums the already proved local bounds. -/
theorem mass_retention {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (w : A → ℕ) (H : Finset A) (g : A → G) (f : A → B) (C : ℕ)
    (hC : ∀c,((grain H g c).image f).card ≤ C) :
    mass w H ≤ C*mass w (selected w H g f) := by
  have hlocal (c : G) : mass w (grain H g c) ≤ C*mass w (grain (selected w H g f) g c) :=
    (local_mass_retention w H g f c).trans (Nat.mul_le_mul_right _ (hC c))
  calc
    _ = ∑c∈H.image g,mass w (grain H g c) := CompatibleTupleSelection.mass_eq_sum_partition w H g
    _ ≤ ∑c∈H.image g,C*mass w (grain (selected w H g f) g c) := sum_le_sum (fun c _ => hlocal c)
    _ = C*∑c∈(selected w H g f).image g,mass w (grain (selected w H g f) g c) := by
      rw [selected_grain_image,mul_sum]
    _ = _ := by simp only [grain]; rw [←CompatibleTupleSelection.mass_eq_sum_partition w (selected w H g f) g]

/-- Unit original-edge weights give global cardinal retention with only the
ceiling of the computed real quotient cap. -/
theorem card_retention_ceil {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (H : Finset A) (g : A → G) (f : A → B) (C : ℝ)
    (hC : ∀c,(((grain H g c).image f).card:ℝ) ≤ C) :
    H.card ≤ ⌈C⌉₊*(selected (fun _ => 1) H g f).card := by
  have hN (c : G) : ((grain H g c).image f).card ≤ ⌈C⌉₊ := by
    exact_mod_cast (hC c).trans (Nat.le_ceil C)
  simpa [mass] using mass_retention (fun _ => 1) H g f ⌈C⌉₊ hN

/-- Local original-edge retention keeps the sharper real quotient count,
rather than adding a ceiling in every source density inequality. -/
theorem local_card_retention {A G B : Type*} [DecidableEq G] [DecidableEq B] [Inhabited B]
    (H : Finset A) (g : A → G) (f : A → B) (c : G) (C : ℝ)
    (hC : (((grain H g c).image f).card:ℝ) ≤ C) :
    ((grain H g c).card:ℝ) ≤ C*(grain (selected (fun _ => 1) H g f) g c).card := by
  have hh := local_mass_retention (fun _ => 1) H g f c
  simp only [mass,sum_const,nsmul_eq_mul,mul_one] at hh
  exact (show ((grain H g c).card:ℝ) ≤ ((grain H g c).image f).card*
    (grain (selected (fun _ => 1) H g f) g c).card by exact_mod_cast hh).trans
      (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))

end NativeWeightedGrainQuotientSelection
