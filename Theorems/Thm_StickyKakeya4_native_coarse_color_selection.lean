import Theorems.Thm_StickyKakeya4_native_coarse_slope_occupancy
import Theorems.Thm_StickyKakeya4_native_dense_original_parent
import Mathlib.Data.Int.ModEq
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace NativeCoarseColorSelection
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open scoped BigOperators

def slopeFiber (P : Finset Parent) (q : Fin 3 → ℤ) : Finset Parent := P.filter (fun p => p.1=q)

def fiberEmbedding (P : Finset Parent) (M : ℕ)
    (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M) (q : Fin 3 → ℤ) :
    slopeFiber P q ↪ Fin M :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_coe,Fintype.card_fin] using h q))

def rank (P : Finset Parent) (M : ℕ) (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M)
    (p : Parent) : ℕ :=
  if hp : p∈P then (fiberEmbedding P M h p.1 ⟨p,mem_filter.mpr ⟨hp,rfl⟩⟩).val else 0

def color (P : Finset Parent) (M : ℕ) (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M)
    (B : ℕ) (p : Parent) : ℕ × (Fin 3 → ℤ) :=
  (rank P M h p,fun j => p.1 j%(B:ℤ))

def palette (M B : ℕ) : Finset (ℕ × (Fin 3 → ℤ)) :=
  (range M) ×ˢ Fintype.piFinset (fun _ : Fin 3 => Ico (0:ℤ) B)

lemma rank_lt (P : Finset Parent) (M : ℕ) (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M)
    {p : Parent} (hp : p∈P) : rank P M h p < M := by
  rw [rank,dif_pos hp]
  exact Fin.isLt _

lemma same_slope_rank_injective (P : Finset Parent) (M : ℕ)
    (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M)
    {p q : Parent} (hp : p∈P) (hq : q∈P) (hs : p.1=q.1)
    (hr : rank P M h p=rank P M h q) : p=q := by
  rcases p with ⟨ps,pi⟩
  rcases q with ⟨qs,qi⟩
  change ps=qs at hs
  subst qs
  simp only [rank,dif_pos hp,dif_pos hq] at hr
  have he := (fiberEmbedding P M h ps).injective (Fin.ext hr)
  exact congrArg Subtype.val he

lemma same_slope_color_injective (P : Finset Parent) (M B : ℕ)
    (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M)
    {p q : Parent} (hp : p∈P) (hq : q∈P) (hs : p.1=q.1)
    (hc : color P M h B p=color P M h B q) : p=q :=
  same_slope_rank_injective P M h hp hq hs (congrArg Prod.fst hc)

lemma palette_card (M B : ℕ) : (palette M B).card=M*B^3 := by
  simp [palette,Fintype.card_piFinset]

lemma color_mem_palette (P : Finset Parent) (M B : ℕ) (hB : 0 < B)
    (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M) {p : Parent} (hp : p∈P) :
    color P M h B p∈palette M B := by
  have hBi : (0:ℤ) < B := by exact_mod_cast hB
  refine mem_product.mpr ⟨mem_range.mpr (rank_lt P M h hp),?_⟩
  apply Fintype.mem_piFinset.mpr
  intro j
  exact mem_Ico.mpr ⟨Int.emod_nonneg _ hBi.ne',Int.emod_lt_of_pos _ hBi⟩

lemma image_color_card_le (P : Finset Parent) (M B : ℕ) (hB : 0 < B)
    (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M) :
    (P.image (color P M h B)).card ≤ M*B^3 := by
  apply (card_le_card ?_).trans_eq (palette_card M B)
  intro c hc
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hc
  exact color_mem_palette P M B hB h hp

/-- Choose the color using ACTUAL shading and tube-volume weights. The
selected quantity is shading mass, and its average density is retained too.
No lower AD property of the selected color is asserted. -/
theorem exists_dense_color (P : Finset Parent) (M B : ℕ) (hB : 0 < B)
    (h : ∀q : Fin 3 → ℤ,(slopeFiber P q).card ≤ M)
    (shading tube : Parent → ℝ)
    (hshade : ∀p∈P,0 ≤ shading p) (htube : ∀p∈P,0 ≤ tube p)
    (hSM : 0 < ∑p∈P,shading p) (hTM : 0 < ∑p∈P,tube p) :
    ∃Q ⊆ P,Q.Nonempty ∧ 0 < ∑p∈Q,shading p ∧
      (∀p∈Q,∀q∈Q,color P M h B p=color P M h B q) ∧
      (∑p∈P,shading p) ≤ 2*((M*B^3:ℕ):ℝ)*(∑p∈Q,shading p) ∧
      (∑p∈P,shading p)*(∑p∈Q,tube p) ≤ 2*(∑p∈P,tube p)*(∑p∈Q,shading p) := by
  let C := P.image (color P M h B)
  let fiber := fun c => P.filter (fun p => color P M h B p=c)
  let sm := fun c => ∑p∈fiber c,shading p
  let tm := fun c => ∑p∈fiber c,tube p
  have hs : (∑c∈C,sm c)=∑p∈P,shading p :=
    sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem _ hp) _
  have ht : (∑c∈C,tm c)=∑p∈P,tube p :=
    sum_fiberwise_of_maps_to (fun p hp => mem_image_of_mem _ hp) _
  obtain ⟨c,_hc,hpos,hret,hden⟩ := NativeDenseOriginalParent.exists_mass_and_density C sm tm
    (fun c _hc => sum_nonneg (fun p hp => hshade p (mem_filter.mp hp).1))
    (fun c _hc => sum_nonneg (fun p hp => htube p (mem_filter.mp hp).1))
    (by rw [hs]; exact hSM) (by rw [ht]; exact hTM)
  have hQ : (fiber c).Nonempty := by
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    change 0 < ∑p∈fiber c,shading p at hpos
    rw [he,sum_empty] at hpos
    exact (lt_irrefl 0) hpos
  rw [hs] at hret hden
  rw [ht] at hden
  refine ⟨fiber c,filter_subset _ _,hQ,hpos,?_,?_,hden⟩
  · intro p hp q hq
    exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
  · have hcard : (C.card:ℝ) ≤ (M*B^3:ℕ) := by exact_mod_cast image_color_card_le P M B hB h
    exact hret.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hpos.le)

/-- Equal residues cannot represent distinct nearby integer floor cells. -/
lemma equal_floor_of_same_residue_close (x y : ℝ) (B : ℕ)
    (hmod : ⌊x⌋%(B:ℤ)=⌊y⌋%(B:ℤ)) (hclose : |x-y| < (B:ℝ)-1) : ⌊x⌋=⌊y⌋ := by
  by_contra hne
  have hdvd : (B:ℤ) ∣ ⌊y⌋-⌊x⌋ := Int.modEq_iff_dvd.mp hmod
  have hgap := Int.le_abs_of_dvd (sub_ne_zero.mpr (Ne.symm hne)) hdvd
  have hgapR : (B:ℝ) ≤ |(⌊y⌋:ℝ)-(⌊x⌋:ℝ)| := by exact_mod_cast hgap
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hclose
  have hxlo := Int.floor_le x
  have hxhi := Int.lt_floor_add_one x
  have hylo := Int.floor_le y
  have hyhi := Int.lt_floor_add_one y
  have hsmall : |(⌊y⌋:ℝ)-(⌊x⌋:ℝ)| < (B:ℝ) := abs_lt.mpr ⟨by linarith,by linarith⟩
  exact (not_lt_of_ge hgapR) hsmall
end NativeCoarseColorSelection
