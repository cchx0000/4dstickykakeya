import Theorems.Thm_StickyKakeya4_original_separated_packing
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalBourgainGraphTransfer

def value (x : ℝ) (p : ℤ × ℤ) : ℝ := (p.1:ℝ)+x*(p.2:ℝ)
def code (x : ℝ) (p : ℤ × ℤ) : ℤ := ⌊value x p⌋

/-- Translating a real value in one occupied floor cell leaves at most two
possible original floor labels. -/
lemma floor_translation_pair {u v : ℝ} {j : ℤ} (h : ⌊u+v⌋=j) :
    ⌊u⌋ ∈ Finset.Icc ⌊(j:ℝ)-v⌋ (⌊(j:ℝ)-v⌋+1) := by
  have hlo := Int.floor_le (u+v)
  have hhi := Int.lt_floor_add_one (u+v)
  rw [h] at hlo hhi
  refine Finset.mem_Icc.mpr ⟨Int.floor_mono (by linarith only [hlo]), ?_⟩
  have hm := Int.floor_mono (show u ≤ (j:ℝ)-v+1 by linarith only [hhi])
  simpa only [Int.floor_add_one] using hm

/-- A finite rounded form of Bourgain's robust graph translation inequality.
All edges of G are original; the two difference sets are literal integer
difference sets, and the only loss is the proved two-label floor carry. -/
theorem original_integer_graph_transfer (A B : Finset ℤ) (G : Finset (ℤ × ℤ))
    (x : ℝ) (hG : G ⊆ A.product B) :
    G.card*((A.product A).image (code x)).card ≤
      2*(A-A).card*(B-A).card*(G.image (code x)).card := by
  let I := (A.product A).image (code x)
  let J := G.image (code x)
  have hw : ∀ t∈I, ∃ p∈A.product A, code x p=t := fun t ht => Finset.mem_image.mp ht
  let rep : ℤ → ℤ × ℤ := fun t => if ht : t∈I then Classical.choose (hw t ht) else (0,0)
  have hrep (t : ℤ) (ht : t∈I) : rep t∈A.product A ∧ code x (rep t)=t := by
    dsimp [rep]
    rw [dif_pos ht]
    exact Classical.choose_spec (hw t ht)
  let P := G.product I
  let f : (ℤ × ℤ) × ℤ → (ℤ × ℤ) × ℤ :=
    fun p => ((p.1.1-(rep p.2).1,p.1.2-(rep p.2).2),code x p.1)
  have hfiber (z : (ℤ × ℤ) × ℤ) : (P.filter (fun p => f p=z)).card ≤ 2 := by
    let lo : ℤ := ⌊(z.2:ℝ)-((z.1.1:ℝ)+x*(z.1.2:ℝ))⌋
    have hc : (P.filter (fun p => f p=z)).card ≤ (Finset.Icc lo (lo+1)).card := by
      apply Finset.card_le_card_of_injOn (fun p : (ℤ × ℤ) × ℤ => p.2)
      · intro p hp
        obtain ⟨hp, hf⟩ := Finset.mem_filter.mp hp
        obtain ⟨_, ht⟩ := Finset.mem_product.mp hp
        have he1 : p.1.1-(rep p.2).1=z.1.1 := congrArg (fun q : (ℤ × ℤ) × ℤ => q.1.1) hf
        have he2 : p.1.2-(rep p.2).2=z.1.2 := congrArg (fun q : (ℤ × ℤ) × ℤ => q.1.2) hf
        have hcell : code x p.1=z.2 := congrArg (fun q : (ℤ × ℤ) × ℤ => q.2) hf
        have hp1 : p.1.1=(rep p.2).1+z.1.1 := by omega
        have hp2 : p.1.2=(rep p.2).2+z.1.2 := by omega
        have hv : value x p.1=value x (rep p.2)+((z.1.1:ℝ)+x*(z.1.2:ℝ)) := by
          unfold value
          rw [hp1,hp2]
          push_cast
          ring
        unfold code at hcell
        rw [hv] at hcell
        have hm := floor_translation_pair hcell
        have hrt := (hrep p.2 ht).2
        change ⌊value x (rep p.2)⌋=p.2 at hrt
        apply Finset.mem_Icc.mpr
        simpa only [hrt,lo] using (Finset.mem_Icc.mp hm)
      · intro p hp q hq ht
        change p.2=q.2 at ht
        have hpf := (Finset.mem_filter.mp hp).2
        have hqf := (Finset.mem_filter.mp hq).2
        have hp1 : p.1.1-(rep p.2).1=z.1.1 := congrArg (fun w : (ℤ × ℤ) × ℤ => w.1.1) hpf
        have hq1 : q.1.1-(rep q.2).1=z.1.1 := congrArg (fun w : (ℤ × ℤ) × ℤ => w.1.1) hqf
        have hp2 : p.1.2-(rep p.2).2=z.1.2 := congrArg (fun w : (ℤ × ℤ) × ℤ => w.1.2) hpf
        have hq2 : q.1.2-(rep q.2).2=z.1.2 := congrArg (fun w : (ℤ × ℤ) × ℤ => w.1.2) hqf
        rw [ht] at hp1 hp2
        exact Prod.ext (Prod.ext (by omega) (by omega)) ht
    have htwo : (Finset.Icc lo (lo+1)).card=2 := by
      rw [Int.card_Icc]
      have he : lo+1+1-lo=2 := by omega
      rw [he]
      rfl
    exact hc.trans_eq htwo
  have htarget : P.image f ⊆ ((A-A).product (B-A)).product J := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hg, ht⟩ := Finset.mem_product.mp hp
    obtain ⟨hga,hgb⟩ := Finset.mem_product.mp (hG hg)
    obtain ⟨hra,hrb⟩ := Finset.mem_product.mp (hrep p.2 ht).1
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_sub.mpr ⟨p.1.1,hga,(rep p.2).1,hra,rfl⟩,
       Finset.mem_sub.mpr ⟨p.1.2,hgb,(rep p.2).2,hrb,rfl⟩⟩,
      Finset.mem_image_of_mem _ hg⟩
  have hmass : (P.card : ℝ) ≤ 2*(P.image f).card :=
    OriginalSeparatedPacking.card_le_real_mul_image P f (fun z _ => by exact_mod_cast hfiber z)
  have hcard : (P.image f).card ≤ (A-A).card*(B-A).card*J.card := by
    simpa only [Finset.product_eq_sprod,Finset.card_product] using Finset.card_le_card htarget
  have hcardR : ((P.image f).card : ℝ) ≤ ((A-A).card : ℝ)*(B-A).card*J.card := by
    exact_mod_cast hcard
  have hPcard : (P.card : ℝ)=(G.card : ℝ)*I.card := by
    simp only [P,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  rw [hPcard] at hmass
  have hfinal : (G.card : ℝ)*I.card ≤ 2*((A-A).card : ℝ)*(B-A).card*J.card := by
    nlinarith only [hmass,hcardR]
  exact_mod_cast hfinal

end OriginalBourgainGraphTransfer
