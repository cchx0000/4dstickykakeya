import Theorems.Thm_StickyKakeya4_original_unit_line_parameters
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalUnitLineGrid
open OriginalPairStripGeometry NativeRadialClassPruning OriginalTwoHopPairFamily
open OriginalUnitLineParameters

abbrev LineCell := ℤ×ℤ×ℤ

def lineCell (rho : ℝ) (z : Pair) : LineCell :=
  (⌊unitX z/rho⌋,⌊unitY z/rho⌋,⌊unitOffset z/rho⌋)

def neighboringCells (c : LineCell) : Finset LineCell :=
  (Finset.Icc (c.1-3) (c.1+3)).product
    ((Finset.Icc (c.2.1-3) (c.2.1+3)).product
      (Finset.Icc (c.2.2-5) (c.2.2+5)))

private theorem floor_close_mem (x y rho : ℝ) (N : ℕ) (hrho : 0<rho)
    (hclose : |x-y|≤(N:ℝ)*rho) :
    ⌊x/rho⌋∈Finset.Icc (⌊y/rho⌋-(N+1:ℕ)) (⌊y/rho⌋+(N+1:ℕ)) := by
  have hd : |x/rho-y/rho|≤(N:ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hrho]
    exact (div_le_iff₀ hrho).mpr hclose
  have hlo := Int.floor_le (x/rho)
  have hhi := Int.lt_floor_add_one (x/rho)
  have hylo := Int.floor_le (y/rho)
  have hyhi := Int.lt_floor_add_one (y/rho)
  obtain ⟨hdlo,hdhi⟩ := abs_le.mp hd
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (show (⌊y/rho⌋:ℝ)-((N:ℝ)+1)≤(⌊x/rho⌋:ℝ) by linarith)
  · exact_mod_cast (show (⌊x/rho⌋:ℝ)≤(⌊y/rho⌋:ℝ)+((N:ℝ)+1) by linarith)

theorem neighboring_cells_card (c : LineCell) : (neighboringCells c).card=539 := by
  unfold neighboringCells
  simp only [Finset.product_eq_sprod,Finset.card_product,Int.card_Icc]
  have h1 : c.1+3+1-(c.1-3)=7 := by omega
  have h2 : c.2.1+3+1-(c.2.1-3)=7 := by omega
  have h3 : c.2.2+5+1-(c.2.2-5)=11 := by omega
  rw [h1,h2,h3]
  decide

/-- Every actual two-hop neighbour has its literal unit-line cell in this
fixed 539-cell box about the original reference line. -/
theorem original_two_hop_cell_localization
    (Pts : Finset Point) (G : Finset Pair) (rho : ℝ) (z v : Pair)
    (hrho : 0<rho) (hz : z∈G) (hGP : G⊆Pts.product Pts)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hv : v∈twoHopPairs G rho z) :
    lineCell rho z∈neighboringCells (lineCell rho v) := by
  obtain ⟨u,hu,hr,hvG,hf⟩ := (mem_two_hop_pairs G rho z v).mp hv
  obtain ⟨hx,hy,hc⟩ := original_class_hops_parameter_close Pts z u v rho hrho
    (Finset.mem_product.mp (hGP hz)).2 (Finset.mem_product.mp (hGP hu)).1 hbox
    (hdistinct z hz) (hdistinct u hu) (hdistinct v hvG) hr.symm hf.symm
  exact Finset.mem_product.mpr ⟨floor_close_mem _ _ rho 2 hrho hx,
    Finset.mem_product.mpr ⟨floor_close_mem _ _ rho 2 hrho hy,
      floor_close_mem _ _ rho 4 hrho hc⟩⟩

/-- Choose original pair representatives of the actual parameter cells. -/
theorem exists_original_line_cell_representatives (G : Finset Pair) (rho : ℝ) :
    ∃ R : Finset Pair, R⊆G ∧ Set.InjOn (lineCell rho) (↑R : Set Pair) ∧
      R.image (lineCell rho)=G.image (lineCell rho) := by
  classical
  obtain ⟨R,hR,hi,heq⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑G : Set Pair) (G.image (lineCell rho)) (by
      intro c hc
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
      exact ⟨z,hz,rfl⟩)
  exact ⟨R,hR,hi,heq⟩

/-- The actual fine parameter grid bounds global charging multiplicity.
Each original pair belongs to at most 539 representative two-hop families. -/
theorem original_two_hop_representative_multiplicity
    (Pts : Finset Point) (G R : Finset Pair) (rho : ℝ) (v : Pair)
    (hrho : 0<rho) (hR : R⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2) :
    (R.filter (fun z => v∈twoHopPairs G rho z)).card≤539 := by
  classical
  calc
    _ ≤ (neighboringCells (lineCell rho v)).card := by
      apply Finset.card_le_card_of_injOn (lineCell rho)
      · intro z hz
        obtain ⟨hzR,hv⟩ := Finset.mem_filter.mp hz
        exact original_two_hop_cell_localization Pts G rho z v hrho (hR hzR)
          hGP hbox hdistinct hv
      · intro z hz u hu heq
        exact hinj (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hu).1 heq
    _ = _ := neighboring_cells_card _

end OriginalUnitLineGrid
