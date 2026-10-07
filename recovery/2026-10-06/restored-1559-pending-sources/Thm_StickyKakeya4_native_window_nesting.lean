import Theorems.Thm_StickyKakeya4_native_window_quotient_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

noncomputable section
namespace NativeWindowNesting
open Classical Finset NativeWindowXYLabels NativeTwoMapRetainedSliceLabels
open NativeQuotientLatticeTransport NativeQuotientGridCenters NativeWindowQuotientReadback
open NativeWindowXFibers GridQuotientAD

/-- Literal quotient labels in the height window containing an original
point. Choosing this anchor does not select or reweight the source. -/
def atPoint {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (z : XY k l) : Finset (Fin l → ℤ) :=
  (productSlice (S.image (window (8*R) R)) (z.1/((8*R:ℕ):ℤ))).image Prod.snd

lemma atPoint_eq_image {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (z : XY k l) :
    atPoint S R z=(S.filter (fun w => w.1/((8*R:ℕ):ℤ)=z.1/((8*R:ℕ):ℤ))).image
      (fun w => gridDiv R w.2.2) := quotient_eq_filtered_image _ _ _ _

lemma anchor_mem {k l : ℕ} (S : Finset (XY k l)) (R : ℕ) (z : XY k l) (hz : z∈S) :
    gridDiv R z.2.2∈atPoint S R z := by
  rw [atPoint_eq_image]
  exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,rfl⟩,rfl⟩

lemma height_div_comp (R D : ℕ) (t : ℤ) :
    (t/((8*R:ℕ):ℤ))/(D:ℤ)=t/((8*(R*D):ℕ):ℤ) := by
  rw [Int.ediv_ediv_of_nonneg (Int.natCast_nonneg (8*R))]
  simp only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc]

/-- A finer occupied window maps into its actual coarser ancestor. No
claim that every child retains a fixed mass fraction is required. -/
theorem coarsen_subset {k l : ℕ} (S : Finset (XY k l)) (R D : ℕ) (z : XY k l) :
    (atPoint S R z).image (gridDiv D)⊆atPoint S (R*D) z := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
  rw [atPoint_eq_image] at hx ⊢
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hx
  obtain ⟨hwS,hheight⟩ := mem_filter.mp hw
  refine mem_image.mpr ⟨w,mem_filter.mpr ⟨hwS,?_⟩,?_⟩
  · have hh := congrArg (fun t : ℤ => t/(D:ℤ)) hheight
    simpa only [height_div_comp] using hh
  · exact (gridDiv_comp R D w.2.2).symm

/-- Exact ambient quotient cost under time-and-space coarsening. -/
theorem card_transfer {k l : ℕ} (S : Finset (XY k l)) (R D : ℕ)
    (hD : 0 < D) (z : XY k l) :
    (atPoint S R z).card ≤ D^l*(atPoint S (R*D) z).card :=
  (gridDiv_card_le _ D hD).trans (Nat.mul_le_mul_left _ (card_le_card (coarsen_subset S R D z)))

lemma integer_div_close (D R : ℕ) (hD : 0 < D) (x a : ℤ)
    (h : |x-a| ≤ ((D*R:ℕ):ℤ)) :
    |x/(D:ℤ)-a/(D:ℤ)| ≤ (R:ℤ) := by
  have hDp : (0:ℤ)<D := by exact_mod_cast hD
  have hD0 : (D:ℤ)≠0 := ne_of_gt hDp
  have hdiv (u : ℤ) : (a+u*(D:ℤ))/(D:ℤ)=a/(D:ℤ)+u := by
    rw [Int.add_ediv_of_dvd_right (show (D:ℤ)∣u*(D:ℤ) from ⟨u,by ring⟩),
      Int.mul_ediv_cancel _ hD0]
  obtain ⟨hlo,hhi⟩ := abs_le.mp h
  rw [Nat.cast_mul] at hlo hhi
  have hl := Int.ediv_le_ediv hDp (show a+(-(R:ℤ))*(D:ℤ) ≤ x by nlinarith only [hlo])
  have hu := Int.ediv_le_ediv hDp (show x ≤ a+(R:ℤ)*(D:ℤ) by nlinarith only [hhi])
  rw [hdiv] at hl hu
  exact abs_le.mpr ⟨by omega,by omega⟩

lemma gridDiv_box {l : ℕ} (D R : ℕ) (hD : 0 < D) (x a : Fin l → ℤ)
    (h : x∈box a (D*R)) : gridDiv D x∈box (gridDiv D a) R := by
  rw [mem_box_iff] at h ⊢
  exact fun j => integer_div_close D R hD (x j) (a j) (h j)

lemma box_radius_mono {l : ℕ} (a : Fin l → ℤ) {R T : ℕ} (hRT : R ≤ T) :
    box a R⊆box a T := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  intro j
  exact (hx j).trans (by exact_mod_cast hRT)

/-- The local grid-ball transfer has no center-rounding loss at integer
multiples. This is the finite statement for both descendant lowers and
ancestor uppers in the prepared-height interpolation. -/
theorem local_card_transfer {k l : ℕ} (S : Finset (XY k l)) (R D a b : ℕ)
    (hD : 0 < D) (hab : a ≤ D*b) (z : XY k l) :
    ((atPoint S R z).filter (fun y => y∈box (gridDiv R z.2.2) a)).card ≤
      D^l*((atPoint S (R*D) z).filter
        (fun y => y∈box (gridDiv (R*D) z.2.2) b)).card := by
  let P := (atPoint S R z).filter (fun y => y∈box (gridDiv R z.2.2) a)
  have hsub : P.image (gridDiv D)⊆(atPoint S (R*D) z).filter
      (fun y => y∈box (gridDiv (R*D) z.2.2) b) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨hxS,hxb⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨coarsen_subset S R D z (mem_image_of_mem _ hxS),?_⟩
    have hh := gridDiv_box D b hD x (gridDiv R z.2.2) (box_radius_mono _ hab hxb)
    simpa only [gridDiv_comp] using hh
  exact (gridDiv_card_le P D hD).trans (Nat.mul_le_mul_left _ (card_le_card hsub))

/-- One actual point chooses an occupied fine descendant and the genuine
coarse ancestor simultaneously. Thin intermediate windows require no
additional retained-fraction assumption. -/
theorem bracket_local_counts {k l : ℕ} (S : Finset (XY k l))
    (Rsmall Dsmall Dbig Rtest Rbigtest : ℕ) (hDs : 0 < Dsmall) (hDb : 0 < Dbig)
    (hTest : Rtest ≤ Dbig*Rbigtest) (z : XY k l) :
    ((atPoint S Rsmall z).filter
      (fun y => y∈box (gridDiv Rsmall z.2.2) (Dsmall*Rtest))).card ≤
        Dsmall^l*((atPoint S (Rsmall*Dsmall) z).filter
          (fun y => y∈box (gridDiv (Rsmall*Dsmall) z.2.2) Rtest)).card ∧
    ((atPoint S (Rsmall*Dsmall) z).filter
      (fun y => y∈box (gridDiv (Rsmall*Dsmall) z.2.2) Rtest)).card ≤
        Dbig^l*((atPoint S ((Rsmall*Dsmall)*Dbig) z).filter
          (fun y => y∈box (gridDiv ((Rsmall*Dsmall)*Dbig) z.2.2) Rbigtest)).card :=
  ⟨local_card_transfer S Rsmall Dsmall (Dsmall*Rtest) Rtest hDs le_rfl z,
    local_card_transfer S (Rsmall*Dsmall) Dbig Rtest Rbigtest hDb hTest z⟩

end NativeWindowNesting
