import Theorems.Thm_StickyKakeya4_native_slice_radius_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeSliceMenuBallJoin
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeAnisotropicSliceLabels NativeSliceCountComparison NativeSliceClassBalls
open NativeSliceRadiusInterpolation

/-- The fixed-height endpoint has at most27 occupied coarse columns.
Summing the actual fine-column classes gives the entire slice population. -/
theorem height_card_le_of_class_bounds (P : Finset Index) (fine coarse : ℕ)
    (height : ℤ) (U : ℝ) (hU : 0 ≤ U)
    (hcap : (((P.image (horizontalCoarsen fine coarse)).filter
      (fun q => q (3:Fin 4)=height)).card:ℕ) ≤ 27)
    (H : ∀v∈P,((preparedClass P fine coarse v).card:ℝ) ≤ U) :
    ((heightSlice P height).card:ℝ) ≤ 27*U := by
  let A := heightSlice P height
  have hc := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    A id (horizontalCoarsen fine coarse) U (by
      intro c hc
      obtain ⟨v,hv,hvc⟩ := mem_image.mp hc
      rw [image_id]
      have hs : A.filter (fun x => horizontalCoarsen fine coarse x=c)⊆preparedClass P fine coarse v := by
        intro x hx
        obtain ⟨hxA,hxc⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨(mem_filter.mp hxA).1,hxc.trans hvc.symm⟩
      exact (Nat.cast_le.mpr (card_le_card hs)).trans (H v (mem_filter.mp hv).1))
  rw [image_id] at hc
  have him : A.image (horizontalCoarsen fine coarse)⊆
      (P.image (horizontalCoarsen fine coarse)).filter (fun q => q (3:Fin 4)=height) := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hq
    obtain ⟨hvP,hvh⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨mem_image_of_mem _ hvP,by simpa only [horizontalCoarsen_height] using hvh⟩
  exact hc.trans (calc
    _ ≤ U*27 := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((card_le_card him).trans hcap)) hU
    _ = _ := mul_comm _ _)

/-- This join uses literal class counts and literal endpoint geometry.
The source-facing caller derives both, and a later retained-incidence core
can reuse the same join with its own proved class coefficients. -/
theorem menu_classes_all_radius (P : Finset Index) (J fine coarse G : ℕ) (hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hfirst : depth 0=coarse)
    (hlast : depth (Fin.last J)=fine) (hdepth : ∀j,depth j ≤ fine)
    (hmono : Monotone depth) (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ G)
    (mu L U s : ℝ) (hmu : 0 < mu) (hL : 0 ≤ L) (hU : 0 ≤ U) (hs : 0 ≤ s)
    (houter : mu*radius fine coarse=1/8)
    (Hlo : ∀j v,v∈P → L*(radius fine (depth j))^s ≤ (preparedClass P fine (depth j) v).card)
    (Hhi : ∀j v,v∈P → ((preparedClass P fine (depth j) v).card:ℝ) ≤ U*(radius fine (depth j))^s)
    (Hcap : ∀z,((P.image (horizontalCoarsen fine coarse)).filter (fun q => q (3:Fin 4)=z)).card ≤ 27)
    (u : Index) (hu : u∈P) (r : ℝ) (hr : mu ≤ r) (hr1 : r ≤ 1) :
    let B : ℝ := max 8 ((2^G:ℕ):ℝ)
    L*(r/mu)^s ≤ B^s*ballCount (realizedSlice P mu (u (3:Fin 4))) (realized mu u) r ∧
      ballCount (realizedSlice P mu (u (3:Fin 4))) (realized mu u) r ≤
        729*U*B^s*(r/mu)^s := by
  have hR := radius_pos fine coarse
  have Hprepared (j : Fin (J+1)) := prepared_real_ball_bounds P hmu fine (depth j) u hu L U s hU
    (Hlo j) (Hhi j)
  have Hglobal : ((realizedSlice P mu (u (3:Fin 4))).card:ℝ) ≤
      27*(27*U)*(radius fine coarse)^s := by
    have hh := height_card_le_of_class_bounds P fine coarse (u (3:Fin 4))
      (U*(radius fine coarse)^s) (by positivity) (Hcap _) (by
        intro v hv
        simpa only [hfirst] using Hhi 0 v hv)
    have him : ((realizedSlice P mu (u (3:Fin 4))).card:ℝ) ≤ (heightSlice P (u (3:Fin 4))).card := by
      exact_mod_cast card_image_le
    exact (him.trans hh).trans (by nlinarith only [show 0 ≤ U*(radius fine coarse)^s by positivity])
  have hh := all_radius_bounds (realizedSlice P mu (u (3:Fin 4))) (realized mu u)
    J fine coarse G hJ depth hfirst hlast hdepth hmono hgap mu L (27*U) s
    hmu hL (by positivity) hs houter
    (fun j => (Hprepared j).1) (fun j => (Hprepared j).2) Hglobal r hr hr1
  simpa only [show (27:ℝ)*(27*U)=729*U by ring] using hh

end NativeSliceMenuBallJoin
