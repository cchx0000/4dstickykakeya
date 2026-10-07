import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_radius
import Theorems.Thm_StickyKakeya4_native_uniform_retention_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeTwoMapRetainedSliceJoin
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeUniformRetentionTransfer
open NativeTwoMapRetainedSliceRadius NativeSliceClassBalls NativeSliceRadiusInterpolation
open NativeAnisotropicSliceLabels NativeSliceCountComparison

/-- Height-preserving two-map cover capacities transfer the reference
endpoint cap to the actual retained XY endpoint, separately at each height. -/
theorem height_image_cap {A X Y H : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq H]
    (I T : Finset A) (hTI : T⊆I) (f : A → X) (g : A → Y)
    (hf : X → H) (hg : Y → H)
    (hheight : ∀a∈T,hf (f a)=hg (g a)) (C N : ℕ)
    (hcap : ∀y∈I.image g,((I.filter (fun a => g a=y)).image f).card ≤ C)
    (hEnd : ∀t,((I.image g).filter (fun y => hg y=t)).card ≤ N) (t : H) :
    ((T.image f).filter (fun x => hf x=t)).card ≤ C*N := by
  let S := T.filter (fun a => hf (f a)=t)
  have hSI : S⊆I := (filter_subset _ _).trans hTI
  have he : (T.image f).filter (fun x => hf x=t)=S.image f := by rw [filter_image]
  rw [he]
  have hc : (S.image f).card ≤ C*(S.image g).card :=
    image_card_le_mul_of_fiber_images S f g C (by
      intro y hy
      exact (card_le_card (image_subset_image (filter_subset_filter _ hSI))).trans
        (hcap y (image_subset_image hSI hy)))
  have hs : S.image g⊆(I.image g).filter (fun y => hg y=t) := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
    exact mem_filter.mpr ⟨mem_image_of_mem _ (hSI ha),
      (hheight a (mem_filter.mp ha).1).symm.trans (mem_filter.mp ha).2⟩
  exact hc.trans (Nat.mul_le_mul_left C ((card_le_card hs).trans (hEnd t)))

theorem height_card_le_of_class_bounds (P : Finset Index) (fine coarse : ℕ)
    (height : ℤ) (N : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (hcap : ((P.image (horizontalCoarsen fine coarse)).filter
      (fun q => q (3:Fin 4)=height)).card ≤ N)
    (H : ∀v∈P,((preparedClass P fine coarse v).card:ℝ) ≤ U) :
    ((heightSlice P height).card:ℝ) ≤ (N:ℝ)*U := by
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
  exact hc.trans ((mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr ((card_le_card him).trans hcap)) hU).trans_eq (by ring))

/-- Generic all-radius join for the actual XY outer width1/64 and its
derived endpoint cap. Prepared-ball geometry remains the certified 3D grid. -/
theorem menu_classes_all_radius64 (P : Finset Index) (J fine coarse gap N : ℕ)
    (hJ : 0 < J) (hN : 0 < N)
    (depth : Fin (J+1) → ℕ) (hfirst : depth 0=coarse)
    (hlast : depth (Fin.last J)=fine) (hdepth : ∀j,depth j ≤ fine)
    (hmono : Monotone depth) (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ gap)
    (mu L U s : ℝ) (hmu : 0 < mu) (hL : 0 ≤ L) (hU : 0 ≤ U) (hs : 0 ≤ s)
    (houter : mu*radius fine coarse=1/64)
    (Hlo : ∀j v,v∈P → L*(radius fine (depth j))^s ≤ (preparedClass P fine (depth j) v).card)
    (Hhi : ∀j v,v∈P → ((preparedClass P fine (depth j) v).card:ℝ) ≤ U*(radius fine (depth j))^s)
    (Hcap : ∀z,((P.image (horizontalCoarsen fine coarse)).filter (fun q => q (3:Fin 4)=z)).card ≤ N)
    (u : Index) (hu : u∈P) (r : ℝ) (hr : mu ≤ r) (hr1 : r ≤ 1) :
    let B : ℝ := max 64 ((2^gap:ℕ):ℝ)
    L*(r/mu)^s ≤ B^s*ballCount (realizedSlice P mu (u (3:Fin 4))) (realized mu u) r ∧
      ballCount (realizedSlice P mu (u (3:Fin 4))) (realized mu u) r ≤
        729*(N:ℝ)*U*B^s*(r/mu)^s := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have Hprepared (j : Fin (J+1)) := prepared_real_ball_bounds P hmu fine (depth j) u hu L U s hU
    (Hlo j) (Hhi j)
  have HpreparedU (j : Fin (J+1)) :
      ballCount (realizedSlice P mu (u (3:Fin 4))) (realized mu u) (mu*radius fine (depth j)) ≤
        (27*(N:ℝ)*U)*(radius fine (depth j))^s := by
    apply (Hprepared j).2.trans
    change 27*U*(radius fine (depth j))^s ≤ (27*(N:ℝ)*U)*(radius fine (depth j))^s
    have hRad := radius_pos fine (depth j)
    have hh := mul_le_mul_of_nonneg_right hNr (show 0 ≤ 27*U*(radius fine (depth j))^s by positivity)
    nlinarith only [hh]
  have Hglobal : ((realizedSlice P mu (u (3:Fin 4))).card:ℝ) ≤
      27*(27*(N:ℝ)*U)*(radius fine coarse)^s := by
    have hRad := radius_pos fine coarse
    have hh := height_card_le_of_class_bounds P fine coarse (u (3:Fin 4)) N
      (U*(radius fine coarse)^s) (by positivity) (Hcap _) (by
        intro v hv
        simpa only [hfirst] using Hhi 0 v hv)
    have him : ((realizedSlice P mu (u (3:Fin 4))).card:ℝ) ≤ (heightSlice P (u (3:Fin 4))).card := by
      exact_mod_cast card_image_le
    exact (him.trans hh).trans (by nlinarith only [show 0 ≤ (N:ℝ)*U*(radius fine coarse)^s by positivity])
  have hh := all_radius_bounds64 (realizedSlice P mu (u (3:Fin 4))) (realized mu u)
    J fine coarse gap hJ depth hfirst hlast hdepth hmono hgap mu L (27*(N:ℝ)*U) s
    hmu hL (by positivity) hs houter (fun j => (Hprepared j).1) HpreparedU Hglobal r hr hr1
  simpa only [show (27:ℝ)*(27*(N:ℝ)*U)=729*(N:ℝ)*U by ring] using hh

end NativeTwoMapRetainedSliceJoin
