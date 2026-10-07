import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_upper
import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_join
import Theorems.Thm_StickyKakeya4_native_paid_parent_scale_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

noncomputable section
namespace NativeTwoMapRetainedSliceAD
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeJointUniformCoarseRelations
open NativeAnisotropicSliceLabels NativeSliceClassBalls NativeSliceRadiusInterpolation
open NativeTwoMapRetainedSliceTransfer NativeTwoMapRetainedSliceUpper NativeTwoMapRetainedSliceJoin

/-- A fixed pair of point maps, actual finite cover capacities and original
incidence retention give BOTH all-radius bounds on the existing third core.
No reference XY uniformity or additional refinement is assumed. -/
theorem all_radius_bounds {A : Type*} [DecidableEq A]
    (I T : Finset A) (hTI : T⊆I) (hTn : T.Nonempty)
    (pref pxy : A → Index) (Qref Qnew Cinv Cfwd : ℕ) (hCi : 0 < Cinv) (hCf : 0 < Cfwd)
    (HRef : HasUniformFibers I Qref pref) (HT : HasUniformFibers T Qnew pxy)
    (J fine coarse gap : ℕ) (hJ : 0 < J) (depth : Fin (J+1) → ℕ)
    (hfirst : depth 0=coarse) (hlast : depth (Fin.last J)=fine) (hdepth : ∀j,depth j ≤ fine)
    (hmono : Monotone depth) (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ gap)
    (HC : ∀j,HasUniformFibers T Qnew (fun x => horizontalCoarsen fine (depth j) (pxy x)))
    (hfineInv : ∀z∈I.image pxy,((I.filter (fun x => pxy x=z)).image pref).card ≤ Cinv)
    (hfineFwd : ∀z∈I.image pref,((I.filter (fun x => pref x=z)).image pxy).card ≤ Cfwd)
    (hFwd : ∀j z,z∈(I.image pref).image (horizontalCoarsen fine (depth j)) →
      ((I.filter (fun x => horizontalCoarsen fine (depth j) (pref x)=z)).image
        (fun x => horizontalCoarsen fine (depth j) (pxy x))).card ≤ Cfwd)
    (hInv : ∀j z,z∈I.image (fun x => horizontalCoarsen fine (depth j) (pxy x)) →
      ((I.filter (fun x => horizontalCoarsen fine (depth j) (pxy x)=z)).image
        (fun x => horizontalCoarsen fine (depth j) (pref x))).card ≤ Cinv)
    (hheight : ∀x∈I,pxy x (3:Fin 4)=pref x (3:Fin 4))
    (hEnd : ∀z,(((I.image pref).image (horizontalCoarsen fine coarse)).filter
      (fun q => q (3:Fin 4)=z)).card ≤ 27)
    (mu L U s lambda loss : ℝ) (hmu : 0 < mu) (hL : 0 ≤ L) (hU : 0 ≤ U) (hs : 0 ≤ s)
    (hlambda : 0 ≤ lambda) (hloss : 0 < loss) (houter : mu*radius fine coarse=1/64)
    (hret : lambda*(I.card:ℝ) ≤ loss*T.card)
    (Hratio : ∀j,(L*(radius fine (depth j))^s)*
      ((I.image pref).image (horizontalCoarsen fine (depth j))).card ≤ (I.image pref).card)
    (Hupper : ∀j v,v∈I.image pref → ((preparedClass (I.image pref) fine (depth j) v).card:ℝ) ≤
      U*(radius fine (depth j))^s)
    (u : Index) (hu : u∈T.image pxy) (r : ℝ) (hr : mu ≤ r) (hr1 : r ≤ 1) :
    let B : ℝ := max 64 ((2^gap:ℕ):ℝ)
    let lower := lambda*L/(loss*(Qref:ℝ)^2*Cinv*Cfwd*(Qnew:ℝ)^4)
    let upper := (27*(Cfwd:ℝ))*((Cfwd:ℝ)*Cinv*U)
    lower*(r/mu)^s ≤ B^s*ballCount (realizedSlice (T.image pxy) mu (u (3:Fin 4))) (realized mu u) r ∧
      ballCount (realizedSlice (T.image pxy) mu (u (3:Fin 4))) (realized mu u) r ≤
        729*upper*B^s*(r/mu)^s := by
  have hIn := hTn.mono hTI
  have hQR : (0:ℝ)<Qref := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hIn _ Qref HRef
  have hQT : (0:ℝ)<Qnew := by
    exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos _ hTn _ Qnew HT
  have hCir : (0:ℝ)<Cinv := by exact_mod_cast hCi
  have hCfr : (0:ℝ)<Cfwd := by exact_mod_cast hCf
  let C := loss*(Qref:ℝ)^2*Cinv*Cfwd*(Qnew:ℝ)^4
  have hC : 0<C := by dsimp [C]; positivity
  have hfineT : ∀z∈T.image pxy,((T.filter (fun x => pxy x=z)).image pref).card ≤ Cinv := by
    intro z hz
    exact (card_le_card (image_subset_image (filter_subset_filter _ hTI))).trans
      (hfineInv z (image_subset_image hTI hz))
  have Hlo (j : Fin (J+1)) (v : Index) (hv : v∈T.image pxy) :
      (lambda*L/C)*(radius fine (depth j))^s ≤ (preparedClass (T.image pxy) fine (depth j) v).card := by
    have hh := retained_class_count_lower I T hTI hIn pref (horizontalCoarsen fine (depth j))
      pxy (horizontalCoarsen fine (depth j)) Qref Qnew Cinv Cfwd HRef HT (HC j) hfineT (hFwd j)
      lambda loss (L*(radius fine (depth j))^s) hlambda hloss.le hret (Hratio j)
      (horizontalCoarsen fine (depth j) v) (mem_image_of_mem _ hv)
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hC).mpr
    have he : (T.image pxy).filter (fun z => horizontalCoarsen fine (depth j) z=
        horizontalCoarsen fine (depth j) v)=preparedClass (T.image pxy) fine (depth j) v := by
      ext z
      simp only [preparedClass,mem_filter]
    rw [he] at hh
    calc
      _ = lambda*(L*(radius fine (depth j))^s) := by ring
      _ ≤ C*(preparedClass (T.image pxy) fine (depth j) v).card := hh
      _ = _ := mul_comm _ _
  have Hhi (j : Fin (J+1)) (v : Index) (_hv : v∈T.image pxy) :
      ((preparedClass (T.image pxy) fine (depth j) v).card:ℝ) ≤
        ((Cfwd:ℝ)*Cinv*U)*(radius fine (depth j))^s := by
    have hRad := radius_pos fine (depth j)
    have hh := retained_class_upper I T hTI pref (horizontalCoarsen fine (depth j))
      pxy (horizontalCoarsen fine (depth j)) Cfwd Cinv (U*(radius fine (depth j))^s)
      (by positivity) hfineFwd (hInv j) (by
        intro z hz
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
        exact Hupper j x hx) (horizontalCoarsen fine (depth j) v)
    simpa only [preparedClass,mul_assoc] using hh
  have Hcap (z : ℤ) : (((T.image pxy).image (horizontalCoarsen fine coarse)).filter
      (fun q => q (3:Fin 4)=z)).card ≤ Cfwd*27 := by
    have hh := height_image_cap I T hTI
      (fun x => horizontalCoarsen fine coarse (pxy x))
      (fun x => horizontalCoarsen fine coarse (pref x))
      (fun q => q (3:Fin 4)) (fun q => q (3:Fin 4))
      (fun x hx => by simpa only [horizontalCoarsen_height] using hheight x (hTI hx)) Cfwd 27
      (by
        intro y hy
        have hh := hFwd 0 y (by simpa only [hfirst,image_image,Function.comp_def] using hy)
        simpa only [hfirst] using hh)
      (fun t => by simpa only [image_image,Function.comp_def] using hEnd t) z
    simpa only [image_image,Function.comp_def] using hh
  have hh := menu_classes_all_radius64 (T.image pxy) J fine coarse gap (Cfwd*27) hJ (by positivity)
    depth hfirst hlast hdepth hmono hgap mu (lambda*L/C) ((Cfwd:ℝ)*Cinv*U) s
    hmu (by positivity) (by positivity) hs houter Hlo Hhi Hcap u hu r hr hr1
  dsimp only
  convert hh using 1
  push_cast
  ring

end NativeTwoMapRetainedSliceAD
