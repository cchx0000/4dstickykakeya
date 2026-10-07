import Theorems.Thm_StickyKakeya4_native_uniform_retention_transfer
import Theorems.Thm_StickyKakeya4_native_window_XY_labels
import Theorems.Thm_StickyKakeya4_native_quotient_fiber_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeWindowXFibers
open Classical Finset NativeWindowXYLabels NativeTwoMapRetainedSliceLabels
open NativeQuotientLatticeTransport NativeQuotientFiberReadback GridQuotientAD
open scoped BigOperators

/-- Exact preimage of one integer product-grid cell. -/
def gridBox {k : ℕ} (R : ℕ) (y : Fin k → ℤ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset (fun j => Ico (y j*(R:ℤ)) (y j*(R:ℤ)+R))

lemma gridBox_card {k : ℕ} (R : ℕ) (y : Fin k → ℤ) : (gridBox R y).card=R^k := by
  simp only [gridBox,Fintype.card_piFinset]
  have hc (j : Fin k) : (Ico (y j*(R:ℤ)) (y j*(R:ℤ)+R)).card=R := by simp [Int.card_Ico]
  simp only [hc,prod_const,card_univ,Fintype.card_fin]

lemma gridDiv_fiber_card {k : ℕ} (P : Finset (Fin k → ℤ)) (R : ℕ) (hR : 0 < R)
    (y : Fin k → ℤ) : (P.filter (fun x => gridDiv R x=y)).card ≤ R^k := by
  have hRp : (0:ℤ)<R := by exact_mod_cast hR
  have hs : P.filter (fun x => gridDiv R x=y)⊆gridBox R y := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro j
    have hh := congrFun (mem_filter.mp hx).2 j
    exact mem_Ico.mpr ((Int.ediv_eq_iff_of_pos hRp).mp hh)
  simpa only [gridBox_card] using card_le_card hs

lemma gridDiv_card_le {k : ℕ} (P : Finset (Fin k → ℤ)) (R : ℕ) (hR : 0 < R) :
    P.card ≤ R^k*(P.image (gridDiv R)).card := by
  have hh := NativeUniformRetentionTransfer.image_card_le_mul_of_fiber_images
    P id (gridDiv R) (R^k) (by
      intro y _hy
      rw [image_id]
      exact gridDiv_fiber_card P R hR y)
  simpa only [image_id] using hh

def fineX {k l : ℕ} (S : Finset (XY k l)) (h : ℤ) (y : Fin l → ℤ) : Finset (Fin k → ℤ) :=
  (S.filter (fun z => z.1=h ∧ z.2.2=y)).image (fun z => z.2.1)

lemma fine_fiber_card {k l : ℕ} (S : Finset (XY k l)) (h : ℤ) (y : Fin l → ℤ) :
    (fiber (productSlice S h) y).card=(fineX S h y).card := by
  simpa only [image_id,id_eq,fineX] using product_fiber_card S id h y

/-- A whole fine X fiber stays in its actual coarse window and actual
coarse Y bin, even though F varies with the fine height. -/
lemma fineX_image_subset {k l : ℕ} (S : Finset (XY k l)) (H R : ℕ)
    (z : XY k l) :
    (fineX S z.1 z.2.2).image (gridDiv R)⊆
      (fiber (productSlice (S.image (window H R)) (window H R z).1) (window H R z).2.2).image Prod.fst := by
  intro u hu
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
  obtain ⟨hvS,hh,hy⟩ := mem_filter.mp hv
  have hh' : (window H R v).1=(window H R z).1 := congrArg (fun h : ℤ => h/(H:ℤ)) hh
  have hy' : (window H R v).2.2=(window H R z).2.2 := congrArg (gridDiv R) hy
  apply mem_image.mpr
  refine ⟨(window H R v).2,mem_filter.mpr ⟨?_,hy'⟩,rfl⟩
  exact mem_image.mpr ⟨window H R v,mem_filter.mpr ⟨mem_image_of_mem _ hvS,hh'⟩,rfl⟩

/-- The sole spatial coarsening loss is the exact ambient tangent capacity R^k. -/
theorem window_fiber_card {k l : ℕ} (S : Finset (XY k l)) (H R : ℕ) (hR : 0 < R)
    (z : XY k l) :
    (fiber (productSlice S z.1) z.2.2).card ≤ R^k*
      (fiber (productSlice (S.image (window H R)) (window H R z).1) (window H R z).2.2).card := by
  rw [fine_fiber_card]
  have hh := gridDiv_card_le (fineX S z.1 z.2.2) R hR
  exact hh.trans (Nat.mul_le_mul_left _ ((card_le_card (fineX_image_subset S H R z)).trans card_image_le))

/-- Dense fine fibers give dense fibers in every occupied coarse-height
window, with the identical density coefficient after rescaling the mesh. -/
theorem window_fiber_density {k l : ℕ} (S : Finset (XY k l)) (H R Nfine Ncoarse : ℕ)
    (hR : 0 < R) (hN : Nfine=Ncoarse*R) (lambda : ℝ)
    (HX : ∀z∈S,lambda*(Nfine:ℝ)^k ≤ ((fiber (productSlice S z.1) z.2.2).card:ℝ)) :
    ∀h : ℤ,∀y∈(productSlice (S.image (window H R)) h).image Prod.snd,
      lambda*(Ncoarse:ℝ)^k ≤
        ((fiber (productSlice (S.image (window H R)) h) y).card:ℝ) := by
  intro height y hy
  simp only [productSlice,mem_image,mem_filter] at hy
  obtain ⟨p,⟨q,⟨⟨z,hz,rfl⟩,hh⟩,rfl⟩,rfl⟩ := hy
  have hcap := window_fiber_card S H R hR z
  have hcapR : ((fiber (productSlice S z.1) z.2.2).card:ℝ) ≤ (R:ℝ)^k*
      (fiber (productSlice (S.image (window H R)) (window H R z).1) (window H R z).2.2).card := by
    exact_mod_cast hcap
  have hrp : (0:ℝ)<(R:ℝ)^k := pow_pos (by exact_mod_cast hR) k
  have hhx := (HX z hz).trans hcapR
  rw [hN,Nat.cast_mul,mul_pow,hh] at hhx
  apply (mul_le_mul_iff_right₀ hrp).mp
  nlinarith only [hhx]

end NativeWindowXFibers
