import Theorems.Thm_StickyKakeya4_native_matrix_height_wholepoint

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace NativeFrozenTimeField
open Classical Finset NativeMatrixHeightWholePoint

/-- Choose once on the pre-refinement source. Later restrictions do not
change this field, even if its representative point is removed. -/
def field {A V : Type*} [Zero V] (S : Finset A) (height : A → ℝ)
    (F : A → V) (delta : ℝ) (k : ℤ) : V :=
  if h : ∃x∈S,⌊height x/delta⌋=k then F (Classical.choose h) else 0

lemma field_realization {A V : Type*} [Zero V] (S : Finset A) (height : A → ℝ)
    (F : A → V) (delta : ℝ) {k : ℤ} (hk : ∃x∈S,⌊height x/delta⌋=k) :
    ∃x∈S,⌊height x/delta⌋=k ∧ field S height F delta k=F x := by
  refine ⟨Classical.choose hk,(Classical.choose_spec hk).1,(Classical.choose_spec hk).2,?_⟩
  simp only [field,dif_pos hk]

lemma field_norm_le {A V : Type*} [SeminormedAddCommGroup V] (S : Finset A)
    (height : A → ℝ) (F : A → V) (delta B : ℝ) (hB : 0 ≤ B)
    (hF : ∀x∈S,‖F x‖≤B) (k : ℤ) : ‖field S height F delta k‖≤B := by
  by_cases hk : ∃x∈S,⌊height x/delta⌋=k
  · obtain ⟨x,hx,_he,hread⟩ := field_realization S height F delta hk
    rw [hread]
    exact hF x hx
  · simp only [field,dif_neg hk,norm_zero]
    exact hB

lemma nested_height_readback (delta h : ℝ) (N : ℕ) :
    ⌊h/(delta*(N:ℝ))⌋=⌊h/delta⌋/(N:ℤ) := by
  rw [←div_div,Int.floor_div_natCast]

/-- Exact nesting includes negative heights. -/
lemma same_base_same_coarse {delta x y : ℝ} (N : ℕ)
    (h : ⌊x/delta⌋=⌊y/delta⌋) :
    ⌊x/(delta*(N:ℝ))⌋=⌊y/(delta*(N:ℝ))⌋ := by
  rw [nested_height_readback,nested_height_readback,h]

lemma field_close_to_original {A V : Type*} [NormedAddCommGroup V] (S : Finset A)
    (height : A → ℝ) (F : A → V) (delta error : ℝ)
    (hcoh : ∀x∈S,∀y∈S,⌊height x/delta⌋=⌊height y/delta⌋ → dist (F x) (F y)≤error)
    {x : A} (hx : x∈S) :
    dist (field S height F delta ⌊height x/delta⌋) (F x)≤error := by
  obtain ⟨y,hy,he,hread⟩ := field_realization S height F delta ⟨x,hx,rfl⟩
  rw [hread]
  exact hcoh y hy x hx he

/-- The frozen representatives inherit each coarser dyadic relation from the
original selected source. No survival of those representatives is required. -/
theorem frozen_field_coarse {A V : Type*} [NormedAddCommGroup V]
    (S T : Finset A) (hTS : T⊆S) (height : A → ℝ) (F : A → V)
    (delta : ℝ) (N : ℕ) (error : ℝ)
    (hcoh : ∀x∈S,∀y∈S,
      ⌊height x/(delta*(N:ℝ))⌋=⌊height y/(delta*(N:ℝ))⌋ → dist (F x) (F y)≤error)
    {x y : A} (hx : x∈T) (hy : y∈T)
    (hcell : ⌊height x/(delta*(N:ℝ))⌋=⌊height y/(delta*(N:ℝ))⌋) :
    dist (field S height F delta ⌊height x/delta⌋)
      (field S height F delta ⌊height y/delta⌋)≤error := by
  obtain ⟨u,hu,heu,hreadu⟩ := field_realization S height F delta ⟨x,hTS hx,rfl⟩
  obtain ⟨v,hv,hev,hreadv⟩ := field_realization S height F delta ⟨y,hTS hy,rfl⟩
  rw [hreadu,hreadv]
  exact hcoh u hu v hv ((same_base_same_coarse N heu).trans
    (hcell.trans (same_base_same_coarse N hev).symm))

/-- Actual weak-Lipschitz two-entry fields supply a single pre-third source
and a single frozen base-grid field. Every later subset inherits the same
coarse-cell bounds, with the original palette mass ledger unchanged. -/
theorem select_frozen_field {A : Type*} (K : ℕ) (S : Finset A) (w : A → ℕ)
    (height : A → ℝ) (F : A → Fin 2 → ℝ) (L delta B : ℝ)
    (hL : 0≤L) (hd : 0<delta) (hB : 0≤B) (hF : ∀x∈S,‖F x‖≤B)
    (N : Fin (K+1) → ℕ) (hN : ∀i,0<N i) (hN0 : N 0=1)
    (hLip : ∀x∈S,∀y∈S,dist (F x) (F y)≤L*|height x-height y|) :
    ∃Spre⊆S,mass S w≤(modulus L)^(2*(K+1))*mass Spre w ∧
      (∀k,‖field Spre height F delta k‖≤B) ∧
      (∀x∈Spre,dist (field Spre height F delta ⌊height x/delta⌋) (F x)≤delta) ∧
      ∀T⊆Spre,∀i : Fin (K+1),∀x∈T,∀y∈T,
        ⌊height x/(delta*(N i:ℝ))⌋=⌊height y/(delta*(N i:ℝ))⌋ →
          dist (field Spre height F delta ⌊height x/delta⌋)
            (field Spre height F delta ⌊height y/delta⌋)≤delta*(N i:ℝ) := by
  obtain ⟨Spre,hsub,hret,hcoh⟩ := select_height_menu univ S w height F L hL
    (fun i => delta*(N i:ℝ)) (fun _ => 0)
    (fun i => mul_pos hd (by exact_mod_cast hN i)) hLip
  have H (i : Fin (K+1)) (x : A) (hx : x∈Spre) (y : A) (hy : y∈Spre)
      (he : ⌊height x/(delta*(N i:ℝ))⌋=⌊height y/(delta*(N i:ℝ))⌋) :
      dist (F x) (F y)≤delta*(N i:ℝ) := by
    exact (hcoh i (mem_univ i) x hx y hy (by simpa only [heightCell,sub_zero] using he)).le
  refine ⟨Spre,hsub,by simpa using hret,field_norm_le Spre height F delta B hB
    (fun x hx => hF x (hsub hx)),?_,?_⟩
  · intro x hx
    apply field_close_to_original Spre height F delta delta ?_ hx
    intro u hu v hv he
    have hh := H 0 u hu v hv
    simpa only [hN0,Nat.cast_one,mul_one] using hh
      (by simpa only [hN0,Nat.cast_one,mul_one] using he)
  · intro T hT i x hx y hy he
    exact frozen_field_coarse Spre T hT height F delta (N i) (delta*(N i:ℝ)) (H i) hx hy he

end NativeFrozenTimeField
