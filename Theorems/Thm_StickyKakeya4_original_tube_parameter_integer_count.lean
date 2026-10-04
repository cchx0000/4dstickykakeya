import Theorems.Thm_StickyKakeya4_original_three_dimensional_cap_count
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace OriginalTubeParameterIntegerCount
open Classical OriginalThreeDimensionalCapCount

lemma floor_mesh_error (rho a : ℝ) (hrho : 0<rho) :
    |rho*(⌊a/rho⌋:ℤ)-a|≤rho := by
  have hlo := (le_div_iff₀ hrho).mp (Int.floor_le (a/rho))
  have hhi := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (a/rho))
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo,hhi]

lemma three_fixed_coordinate_mass (S : Finset (Fin 3→ℤ))
    (i : Fin 3) (a : ℤ) (T M : ℝ) (hT : 0≤T) (hM : 0≤M)
    (hfixed : ∀ z∈S, z i=a)
    (hbound : ∀ j : Fin 3, j≠i → ((S.image (fun z => z j)).card : ℝ)*T≤M) :
    (S.card : ℝ)*T^2≤M^2 := by
  have hex : ∃ j k : Fin 3, j≠i ∧ k≠i ∧ ∀ l : Fin 3, l=i ∨ l=j ∨ l=k := by
    fin_cases i
    · refine ⟨1,2,by decide,by decide,?_⟩
      intro l; fin_cases l <;> simp
    · refine ⟨0,2,by decide,by decide,?_⟩
      intro l; fin_cases l <;> simp
    · refine ⟨0,1,by decide,by decide,?_⟩
      intro l; fin_cases l <;> simp
  obtain ⟨j,k,hji,hki,hcover⟩ := hex
  let f : (Fin 3→ℤ)→ℤ×ℤ := fun z => (z j,z k)
  have hinj : Set.InjOn f (↑S : Set (Fin 3→ℤ)) := by
    intro z hz v hv he
    funext l
    rcases hcover l with rfl | rfl | rfl
    · exact (hfixed z hz).trans (hfixed v hv).symm
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have hsub : S.image f⊆(S.image (fun z => z j)).product (S.image (fun z => z k)) := by
    rintro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz,Finset.mem_image_of_mem _ hz⟩
  have hcard : (S.card : ℝ)≤((S.image (fun z => z j)).card : ℝ)*(S.image (fun z => z k)).card := by
    have hn := (Finset.card_le_card hsub).trans_eq (Finset.card_product _ _)
    rw [Finset.card_image_of_injOn hinj] at hn
    exact_mod_cast hn
  have hprod := mul_le_mul (hbound j hji) (hbound k hki)
    (mul_nonneg (Nat.cast_nonneg _) hT) hM
  have hscaled := mul_le_mul_of_nonneg_right hcard (sq_nonneg T)
  nlinarith only [hprod,hscaled]

end OriginalTubeParameterIntegerCount
