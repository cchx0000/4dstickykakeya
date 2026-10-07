import Theorems.Thm_StickyKakeya4_native_local_offset_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeLocalOffsetMenu
open Classical Finset NativeMatrixHeightWholePoint NativeLocalOffsetSelection
open scoped BigOperators

/-- Literal equality of every surviving original-point incidence fiber. -/
def WholePoints {P T : Type*} (S U : Finset (P × T)) : Prop :=
  U⊆S ∧ ∀p∈U.image Prod.fst,U.filter (fun z => z.1=p)=S.filter (fun z => z.1=p)

lemma whole_refl {P T : Type*} (S : Finset (P × T)) : WholePoints S S :=
  ⟨Subset.refl _,fun _ _ => rfl⟩

lemma whole_trans {P T : Type*} {S U V : Finset (P × T)}
    (hSU : WholePoints S U) (hUV : WholePoints U V) : WholePoints S V := by
  refine ⟨hUV.1.trans hSU.1,?_⟩
  intro p hp
  exact (hUV.2 p hp).trans (hSU.2 p (image_subset_image hUV.1 hp))

lemma lift_point_image {P T : Type*} (S : Finset (P × T)) (B : Finset P)
    (hB : B⊆S.image Prod.fst) : (edgeLift S Prod.fst B).image Prod.fst=B := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
    simpa only [hzp] using (mem_filter.mp hz).2
  · intro p hp
    obtain ⟨z,hz,hzp⟩ := mem_image.mp (hB hp)
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,by simpa only [hzp] using hp⟩,hzp⟩

/-- Only actual coordinate, incidence, angular-image, and local field data.
No offset-image or selected-set conclusion is included in this predicate. -/
def LocalData {P T Angle Cell : Type*} {k ell : ℕ}
    (S : Finset (P × T)) (angle : T → Angle) (physical : P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : ℝ) : Prop :=
  (∀z∈S,∀j,|tangent z.2 j| ≤ B) ∧
  (∀p∈S.image Prod.fst,∀i j,|field p i j| ≤ (1/4:ℝ)) ∧
  (∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,physical p=physical q →
    ∀i j,|field p i j-field q i j| ≤ v) ∧
  (∀z∈S,∀u∈S,angle z.2=angle u.2 →
    (∀j,|tangent z.2 j-tangent u.2 j| ≤ A/M) ∧
    (∀i,|normal z.2 i-normal u.2 i| ≤ A/M)) ∧
  (∀z∈S,∀i,|normal z.2 i-(∑j,field z.1 i j*tangent z.2 j)-xi z.1 i| ≤ E) ∧
  (∀p∈S.image Prod.fst,
    lower ≤ (((S.filter (fun z => z.1=p)).image (fun z => angle z.2)).card:ℝ)) ∧
  (∀c,(((physicalFiber S physical c).image (fun z => angle z.2)).card:ℝ) ≤ upper)

/-- The angular lower survives by EXACT whole-fiber equality, not by an
unsupported monotonicity claim for lower cardinalities. -/
lemma localData_of_whole {P T Angle Cell : Type*} {k ell : ℕ}
    {S U : Finset (P × T)} (angle : T → Angle) (physical : P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : ℝ) (hWhole : WholePoints S U)
    (H : LocalData S angle physical tangent normal field xi E M v A B lower upper) :
    LocalData U angle physical tangent normal field xi E M v A B lower upper := by
  obtain ⟨hT,hF,hVar,hAngle,hRes,hLower,hUpper⟩ := H
  have hP : U.image Prod.fst⊆S.image Prod.fst := image_subset_image hWhole.1
  refine ⟨(fun z hz => hT z (hWhole.1 hz)),(fun p hp => hF p (hP hp)),
    (fun p hp q hq => hVar p (hP hp) q (hP hq)),
    (fun z hz u hu => hAngle z (hWhole.1 hz) u (hWhole.1 hu)),
    (fun z hz => hRes z (hWhole.1 hz)),?_,?_⟩
  · intro p hp
    rw [hWhole.2 p hp]
    exact hLower p (hP hp)
  · intro c
    have hsub : physicalFiber U physical c⊆physicalFiber S physical c :=
      filter_subset_filter _ hWhole.1
    exact (Nat.cast_le.mpr (card_le_card (image_subset_image hsub))).trans (hUpper c)

/-- One actual source-count/maximum-weight choice, in whole-fiber form. -/
theorem select_one {P T Angle Cell : Type*} {k ell : ℕ}
    (S : Finset (P × T)) (weight : P → ℕ) (angle : T → Angle) (physical : P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : ℝ) (hk : k ≤ 2)
    (hE : 0 ≤ E) (hM : 0 < M) (hv : 0 ≤ v) (hA : 0 < A) (hB : 0 ≤ B) (hL : 0 < lower)
    (H : LocalData S angle physical tangent normal field xi E M v A B lower upper) :
    ∃U,WholePoints S U ∧
      mass (S.image Prod.fst) weight ≤ ⌈((3:ℝ)^ell*upper)/lower⌉₊*mass (U.image Prod.fst) weight ∧
      (S.Nonempty → U.Nonempty) ∧
      ∀z∈U,∀u∈U,physical z.1=physical u.1 → ∀i,|xi z.1 i-xi u.1 i| < 2*E+2*A/M+2*B*v := by
  obtain ⟨hT,hF,hVar,hAngle,hRes,hLower,hUpper⟩ := H
  obtain ⟨_hN,Bpoints,hBpoints,hsub,hret,_hphysical,hfiber,hne,hcoh⟩ :=
    actual_weighted_offset_selection S angle physical tangent normal field xi E M v A B lower upper
      hk hE hM hv hA hB hL hT hF hVar hAngle hRes hLower hUpper weight
  have hImage := lift_point_image S Bpoints hBpoints
  refine ⟨edgeLift S Prod.fst Bpoints,⟨hsub,?_⟩,?_,hne,hcoh⟩
  · intro p hp
    exact hfiber p (hImage ▸ hp)
  · simpa only [hImage] using hret

/-- Fixed prepared menus are realized by genuine selections on the same
original family. Each later source keeps the entire original angular point
fiber, so the original lower bounds remain valid in every round. -/
theorem select_prepared_menu {P T Angle Cell I : Type*} [DecidableEq I] {k ell : ℕ}
    (menu : Finset I) (S : Finset (P × T)) (weight : P → ℕ)
    (angle : I → T → Angle) (physical : I → P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : I → ℝ) (hk : k ≤ 2)
    (hE : ∀i,0 ≤ E i) (hM : ∀i,0 < M i) (hv : ∀i,0 ≤ v i)
    (hA : ∀i,0 < A i) (hB : ∀i,0 ≤ B i) (hL : ∀i,0 < lower i)
    (H : ∀i,LocalData S (angle i) (physical i) tangent normal field xi
      (E i) (M i) (v i) (A i) (B i) (lower i) (upper i)) :
    ∃U,WholePoints S U ∧
      mass (S.image Prod.fst) weight ≤
        (∏i∈menu,⌈((3:ℝ)^ell*upper i)/lower i⌉₊)*mass (U.image Prod.fst) weight ∧
      (S.Nonempty → U.Nonempty) ∧
      ∀i∈menu,∀z∈U,∀u∈U,physical i z.1=physical i u.1 →
        ∀j,|xi z.1 j-xi u.1 j| < 2*E i+2*A i/M i+2*B i*v i := by
  induction menu using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨S,whole_refl S,?_,fun h => h,?_⟩
      · simp
      · intro i hi
        simp at hi
  | @insert i menu hi ih =>
      obtain ⟨S1,hS1,hret1,hne1,hcoh1⟩ := select_one S weight (angle i) (physical i) tangent normal field xi
        (E i) (M i) (v i) (A i) (B i) (lower i) (upper i) hk
        (hE i) (hM i) (hv i) (hA i) (hB i) (hL i) (H i)
      have H1 : ∀j,LocalData S1 (angle j) (physical j) tangent normal field xi
          (E j) (M j) (v j) (A j) (B j) (lower j) (upper j) := by
        intro j
        exact localData_of_whole (angle j) (physical j) tangent normal field xi
          (E j) (M j) (v j) (A j) (B j) (lower j) (upper j) hS1 (H j)
      obtain ⟨U,hU,hret,hne,hcoh⟩ := ih S1 H1
      refine ⟨U,whole_trans hS1 hU,?_,fun h => hne (hne1 h),?_⟩
      · calc
          _ ≤ ⌈((3:ℝ)^ell*upper i)/lower i⌉₊*mass (S1.image Prod.fst) weight := hret1
          _ ≤ ⌈((3:ℝ)^ell*upper i)/lower i⌉₊*
              ((∏j∈menu,⌈((3:ℝ)^ell*upper j)/lower j⌉₊)*mass (U.image Prod.fst) weight) :=
            Nat.mul_le_mul_left _ hret
          _ = _ := by rw [prod_insert hi]; ring
      · intro j hj z hz u hu heq
        rcases mem_insert.mp hj with rfl | hj
        · exact hcoh1 z (hU.1 hz) u (hU.1 hu) heq
        · exact hcoh j hj z hz u hu heq

lemma whole_mass_eq_card {P T : Type*} {S U : Finset (P × T)} (H : WholePoints S U) :
    mass (U.image Prod.fst) (fun p => (S.filter (fun z => z.1=p)).card)=U.card := by
  calc
    _ = ∑p∈U.image Prod.fst,(U.filter (fun z => z.1=p)).card := by
      apply sum_congr rfl
      intro p hp
      rw [H.2 p hp]
    _ = _ := (card_eq_sum_card_image Prod.fst U).symm

/-- The original-edge cardinality form has the same product charge and
literal original point fibers; it is not a product of shrinking angular counts. -/
theorem select_prepared_incidences {P T Angle Cell I : Type*} [DecidableEq I] {k ell : ℕ}
    (menu : Finset I) (S : Finset (P × T))
    (angle : I → T → Angle) (physical : I → P → Cell)
    (tangent : T → Fin k → ℝ) (normal : T → Fin ell → ℝ)
    (field : P → Fin ell → Fin k → ℝ) (xi : P → Fin ell → ℝ)
    (E M v A B lower upper : I → ℝ) (hk : k ≤ 2)
    (hE : ∀i,0 ≤ E i) (hM : ∀i,0 < M i) (hv : ∀i,0 ≤ v i)
    (hA : ∀i,0 < A i) (hB : ∀i,0 ≤ B i) (hL : ∀i,0 < lower i)
    (H : ∀i,LocalData S (angle i) (physical i) tangent normal field xi
      (E i) (M i) (v i) (A i) (B i) (lower i) (upper i)) :
    ∃U,WholePoints S U ∧ S.card ≤ (∏i∈menu,⌈((3:ℝ)^ell*upper i)/lower i⌉₊)*U.card ∧
      (S.Nonempty → U.Nonempty) ∧
      ∀i∈menu,∀z∈U,∀u∈U,physical i z.1=physical i u.1 →
        ∀j,|xi z.1 j-xi u.1 j| < 2*E i+2*A i/M i+2*B i*v i := by
  let weight := fun p => (S.filter (fun z => z.1=p)).card
  obtain ⟨U,hU,hret,hne,hcoh⟩ := select_prepared_menu menu S weight angle physical tangent normal field xi
    E M v A B lower upper hk hE hM hv hA hB hL H
  have hmassS : mass (S.image Prod.fst) weight=S.card := whole_mass_eq_card (whole_refl S)
  have hmassU : mass (U.image Prod.fst) weight=U.card := whole_mass_eq_card hU
  rw [hmassS,hmassU] at hret
  exact ⟨U,hU,hret,hne,hcoh⟩

end NativeLocalOffsetMenu
