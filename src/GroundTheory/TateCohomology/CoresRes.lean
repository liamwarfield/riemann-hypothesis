module

public import GroundTheory.TateCohomology.ResCores
public import GroundTheory.TateCohomology.Annihilation

@[expose] public section

section -- merged from GroundTheory.TateCohomology.CoresRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Additive

variable [Fintype G]

instance tateCohomologyFunctor_additive (n : ℤ) :
    (tateCohomologyFunctor (R := k) (G := G) n).Additive := by
  unfold tateCohomologyFunctor
  infer_instance

end Additive

section Rep

variable (S : Subgroup G) [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex


omit [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)] in
theorem indResAdjunction_counit_app_hom_mk (A : Rep.{u} k G) (g : G) (a : A) :
    ((indResAdjunction k S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (res S.subtype A).ρ g a) = A.ρ g⁻¹ a := by
  change ((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = _
  simp

theorem unit_comp_indCoindIso_inv_comp_counit (A : Rep.{u} k G) :
    (resCoindAdjunction.{u, u} k S.subtype).unit.app A ≫ (indCoindIso (res S.subtype A)).inv ≫
      (indResAdjunction.{u} k S.subtype).counit.app A = S.index • 𝟙 A := by
  ext a
  change ((indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (((resCoindAdjunction.{u, u} k S.subtype).unit.app A).hom a)) =
    S.index • a
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coindToInd_apply, map_sum]
  refine (Finset.sum_congr rfl (g := fun _ => a) fun x _ => ?_).trans ?_
  · induction x using Quotient.inductionOn with
    | h g =>
      rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
      change A.ρ g⁻¹ (A.ρ g a) = a
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · rw [Finset.sum_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]
    rfl

end Rep

section Tate

variable [Fintype G] (S : Subgroup G) [Fintype S]


open scoped Classical in
theorem tateIndIso_inv_eq (B : Rep.{u} k S) (n : ℤ) :
    (tateIndIso S B n).inv =
      (tateCoindIso S B n).inv ≫ (tateCohomologyFunctor n).map (indCoindIso.{u, u, u} B).inv :=
  rfl

theorem tateRes_app_comp_tateCores_app (A : Rep.{u} k G) (n : ℤ) :
    (tateRes S n).app A ≫ (tateCores S n).app A = S.index • 𝟙 (tateCohomology A n) := by
  rw [tateRes_app, tateCores_app, tateIndIso_inv_eq, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
    unit_comp_indCoindIso_inv_comp_counit, Functor.map_nsmul]
  exact congrArg (S.index • ·) ((tateCohomologyFunctor n).map_id A)

end Tate

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.TateGroupIso
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section Bijective

variable {k H K : Type u} [CommRing k] [Group H] [Group K] [Fintype H] [Fintype K]
  (f : H →* K) (hf : Function.Bijective f)

include hf

theorem norm_res_of_bijective (B : Rep.{u} k K) (m : B) :
    (res f B).ρ.norm m = B.ρ.norm m := by
  rw [Representation.norm, Representation.norm, LinearMap.sum_apply, LinearMap.sum_apply]
  exact Fintype.sum_bijective f hf _ _ fun _ => rfl

theorem isZero_tateCohomology_zero_res_iff (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) 0) ↔ IsZero (tateCohomology B 0) := by
  rw [isZero_tateCohomology_zero_iff_forall, isZero_tateCohomology_zero_iff_forall]
  have hinv : ∀ x : B, x ∈ (res f B).ρ.invariants ↔ x ∈ B.ρ.invariants := fun x => by
    simp only [Representation.mem_invariants]
    constructor
    · intro h g
      obtain ⟨h', rfl⟩ := hf.2 g
      exact h h'
    · intro h h'
      exact h (f h')
  constructor
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).2 hx)
    exact ⟨m, by rw [← norm_res_of_bijective f hf]; exact hm⟩
  · intro h x hx
    obtain ⟨m, hm⟩ := h x ((hinv x).1 hx)
    exact ⟨m, by rw [norm_res_of_bijective f hf]; exact hm⟩

theorem tateAcyclic_res_of_sum_eq (B : Rep.{u} k K) (φ : B.V →ₗ[k] B.V)
    (hφ : ∀ m : B, ∑ g : K, B.ρ g (φ (B.ρ g⁻¹ m)) = m) : TateAcyclic (res f B) :=
  tateAcyclic_of_sum_eq (res f B) φ fun m => by
    conv_rhs => rw [← hφ m]
    exact Fintype.sum_bijective f hf _ _ fun h => by
      simp only [MonoidHom.comp_apply, map_inv]

theorem isZero_tateCohomology_res_iff (n : ℤ) (B : Rep.{u} k K) :
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n) := by
  refine Int.inductionOn' (motive := fun n => ∀ B : Rep.{u} k K,
    IsZero (tateCohomology (res f B) n) ↔ IsZero (tateCohomology B n)) n 0
    (fun B => isZero_tateCohomology_zero_res_iff f hf B) ?_ ?_ B
  · intro n _ ih B
    have hX' : ((coindSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (coindSES_shortExact B)
    have h2 : TateAcyclic ((coindSES.obj B).map (resFunctor f)).X₂ := by
      rw [ShortComplex.map_X₂, coindSES_obj_X₂]
      exact tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' n) (isIso_δ_of_tateAcyclic hX' h2 n)
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, coindSES_obj_X₁] at e1
    rw [← e1.isZero_iff, ← (coindShiftIso B n).isZero_iff]
    exact ih _
  · intro n _ ih B
    have hX' : ((indSES.obj B).map (resFunctor f)).ShortExact :=
      (shortExact_res f).2 (indSES_shortExact B)
    have h2 : TateAcyclic ((indSES.obj B).map (resFunctor f)).X₂ := by
      classical
      rw [ShortComplex.map_X₂, indSES_obj_X₂]
      exact (tateAcyclic_res_of_sum_eq f hf _ (coindBotProj _) (sum_coindBotProj _)).of_iso
        ((resFunctor f).mapIso (indCoindIso _))
    have e1 := @asIso _ _ _ _ (TateCohomology.δ hX' (n - 1))
      (isIso_δ_of_tateAcyclic hX' h2 (n - 1))
    rw [ShortComplex.map_X₃, ShortComplex.map_X₁, indSES_obj_X₃] at e1
    rw [e1.isZero_iff, (indShiftIso B (n - 1)).isZero_iff, sub_add_cancel]
    exact ih _

theorem tateAcyclic_res_iff (B : Rep.{u} k K) : TateAcyclic (res f B) ↔ TateAcyclic B :=
  forall_congr' fun n => isZero_tateCohomology_res_iff f hf n B

end Bijective

section Consequences

variable {k G : Type u} [CommRing k] [Group G]


omit [Group G] in
theorem res_res {H K : Type u} [Group H] [Group K] [Group G] (f : H →* K) (g : K →* G)
    (A : Rep.{u} k G) : res f (res g A) = res (g.comp f) A :=
  rfl

theorem CohTrivial.tateAcyclic [Fintype G] {A : Rep.{u} k G} (h : CohTrivial A) :
    TateAcyclic A := by
  let _ : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  have hbij : Function.Bijective (⊤ : Subgroup G).subtype :=
    ⟨Subgroup.subtype_injective _, fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩⟩
  have h1 : TateAcyclic (res (⊤ : Subgroup G).subtype A) := h ⊤
  exact (tateAcyclic_res_iff _ hbij A).1 h1

theorem tateAcyclic_res_conj {A : Rep.{u} k G} (U V : Subgroup G) [Fintype U] [Fintype V] (g : G)
    (hUV : ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ V) (hV : TateAcyclic (res V.subtype A)) :
    TateAcyclic (res U.subtype A) := by
  let c : U →* V :=
    { toFun := fun u => ⟨g⁻¹ * u * g, (hUV u).1 u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hinj : Function.Injective c := fun a b hab => by
    have h := congrArg (fun x : V => (x : G)) hab
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  have hsurj : Function.Surjective c := fun v =>
    ⟨⟨g * v * g⁻¹, (hUV _).2 (by simp [mul_assoc])⟩, Subtype.ext (by simp [c, mul_assoc])⟩
  have hc := (tateAcyclic_res_iff c ⟨hinj, hsurj⟩ (res V.subtype A)).2 hV
  let e : A.V ≃ₗ[k] A.V := LinearEquiv.ofLinearMap (A.ρ g⁻¹) (A.ρ g)
    (LinearMap.ext fun a => by simp) (LinearMap.ext fun a => by simp)
  let eqv : (res U.subtype A).ρ.Equiv (res c (res V.subtype A)).ρ :=
    Representation.Equiv.mk e fun u => LinearMap.ext fun a => by
      change A.ρ g⁻¹ (A.ρ u a) = A.ρ (g⁻¹ * u * g) (A.ρ g⁻¹ a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc,
        mul_inv_cancel, mul_one]
  exact hc.of_iso (Rep.mkIso eqv)

end Consequences

end GroundTheory.GroupCoh
end
