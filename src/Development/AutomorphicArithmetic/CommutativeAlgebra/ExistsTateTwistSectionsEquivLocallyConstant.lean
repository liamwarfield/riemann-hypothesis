module

public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistFinitary

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LocallyExactCech
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Et

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

variable {R : Type} [CommRing R]

abbrev sec (M : PMod R) (U : Scheme.{0}) : Type 1 := M.obj (op U)

abbrev rs (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (x : sec M U) : sec M V := (M.map g.op).hom x

abbrev ap {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} (x : sec M U) : sec N U := (α.app (op U)).hom x

def LocT (τ : GrothendieckTopology Scheme.{0}) (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ τ U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

def Inv (q : ℕ) (U : Scheme.{0}) : Prop := IsUnit (q : Γ(U, ⊤))

def Gen (τ : GrothendieckTopology Scheme.{0}) (q : ℕ) (M : PMod R) {U : Scheme.{0}} (g : sec M U) : Prop :=
  q • g = 0 ∧ (∀ (V : Scheme.{0}) (k : V ⟶ U) (c : ℕ), Nonempty V → c • rs M k g = 0 → q ∣ c) ∧
  ∀ (V : Scheme.{0}) (k : V ⟶ U) (y : sec M V), LocT τ V fun _ h => ∃ c : ℕ, rs M h y = c • rs M (h ≫ k) g

section Cech
variable {Y X : Scheme.{0}} (f : Y ⟶ X)




variable {f}

variable (f)


end Cech

end UpperTheory.Et

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleLocalPrimitiveRootAndRootsOfUnity
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.PrimLoc

open Polynomial

private theorem etale_adjoinRoot {A : Type} [CommRing A] (f : A[X]) (hf : f.Monic)
    (h : IsUnit (AdjoinRoot.mk f (derivative f))) : Algebra.Etale A (AdjoinRoot f) := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective v
  rw [← map_mul, ← map_one (AdjoinRoot.mk f), ← sub_eq_zero, ← map_sub,
    AdjoinRoot.mk_eq_zero] at hv
  obtain ⟨c, hc⟩ := hv
  let P : StandardEtalePair A :=
    { f := f, monic_f := hf, g := 1,
      cond := ⟨p, -c, 1, by rw [pow_one]; linear_combination hc⟩ }
  have hX : eval₂ (↑(Algebra.ofId A P.Ring)) P.X f = 0 := by
    simpa [aeval_def] using P.hasMap_X.1
  have hR : P.HasMap (AdjoinRoot.root f) :=
    ⟨by simp [P, AdjoinRoot.aeval_eq], by simp [P]⟩
  let e : AdjoinRoot f ≃ₐ[A] P.Ring :=
    AlgEquiv.ofAlgHom (AdjoinRoot.liftAlgHom f (Algebra.ofId A P.Ring) P.X hX)
      (P.lift (AdjoinRoot.root f) hR)
      (P.hom_ext (by simp)) (AdjoinRoot.algHom_ext (by simp))
  exact Algebra.Etale.of_equiv e.symm

private theorem exists_affine (U : Scheme.{0}) (x : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U), IsAffine V ∧ Etale j ∧ x ∈ Set.range j ∧ Nontrivial Γ(V, ⊤) := by
  obtain ⟨i, y, hy⟩ := U.affineCover.exists_eq x
  haveI : IsOpenImmersion (U.affineCover.f i) := U.affineCover.map_prop i
  refine ⟨U.affineCover.X i, U.affineCover.f i, ?_, inferInstance, ⟨y, hy⟩, ?_⟩
  · dsimp [Scheme.affineCover]
    infer_instance
  · exact RingHom.domain_nontrivial ((U.affineCover.X i).presheaf.germ ⊤ y trivial).hom

private theorem exists_cover (V₀ : Scheme.{0}) [IsAffine V₀] [Nontrivial Γ(V₀, ⊤)] (f : Γ(V₀, ⊤)[X])
    (hf : f.Monic) (hd : 0 < f.natDegree) (h : IsUnit (AdjoinRoot.mk f (derivative f))) :
    ∃ (V : Scheme.{0}) (g : V ⟶ V₀) (θ : Γ(V, ⊤)), IsAffine V ∧ Etale g ∧ Function.Surjective g ∧
      eval₂ g.appTop.hom θ f = 0 := by
  haveI : Module.Free Γ(V₀, ⊤) (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Finite Γ(V₀, ⊤) (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Nontrivial (AdjoinRoot f) := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    have hdim : 0 < (AdjoinRoot.powerBasis' hf).dim := by
      rw [AdjoinRoot.powerBasis'_dim]
      exact hd
    exact (AdjoinRoot.powerBasis' hf).basis.ne_zero ⟨0, hdim⟩ (Subsingleton.elim _ _)
  let φ : Γ(V₀, ⊤) ⟶ CommRingCat.of (AdjoinRoot f) :=
    CommRingCat.ofHom (algebraMap Γ(V₀, ⊤) (AdjoinRoot f))
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr
      ((RingHom.etale_algebraMap (R := Γ(V₀, ⊤)) (S := AdjoinRoot f)).mpr
        (etale_adjoinRoot f hf h))
  have hsφ : Surjective (Spec.map φ) := by
    rw [surjective_iff]
    intro y
    obtain ⟨p, hp⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Γ(V₀, ⊤)) (B := AdjoinRoot f) y
    refine ⟨p, ?_⟩
    show (Spec.map φ).base p = y
    rw [Spec.map_base]
    exact hp
  refine ⟨Spec (CommRingCat.of (AdjoinRoot f)), Spec.map φ ≫ V₀.isoSpec.inv,
    (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot f))).inv.hom (AdjoinRoot.root f),
    inferInstance, inferInstance, (surjective_iff _).mp inferInstance, ?_⟩
  have e1 : V₀.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(V₀, ⊤)).inv := by
    have := congrArg Scheme.Hom.appTop (Scheme.isoSpec_inv_toSpecΓ V₀)
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at this
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(V₀, ⊤)).hom, this, Iso.hom_inv_id]
  have e2 : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso _).hom ≫ φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot f))).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Scheme.Hom.comp_appTop, e1, e2, Iso.inv_hom_id_assoc, CommRingCat.hom_comp, ← hom_eval₂]
  simp [φ, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]

private theorem isUnit_restrict_basicOpen (X : Scheme.{0}) (a : Γ(X, ⊤)) :
    IsUnit ((X.basicOpen a).ι.appTop.hom a) := by
  have hb := Scheme.Opens.ι_preimage_self (X.basicOpen a)
  rw [Scheme.preimage_basicOpen] at hb
  apply RingedSpace.isUnit_of_isUnit_germ _ ⊤
  intro x hx
  have hx' : x ∈ (X.basicOpen a).toScheme.basicOpen
      ((ConcreteCategory.hom ((X.basicOpen a).ι.app ⊤)) a) := by
    rw [hb]
    trivial
  exact (Scheme.mem_basicOpen _ _ x hx).mp hx'

private theorem local_eq (U : Scheme.{0}) (s : Finset ℕ) (y : Γ(U, ⊤)) (t : ℕ → Γ(U, ⊤))
    (hd : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → IsUnit (t a - t b)) (hp : ∏ a ∈ s, (y - t a) = 0) :
    Loc U fun _ g => ∃ a ∈ s, g.appTop.hom y = g.appTop.hom (t a) := by
  classical
  let p : ℕ → Γ(U, ⊤) := fun a => ∏ b ∈ s.erase a, (y - t b)
  let O : s → U.Opens := fun a => U.basicOpen (p a)
  have hcov : TopologicalSpace.IsOpenCover O := by
    apply eq_top_iff.mpr
    intro x _
    let g := ConcreteCategory.hom (U.presheaf.germ ⊤ x trivial)
    have hz : ∏ a ∈ s, g (y - t a) = 0 := by rw [← map_prod, hp, map_zero]
    have hex : ∃ a ∈ s, ¬ IsUnit (g (y - t a)) := by
      by_contra hne
      push_neg at hne
      have hu : IsUnit (∏ a ∈ s, g (y - t a)) := IsUnit.prod_iff.mpr hne
      rw [hz] at hu
      exact not_isUnit_zero hu
    obtain ⟨a, ha, hna⟩ := hex
    have hoth : ∀ b ∈ s.erase a, IsUnit (g (y - t b)) := by
      intro b hb
      obtain ⟨hba, hbs⟩ := Finset.mem_erase.mp hb
      by_contra hnb
      have hu : IsUnit (g (t a - t b)) := (hd a ha b hbs (Ne.symm hba)).map g
      have he : g (t a - t b) = g (y - t b) + -(g (y - t a)) := by
        simp only [map_sub]
        ring
      rw [he] at hu
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h1 | h1
      · exact hnb h1
      · exact hna (IsUnit.neg_iff _ |>.mp h1)
    have hx : x ∈ O ⟨a, ha⟩ := by
      show x ∈ U.basicOpen (p a)
      rw [Scheme.mem_basicOpen_top]
      show IsUnit (g (p a))
      rw [map_prod]
      exact IsUnit.prod_iff.mpr hoth
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hx⟩
  let C := U.openCoverOfIsOpenCover O hcov
  refine ⟨Sieve.ofArrows C.X C.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro V g hg
  obtain ⟨⟨a, ha⟩, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  refine ⟨a, ha, ?_⟩
  have hu : IsUnit ((U.basicOpen (p a)).ι.appTop.hom (p a)) := isUnit_restrict_basicOpen U (p a)
  have hprod : (y - t a) * p a = 0 := by
    rw [Finset.mul_prod_erase s (fun b => y - t b) ha]
    exact hp
  have h2 := congrArg (U.basicOpen (p a)).ι.appTop.hom hprod
  rw [map_mul, map_zero] at h2
  have h3 := (hu.mul_left_eq_zero).mp h2
  rw [map_sub, sub_eq_zero] at h3
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply]
  exact congrArg c.appTop.hom h3

private theorem unit_deriv_cyclotomic {A : Type} [CommRing A] (q : ℕ) [NeZero q]
    (hq : IsUnit (q : A)) :
    IsUnit (AdjoinRoot.mk (cyclotomic q A) (derivative (cyclotomic q A))) := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q A
  have hm := congrArg (AdjoinRoot.mk (cyclotomic q A)) (congrArg derivative hg)
  rw [derivative_mul, map_add (f := _), map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero] at hm
  have hX : IsUnit (AdjoinRoot.mk (cyclotomic q A) (X : A[X])) := by
    have h1 := congrArg (AdjoinRoot.mk (cyclotomic q A)) hg
    rw [map_mul, AdjoinRoot.mk_self, zero_mul, map_sub, map_pow, map_one, sub_eq_zero] at h1
    exact IsUnit.of_pow_eq_one h1 (NeZero.ne q)
  have hl : IsUnit (AdjoinRoot.mk (cyclotomic q A) (derivative (X ^ q - 1 : A[X]))) := by
    rw [derivative_sub, derivative_one, sub_zero, derivative_X_pow, map_mul, map_pow]
    refine IsUnit.mul ?_ (hX.pow _)
    simpa using hq.map (AdjoinRoot.of (cyclotomic q A))
  rw [hm] at hl
  exact isUnit_of_mul_isUnit_left hl

private theorem unit_deriv_kummer {A : Type} [CommRing A] (q : ℕ) [NeZero q]
    (hq : IsUnit (q : A)) (u : A) (hu : IsUnit u) :
    IsUnit (AdjoinRoot.mk (X ^ q - C u) (derivative (X ^ q - C u))) := by
  have hr : (AdjoinRoot.root (X ^ q - C u)) ^ q = AdjoinRoot.of (X ^ q - C u) u := by
    have h1 := AdjoinRoot.eval₂_root (X ^ q - C u)
    simpa [sub_eq_zero] using h1
  have hR : IsUnit (AdjoinRoot.root (X ^ q - C u)) := by
    rw [← isUnit_pow_iff (NeZero.ne q), hr]
    exact hu.map _
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, map_pow, AdjoinRoot.mk_X]
  refine IsUnit.mul ?_ (hR.pow _)
  simpa using hq.map (AdjoinRoot.of (X ^ q - C u))

private theorem part_prim (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) :
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤)) := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ ?_).2 fun x => ?_
  · rintro V W g k ⟨ζ⟩
    exact ⟨ζ.map k.appTop.hom⟩
  obtain ⟨V₀, j, hV, hj, ⟨y, hy⟩, hnt⟩ := exists_affine U x
  have hq₀ : IsUnit ((q : ℕ) : Γ(V₀, ⊤)) := by simpa using hq.map j.appTop.hom
  obtain ⟨V, g, θ, hVa, hg, hs, hθ⟩ := exists_cover V₀ (cyclotomic q Γ(V₀, ⊤))
    (cyclotomic.monic q _) (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
    (unit_deriv_cyclotomic q hq₀)
  obtain ⟨z, hz⟩ := hs y
  refine ⟨V, g ≫ j, hVa, inferInstance, ⟨z, by simp [hz, hy]⟩,
    ⟨Subtype.mk θ ⟨by simpa using hq₀.map g.appTop.hom, ?_⟩⟩⟩
  rw [← map_cyclotomic_int, eval₂_map] at hθ
  rw [aeval_def]
  rwa [show algebraMap ℤ Γ(V, ⊤) = g.appTop.hom.comp (Int.castRingHom Γ(V₀, ⊤)) from
    Subsingleton.elim _ _]

private theorem part_kummer (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤)))
    (u : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ ?_).2 fun x => ?_
  · rintro V W g k ⟨v, hv⟩
    refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]
    ext
    simp only [Units.coe_map, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rfl
  obtain ⟨V₀, j, hV, hj, ⟨y, hy⟩, hnt⟩ := exists_affine U x
  have hq₀ : IsUnit ((q : ℕ) : Γ(V₀, ⊤)) := by simpa using hq.map j.appTop.hom
  have hu₀ : IsUnit (j.appTop.hom (u : Γ(U, ⊤))) := u.isUnit.map _
  obtain ⟨V, g, θ, hVa, hg, hs, hθ⟩ := exists_cover V₀ (X ^ q - C (j.appTop.hom (u : Γ(U, ⊤))))
    (monic_X_pow_sub_C _ (NeZero.ne q))
    (by rw [natDegree_X_pow_sub_C _]; exact NeZero.pos q)
    (unit_deriv_kummer q hq₀ _ hu₀)
  obtain ⟨z, hz⟩ := hs y
  have h1 : θ ^ q = g.appTop.hom (j.appTop.hom (u : Γ(U, ⊤))) := by
    simpa [eval₂_sub, sub_eq_zero] using hθ
  have hθu : IsUnit θ := (isUnit_pow_iff (NeZero.ne q)).1 (h1 ▸ hu₀.map _)
  refine ⟨V, g ≫ j, hVa, inferInstance, ⟨z, by simp [hz, hy]⟩, hθu.unit, ?_⟩
  ext
  simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_map, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  exact h1

end UpperTheory.Cb.PrimLoc

open UpperTheory.Cb.PrimLoc in
theorem UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity :
    ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  intro q _ U
  refine ⟨part_prim q U, ?_, ?_, part_kummer q U⟩
  · intro ζ ξ
    have hprod := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.2.1 ζ ξ
    have hdist : ∀ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ∀ b ∈ (Finset.range q).filter (fun a => a.Coprime q), a ≠ b →
          IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
      intro a ha b hb hab
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      apply (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q _).2.2.1 ζ a b
      intro hmod
      apply hab
      simpa [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] using hmod
    obtain ⟨S, hS, hall⟩ := local_eq U _ ξ.1 (fun a => ζ.1 ^ a) hdist hprod
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨a, ha, he⟩ := hall V g hg
    rw [Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨ZMod.unitOfCoprime a ha.2, ?_⟩
    rw [he, map_pow]
    congr 1
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha.1]
  · intro ζ x hx
    have hprod := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.1 ζ x hx
    have hdist : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q, a ≠ b →
          IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
      intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      apply (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q _).2.2.1 ζ a b
      intro hmod
      apply hab
      simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmod
    obtain ⟨S, hS, hall⟩ := local_eq U _ x (fun a => ζ.1 ^ a) hdist hprod
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨a, -, he⟩ := hall V g hg
    exact ⟨a, by rw [he, map_pow]⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace UpperTheory.Et

variable {R : Type} [CommRing R]

def prGen (R : Type) [CommRing R] (X : Scheme.{0}) : sec ((GlobalTheory.Et.freeOn R).obj X).obj X :=
  ap (toSheafify Scheme.proetaleTopology
    (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).obj (uliftYoneda.{1}.obj X)))
    (ModuleCat.freeMk (ULift.up (𝟙 X)))

section Cont
variable (R) (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T]

def cPre : PMod R where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} C(U.unop, T))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ⟨g.down.comp f.unop.base.hom⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def cSh : GlobalTheory.Et.Shv R := (presheafToSheaf _ _).obj (cPre R T)

def cSec {U : Scheme.{0}} (g : C(U, T)) : sec (cSh R T).obj U :=
  ap (toSheafify Scheme.proetaleTopology (cPre R T)) (ULift.up g)

variable {R T} {T' : Type} [AddCommGroup T'] [Module R T'] [TopologicalSpace T'] [IsTopologicalAddGroup T']
  [ContinuousConstSMul R T']

def cPreMap (u : T →L[R] T') : cPre R T ⟶ cPre R T' where
  app U := ModuleCat.ofHom
    { toFun := fun g => ⟨(⟨u, u.continuous⟩ : C(T, T')).comp g.down⟩
      map_add' := fun a b => congrArg ULift.up (ContinuousMap.ext fun x => map_add u _ _)
      map_smul' := fun r a => congrArg ULift.up (ContinuousMap.ext fun x => map_smul u r.down _) }
  naturality _ _ _ := rfl

def cMap (u : T →L[R] T') : cSh R T ⟶ cSh R T' := (presheafToSheaf _ _).map (cPreMap u)

end Cont

section Adic
variable (l : ℕ) [Fact l.Prime]

end Adic

end UpperTheory.Et

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyHoldsOfForallAndMonoAndInterAndPullback
open CategoryTheory Limits AlgebraicGeometry Opposite UpperTheory.Et

private theorem typeSheaf {τ : GrothendieckTopology Scheme.{0}} {R : Type} [CommRing R] {M : PMod R}
    (h : Presheaf.IsSheaf τ M) : Presieve.IsSheaf τ (M ⋙ forget _) := by
  have h1 := (Presheaf.isSheaf_iff_isSheaf_comp τ M (forget _)).mp h
  exact (isSheaf_iff_isSheaf_of_type τ _).mp h1

private theorem ap_rs {R : Type} [CommRing R] {M N : PMod R} (α : M ⟶ N) {V U : Scheme.{0}} (g : V ⟶ U)
    (y : sec M U) : ap α (rs M g y) = rs N g (ap α y) :=
  ConcreteCategory.congr_hom (α.naturality g.op) y

private theorem rs_comp {R : Type} [CommRing R] (M : PMod R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U)
    (z : sec M U) : rs M (f ≫ g) z = rs M f (rs M g z) := by
  simp [rs]

private theorem loc_mono {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : LocT τ U P) (hPQ : ∀ V g, P V g → Q V g) : LocT τ U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

private theorem loc_and {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : LocT τ U P) (h' : LocT τ U Q) :
    LocT τ U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨T, hT, hQ⟩ := h'
  exact ⟨S ⊓ T, τ.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

private theorem loc_top {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : LocT τ U P :=
  ⟨⊤, τ.top_mem U, fun V g _ => h V g⟩

theorem UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback :
    ∀ (τ : GrothendieckTopology Scheme.{0}),
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → LocT τ U P) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → (∀ V g, P V g → Q V g) → LocT τ U Q) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → LocT τ U Q → LocT τ U fun V g => P V g ∧ Q V g) ∧
    (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → LocT τ W fun V g => P V (g ≫ k)) ∧
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U (fun V g => LocT τ V fun W k => P W (k ≫ g)) → LocT τ U P) ∧
    (∀ (U : Scheme.{0}) (ι : Type 1) (s : Finset ι) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i ∈ s, LocT τ U (P i)) → LocT τ U fun V g => ∀ i ∈ s, P i V g) ∧
    (∀ (R : Type) [CommRing R] (M : PMod R), Presheaf.IsSheaf τ M → ∀ (U : Scheme.{0}) (z : sec M U), (LocT τ U fun _ g => rs M g z = 0) → z = 0) ∧
    (∀ (R : Type) [CommRing R] (M N : PMod R) (α : M ⟶ N), Presheaf.IsSheaf τ M → Presheaf.IsSheaf τ N → ∀ (U : Scheme.{0}), (∀ (V : Scheme.{0}) (_ : V ⟶ U), Function.Injective (ap α (U := V))) → ∀ z : sec N U, (LocT τ U fun V g => ∃ y : sec M V, ap α y = rs N g z) → ∃ y : sec M U, ap α y = z) := by
  intro τ
  refine ⟨fun U P h => loc_top h, fun U P Q h hPQ => loc_mono h hPQ,
    fun U P Q h h' => loc_and h h', ?_, ?_, ?_, ?_, ?_⟩
  · intro U W k P h
    obtain ⟨S, hS, hP⟩ := h
    exact ⟨S.pullback k, τ.pullback_stable k hS, fun V g hg => hP V (g ≫ k) hg⟩
  · intro U P h
    obtain ⟨S, hS, hP⟩ := h
    choose T hT hTP using hP
    refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), τ.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
    rintro V f ⟨W, f', g, hg, hf', rfl⟩
    exact hTP W g hg V f' hf'
  · intro U ι s P h
    classical
    induction s using Finset.induction_on with
    | empty => exact loc_top fun V g i hi => absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
      have h1 := h a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine loc_mono (loc_and h1 h2) ?_
      rintro V g ⟨hA, hB⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hA
      · exact hB i hi
  · intro R _ M hM U z hz
    obtain ⟨S, hS, hP⟩ := hz
    have hM' := typeSheaf hM
    refine (hM' S hS).isSeparatedFor.ext ?_
    intro V g hg
    change rs M g z = (ModuleCat.Hom.hom (M.map g.op)) 0
    rw [hP V g hg, map_zero]
  · intro R _ M N α hM hN U hinj z hz
    obtain ⟨S, hS, hP⟩ := hz
    choose y hy using hP
    have hM' := typeSheaf hM
    have hN' := typeSheaf hN
    let x : Presieve.FamilyOfElements (M ⋙ forget _) S.arrows := fun V g hg => y V g hg
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ he
      apply hinj Z (g₁ ≫ f₁)
      change ap α (rs M g₁ (y Y₁ f₁ h₁)) = ap α (rs M g₂ (y Y₂ f₂ h₂))
      rw [ap_rs, ap_rs, hy, hy, ← rs_comp, ← rs_comp, he]
    obtain ⟨t, ht, -⟩ := hM' S hS x hx
    refine ⟨t, (hN' S hS).isSeparatedFor.ext ?_⟩
    intro V g hg
    change rs N g (ap α t) = rs N g z
    rw [← ap_rs]
    change ap α ((M ⋙ forget _).map g.op t) = rs N g z
    rw [ht g hg]
    exact hy V g hg
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ContinuousSectionsBijectiveAdditiveNatural
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem cPre_isSheaf (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [ContinuousConstSMul R T] :
    Presheaf.IsSheaf Scheme.proetaleTopology.{0} (cPre R T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  have h := Presieve.isSheaf_of_le _ Scheme.proetaleTopology_le_fpqcTopology
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqcTopology_continuousMapPresheaf.{0, 0} T))
  have h' : Presieve.IsSheaf Scheme.proetaleTopology
      (continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1}) :=
    (Presieve.isSheaf_comp_uliftFunctor_iff _).2 h
  exact Presieve.isSheaf_iso _
    (NatIso.ofComponents (fun U => Iso.refl _) (by intros; rfl) :
      continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1} ≅ cPre R T ⋙ forget _) h'

theorem UpperTheory.continuousSections_bijective_additive_natural :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0}),
    Function.Bijective (cSec R T (U := U)) ∧ (∀ a b : C(U, T), cSec R T (a + b) = cSec R T a + cSec R T b) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ U) (a : C(U, T)), rs _ g (cSec R T a) = cSec R T (a.comp g.base.hom)) ∧
    ∀ (T' : Type) [AddCommGroup T'] [Module R T'] [TopologicalSpace T'] [IsTopologicalAddGroup T'] [ContinuousConstSMul R T'] (u : T →L[R] T') (a : C(U, T)), ap (cMap u).hom (cSec R T a) = cSec R T' ((⟨u, u.continuous⟩ : C(T, T')).comp a) := by
  intro R _ T _ _ _ _ _ U
  haveI : IsIso (toSheafify Scheme.proetaleTopology (cPre R T)) :=
    isIso_toSheafify _ (cPre_isSheaf R T)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hb := ConcreteCategory.bijective_of_isIso
      ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U))
    exact hb.comp Equiv.ulift.symm.bijective
  · intro a b
    exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U)))
      (ULift.up a) (ULift.up b)
  · intro V g a
    exact (congrArg (fun f => ModuleCat.Hom.hom f (ULift.up a))
      ((toSheafify Scheme.proetaleTopology (cPre R T)).naturality g.op)).symm
  · intro T' _ _ _ _ _ u a
    exact congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) (ULift.up a))
      (toSheafify_naturality Scheme.proetaleTopology (cPreMap u)).symm
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleLocallyHoldsOfPointwiseCoverOrAffineLocal
open CategoryTheory Limits AlgebraicGeometry Opposite UpperTheory.Et

private theorem UpperTheory.locally_of_etale_cover (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), Etale g ∧ x ∈ Set.range g ∧ P V g) :
    LocT Scheme.etaleTopology U P := by
  choose V g hg hx hP' using h
  refine ⟨Sieve.ofArrows V g, ?_, ?_⟩
  · exact Precoverage.generate_mem_toGrothendieck
      ((Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ⟨x, hx x⟩, hg⟩)
  · rintro W f ⟨Y, k, _, ⟨i⟩, rfl⟩
    exact hP _ _ _ _ (hP' i)

theorem UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local :
    ∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    ((∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), Etale g ∧ x ∈ Set.range g ∧ P V g) → LocT Scheme.etaleTopology U P) ∧
    ((∀ (A : CommRingCat.{0}) (g : Spec A ⟶ U), LocT Scheme.etaleTopology (Spec A) fun V k => P V (k ≫ g)) → LocT Scheme.etaleTopology U P) := by
  intro U P hP
  refine ⟨UpperTheory.locally_of_etale_cover U P hP, fun hA => ?_⟩
  obtain ⟨-, -, -, h4, h5, -⟩ := UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology
  apply h5
  apply UpperTheory.locally_of_etale_cover U _
  · intro V W g k hV
    simpa only [Category.assoc] using h4 V W k _ hV
  · intro x
    exact ⟨_, U.affineCover.f (U.affineCover.idx x), inferInstance,
      U.affineCover.covers x, hA _ _⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistGeneratorOfPrimitiveRootAndRootsEtaleLo
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

theorem UpperTheory.tateTwist_generator_of_primitiveRoot_and_roots_etaleLocal :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}), (∀ ζ : GlobalTheory.EtC.Prim q Γ(U, ⊤), Gen Scheme.etaleTopology q (GlobalTheory.EtC.tw q i).obj (GlobalTheory.EtC.twGen i ζ)) ∧ (UpperTheory.Et.Inv q U → LocT Scheme.etaleTopology U fun V _ => Nonempty (GlobalTheory.EtC.Prim q Γ(V, ⊤))) := by
  intro q _ i U
  obtain ⟨-, h2, h3, h4, -⟩ := UpperTheory.Cb.tateTwist_sections_locally_generated q i
  refine ⟨fun ζ => ⟨?_, ?_, ?_⟩, fun hq => (UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq⟩
  · have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (ZMod.natCast_self q)
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q, h0, zero_smul]
  · intro V k c hV hc
    haveI := hV
    refine h3 V (ζ.map k.appTop.hom) c ?_
    rw [← h4 V U k ζ]
    exact hc
  · intro V k y
    obtain ⟨S, hS, h⟩ := h2 V (ζ.map k.appTop.hom) y
    refine ⟨S, hS, fun W g hg => ?_⟩
    obtain ⟨c, hc⟩ := h W g hg
    refine ⟨c, hc.trans ?_⟩
    have e : GlobalTheory.EtC.twGen i ((ζ.map k.appTop.hom).map g.appTop.hom) =
        GlobalTheory.EtC.Sec.res (g ≫ k) (GlobalTheory.EtC.twGen i ζ) := by
      rw [← h4 W V g, ← h4 V U k]
      simp [GlobalTheory.EtC.Sec.res]
    rw [e]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ConstantSheafCyclicGeneratorOfOrder
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem UpperTheory.continuousSection_nsmul (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T]
    [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0})
    (a : C(U, T)) (c : ℕ) : cSec R T (c • a) = c • cSec R T a := by
  exact map_nsmul (AddMonoidHom.mk' (cSec R T (U := U)) (UpperTheory.continuousSections_bijective_additive_natural R T U).2.1) c a

private theorem UpperTheory.restriction_comp {R : Type} [CommRing R] (M : PMod R) {W' W V : Scheme.{0}}
    (l : W' ⟶ W) (h : W ⟶ V) (z : sec M V) : rs M (l ≫ h) z = rs M l (rs M h z) := by
  simp only [rs, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem UpperTheory.constantSheaf_cyclic_generator_of_order :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [DiscreteTopology T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (q : ℕ) (t : T), q • t = 0 → (∀ c : ℕ, c • t = 0 → q ∣ c) → (∀ x : T, ∃ c : ℕ, x = c • t) → ∀ U : Scheme.{0}, Gen Scheme.etaleTopology q (cSh R T).obj (cSec R T (ContinuousMap.const U t)) := by
  intro R _ T _ _ _ _ _ _ q t hq hmin hgen U
  have hsm : ∀ (W : Scheme.{0}) (a : C(W, T)) (c : ℕ), cSec R T (c • a) = c • cSec R T a :=
    fun W a c => UpperTheory.continuousSection_nsmul R T W a c
  have h0 : ∀ W : Scheme.{0}, cSec R T (0 : C(W, T)) = 0 := fun W =>
    map_zero (AddMonoidHom.mk' (cSec R T (U := W)) (UpperTheory.continuousSections_bijective_additive_natural R T W).2.1)
  have hrs : ∀ (V : Scheme.{0}) (k : V ⟶ U),
      rs (cSh R T).obj k (cSec R T (ContinuousMap.const U t)) =
        cSec R T (ContinuousMap.const V t) := by
    intro V k
    rw [(UpperTheory.continuousSections_bijective_additive_natural R T U).2.2.1]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsm, show q • ContinuousMap.const U t = 0 by ext; simp [hq], h0]
  · intro V k c hV hc
    obtain ⟨v⟩ := hV
    rw [hrs, ← hsm, ← h0 V] at hc
    have he := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.1 hc
    have hv : c • t = 0 := by simpa using congrArg (fun f : C(V, T) => f v) he
    exact hmin c hv
  · intro V k y
    obtain ⟨b, rfl⟩ := (UpperTheory.continuousSections_bijective_additive_natural R T V).1.2 y
    refine (UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local V _ ?_).1 ?_
    · rintro W W' g' k' ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [UpperTheory.restriction_comp _ k' g', hc, Category.assoc, UpperTheory.restriction_comp _ k' (g' ≫ k)]
      exact map_nsmul ((cSh R T).obj.map k'.op).hom c _
    · intro x
      obtain ⟨c, hc⟩ := hgen (b x)
      let O : V.Opens := ⟨b ⁻¹' {b x}, (isOpen_discrete _).preimage b.continuous⟩
      refine ⟨O, O.ι, inferInstance, ?_, c, ?_⟩
      · rw [Scheme.Opens.range_ι]
        show b x ∈ ({b x} : Set T)
        exact Set.mem_singleton _
      · rw [(UpperTheory.continuousSections_bijective_additive_natural R T V).2.2.1, hrs, ← hsm]
        congr 1
        ext w
        have hw : O.ι w ∈ (O : Set V) := Scheme.Opens.range_ι O ▸ Set.mem_range_self w
        have hw' : b (O.ι w) = b x := hw
        simp [hw', hc]
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.SecLc
open UpperTheory.Et

variable {R : Type} [CommRing R]

private theorem rs_comp (M : PMod R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (z : sec M U) :
    rs M (f ≫ g) z = rs M f (rs M g z) := by
  simp [rs]

private theorem rs_nsmul (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (z : sec M U) :
    rs M g (c • z) = c • rs M g z :=
  map_nsmul _ _ _

private abbrev Rel (M N : PMod R) {U : Scheme.{0}} (g : sec M U) (h : sec N U) (y : sec M U)
    (z : sec N U) : Prop :=
  LocT Scheme.etaleTopology U fun _ k => ∃ c : ℕ, rs M k y = c • rs M k g ∧ rs N k z = c • rs N k h

end UpperTheory.Cb.SecLc

private theorem exists_sec_locT_rs_eq_of_compatible {R : Type} [CommRing R] (N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) {U : Scheme}
    (P : (V : Scheme) → (V ⟶ U) → Prop) (hP : UpperTheory.Et.LocT Scheme.etaleTopology U P)
    (s : ∀ (V : Scheme) (k : V ⟶ U), P V k → UpperTheory.Et.sec N V)
    (hc : ∀ (V1 V2 W : Scheme) (k1 : V1 ⟶ U) (k2 : V2 ⟶ U) (f1 : W ⟶ V1) (f2 : W ⟶ V2)
      (h1 : P V1 k1) (h2 : P V2 k2),
      f1 ≫ k1 = f2 ≫ k2 → UpperTheory.Et.rs N f1 (s V1 k1 h1) = UpperTheory.Et.rs N f2 (s V2 k2 h2)) :
    ∃ z : UpperTheory.Et.sec N U, UpperTheory.Et.LocT Scheme.etaleTopology U
      fun V k => ∃ hk : P V k, UpperTheory.Et.rs N k z = s V k hk := by
  obtain ⟨S, hS, hSP⟩ := hP
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology N (forget _)).mp hN) S hS
  let x : Presieve.FamilyOfElements (N ⋙ forget _) S.arrows := fun V k hk => s V k (hSP V k hk)
  have hx : x.Compatible := by
    intro Y1 Y2 Z g1 g2 f1 f2 h1 h2 hcomm
    exact hc Y1 Y2 Z f1 f2 g1 g2 _ _ hcomm
  obtain ⟨z, hz, -⟩ := hsh x hx
  exact ⟨z, S, hS, fun V k hk => ⟨hSP V k hk, hz k hk⟩⟩

private theorem pmod_rs_zero {R : Type} [CommRing R] (M : UpperTheory.Et.PMod R) {V U : Scheme}
    (k : V ⟶ U) : UpperTheory.Et.rs M k 0 = 0 := by
  simpa using UpperTheory.Cb.SecLc.rs_nsmul M k 0 0

private theorem nsmul_eq_nsmul_of_nsmul_eq_nsmul_of_exact_order {A B : Type*} [AddCommGroup A] [AddCommGroup B] (q : ℕ) (hq : 0 < q)
    (x : A) (hx : q • x = 0) (hdiv : ∀ c : ℕ, c • x = 0 → q ∣ c) (y : B) (hy : q • y = 0)
    (c c' : ℕ) (h : c • x = c' • x) : c • y = c' • y := by
  have hm : ∀ z : A, q • z = 0 → ∀ n : ℕ, n • z = (n % q) • z := by
    intro z hz n
    conv_lhs => rw [← Nat.mod_add_div n q]
    rw [add_nsmul, mul_comm q, mul_nsmul', hz, nsmul_zero, add_zero]
  have hm' : ∀ z : B, q • z = 0 → ∀ n : ℕ, n • z = (n % q) • z := by
    intro z hz n
    conv_lhs => rw [← Nat.mod_add_div n q]
    rw [add_nsmul, mul_comm q, mul_nsmul', hz, nsmul_zero, add_zero]
  have e : (c % q) • x = (c' % q) • x := by rw [← hm x hx, ← hm x hx, h]
  have key : c % q = c' % q := by
    rcases le_total (c' % q) (c % q) with hle | hle
    · have h0 : (c % q - c' % q) • x = 0 := by
        rw [← Nat.sub_add_cancel hle, add_nsmul] at e
        simpa using e
      have := Nat.eq_zero_of_dvd_of_lt (hdiv _ h0)
        (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hq))
      omega
    · have h0 : (c' % q - c % q) • x = 0 := by
        rw [← Nat.sub_add_cancel hle, add_nsmul] at e
        simpa using e.symm
      have := Nat.eq_zero_of_dvd_of_lt (hdiv _ h0)
        (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hq))
      omega
  rw [hm' y hy c, hm' y hy c', key]

private theorem sec_eq_of_isSheaf_of_not_nonempty {R : Type} [CommRing R] (N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) {W : Scheme} (hW : ¬ Nonempty ↥W)
    (a b : UpperTheory.Et.sec N W) : a = b := by
  have h0 : a - b = 0 := by
    refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.2.2.2.2.1 R N hN W (a - b) ?_
    refine (UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local W _ ?_).1 ?_
    · intro V V' g k hg
      rw [UpperTheory.Cb.SecLc.rs_comp, hg, pmod_rs_zero]
    · intro x
      exact (hW ⟨x⟩).elim
  exact sub_eq_zero.mp h0

private theorem nsmul_rs_eq_nsmul_rs_of_gen_of_nsmul_eq_zero {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) (q : ℕ) (hq : 0 < q) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g)
    (hh : q • h = 0) {W : Scheme} (k : W ⟶ U) (c c' : ℕ)
    (e : c • UpperTheory.Et.rs M k g = c' • UpperTheory.Et.rs M k g) :
    c • UpperTheory.Et.rs N k h = c' • UpperTheory.Et.rs N k h := by
  by_cases hW : Nonempty ↥W
  · refine nsmul_eq_nsmul_of_nsmul_eq_nsmul_of_exact_order q hq (UpperTheory.Et.rs M k g) ?_ ?_ (UpperTheory.Et.rs N k h) ?_ c c' e
    · rw [← UpperTheory.Cb.SecLc.rs_nsmul, hg.1, pmod_rs_zero]
    · intro c hc
      exact hg.2.1 W k c hW hc
    · rw [← UpperTheory.Cb.SecLc.rs_nsmul, hh, pmod_rs_zero]
  · exact sec_eq_of_isSheaf_of_not_nonempty N hN hW _ _

private theorem pmod_rs_sub {R : Type} [CommRing R] (M : UpperTheory.Et.PMod R) {V U : Scheme}
    (k : V ⟶ U) (a b : UpperTheory.Et.sec M U) :
    UpperTheory.Et.rs M k (a - b) = UpperTheory.Et.rs M k a - UpperTheory.Et.rs M k b :=
  map_sub _ _ _

private theorem pmod_rs_add {R : Type} [CommRing R] (M : UpperTheory.Et.PMod R) {V U : Scheme}
    (k : V ⟶ U) (a b : UpperTheory.Et.sec M U) :
    UpperTheory.Et.rs M k (a + b) = UpperTheory.Et.rs M k a + UpperTheory.Et.rs M k b :=
  map_add _ _ _

private theorem exists_secLc_rel_of_gen_of_nsmul_eq_zero {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) (q : ℕ) (hq : 0 < q) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g)
    (hh : q • h = 0) (y : UpperTheory.Et.sec M U) : ∃ z, UpperTheory.Cb.SecLc.Rel M N g h y z := by
  have hy := hg.2.2 U (𝟙 U) y
  simp only [Category.comp_id] at hy
  obtain ⟨z, hz⟩ := exists_sec_locT_rs_eq_of_compatible N hN
    (fun V k => ∃ c : ℕ, UpperTheory.Et.rs M k y = c • UpperTheory.Et.rs M k g) hy
    (fun V k hk => hk.choose • UpperTheory.Et.rs N k h) (by
      intro V1 V2 W k1 k2 f1 f2 h1 h2 hc
      rw [UpperTheory.Cb.SecLc.rs_nsmul, UpperTheory.Cb.SecLc.rs_nsmul, ← UpperTheory.Cb.SecLc.rs_comp,
        ← UpperTheory.Cb.SecLc.rs_comp, hc]
      apply nsmul_rs_eq_nsmul_rs_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh
      have e1 := congrArg (UpperTheory.Et.rs M f1) h1.choose_spec
      have e2 := congrArg (UpperTheory.Et.rs M f2) h2.choose_spec
      rw [← UpperTheory.Cb.SecLc.rs_comp, UpperTheory.Cb.SecLc.rs_nsmul, ← UpperTheory.Cb.SecLc.rs_comp] at e1 e2
      rw [hc] at e1
      exact e1.symm.trans e2)
  refine ⟨z, (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _ hz ?_⟩
  rintro V k ⟨hk, e⟩
  exact ⟨hk.choose, hk.choose_spec, e⟩

private theorem secLc_rel_right_unique_of_gen_of_nsmul_eq_zero {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hN : Presheaf.IsSheaf Scheme.etaleTopology N) (q : ℕ) (hq : 0 < q) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g)
    (hh : q • h = 0) {y : UpperTheory.Et.sec M U} {z z' : UpperTheory.Et.sec N U}
    (h1 : UpperTheory.Cb.SecLc.Rel M N g h y z) (h2 : UpperTheory.Cb.SecLc.Rel M N g h y z') : z = z' := by
  have h12 := (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.1 U _ _ h1 h2
  have h0 : z - z' = 0 := by
    refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.2.2.2.2.1 R N hN U (z - z') ?_
    refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _ h12 ?_
    rintro V k ⟨⟨c, ey, ez⟩, ⟨c', ey', ez'⟩⟩
    rw [pmod_rs_sub, ez, ez', nsmul_rs_eq_nsmul_rs_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh k c c' (ey.symm.trans ey'),
      sub_self]
  exact sub_eq_zero.mp h0

private theorem secLc_rel_add {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) {y y' : UpperTheory.Et.sec M U} {z z' : UpperTheory.Et.sec N U}
    (h1 : UpperTheory.Cb.SecLc.Rel M N g h y z) (h2 : UpperTheory.Cb.SecLc.Rel M N g h y' z') :
    UpperTheory.Cb.SecLc.Rel M N g h (y + y') (z + z') := by
  refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _
    ((UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.1 U _ _ h1 h2) ?_
  rintro V k ⟨⟨c, ey, ez⟩, ⟨c', ey', ez'⟩⟩
  exact ⟨c + c', by rw [pmod_rs_add, ey, ey', add_nsmul], by rw [pmod_rs_add, ez, ez', add_nsmul]⟩

private theorem secLc_rel_rs {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) {y : UpperTheory.Et.sec M U} {z : UpperTheory.Et.sec N U}
    (hr : UpperTheory.Cb.SecLc.Rel M N g h y z) {W : Scheme} (k : W ⟶ U) :
    UpperTheory.Cb.SecLc.Rel M N (UpperTheory.Et.rs M k g) (UpperTheory.Et.rs N k h) (UpperTheory.Et.rs M k y)
      (UpperTheory.Et.rs N k z) := by
  refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 W _ _
    ((UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.2.2.1 U W k _ hr) ?_
  rintro V k' ⟨c, ey, ez⟩
  exact ⟨c, by rw [← UpperTheory.Cb.SecLc.rs_comp, ← UpperTheory.Cb.SecLc.rs_comp, ey],
    by rw [← UpperTheory.Cb.SecLc.rs_comp, ← UpperTheory.Cb.SecLc.rs_comp, ez]⟩

private theorem secLc_rel_symm {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R) {U : Scheme}
    (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U) {y : UpperTheory.Et.sec M U} {z : UpperTheory.Et.sec N U}
    (hr : UpperTheory.Cb.SecLc.Rel M N g h y z) : UpperTheory.Cb.SecLc.Rel N M h g z y := by
  refine (UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology).2.1 U _ _ hr ?_
  rintro V k ⟨c, ey, ez⟩
  exact ⟨c, ez, ey⟩

private theorem exists_sec_addEquiv_secLc_rel_of_gen {R : Type} [CommRing R] (M N : UpperTheory.Et.PMod R)
    (hM : Presheaf.IsSheaf Scheme.etaleTopology M) (hN : Presheaf.IsSheaf Scheme.etaleTopology N)
    (q : ℕ) (hq : 0 < q) {U : Scheme} (g : UpperTheory.Et.sec M U) (h : UpperTheory.Et.sec N U)
    (hg : UpperTheory.Et.Gen Scheme.etaleTopology q M g) (hh : UpperTheory.Et.Gen Scheme.etaleTopology q N h) :
    ∃ φ : UpperTheory.Et.sec M U ≃+ UpperTheory.Et.sec N U, ∀ y, UpperTheory.Cb.SecLc.Rel M N g h y (φ y) := by
  choose f hf using exists_secLc_rel_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh.1
  have fadd : ∀ a b, f (a + b) = f a + f b := fun a b =>
    secLc_rel_right_unique_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh.1 (hf (a + b)) (secLc_rel_add M N g h (hf a) (hf b))
  have finj : Function.Injective f := by
    intro a b e
    have ha := secLc_rel_symm M N g h (hf a)
    have hb := secLc_rel_symm M N g h (hf b)
    rw [e] at ha
    exact secLc_rel_right_unique_of_gen_of_nsmul_eq_zero N M hM q hq h g hh hg.1 ha hb
  have fsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, hy⟩ := exists_secLc_rel_of_gen_of_nsmul_eq_zero N M hM q hq h g hh hg.1 z
    exact ⟨y, secLc_rel_right_unique_of_gen_of_nsmul_eq_zero M N hN q hq g h hg hh.1 (hf y) (secLc_rel_symm N M h g hy)⟩
  exact ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) ⟨finj, fsurj⟩, hf⟩

private theorem sec_res_twGen (q : ℕ) (i : ℤ) (V' V : Scheme) (g : V' ⟶ V)
    (ζ : Prim q Γ(V, ⊤)) : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold twGen Sec.res ofRings.sec
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op
  have h2 := congrArg (fun f => ModuleCat.Hom.hom f
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q i).obj (op V))) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  erw [← h2]
  refine congrArg (ModuleCat.Hom.hom
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V'))) ?_
  simp only [Functor.comp_map, twF, ModuleCat.hom_ofHom]
  erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

open UpperTheory.Cb.SecLc in
theorem UpperTheory.exists_tateTwist_sections_equiv_locallyConstant :
    ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ E : ∀ (V : Scheme.{0}), Prim q Γ(V, ⊤) → (Sec (tw q i) V ≃+ LocallyConstant V (ZMod q)), ∀ (V' V : Scheme.{0}) (g : V' ⟶ V) (ζ : Prim q Γ(V, ⊤)) (s : Sec (tw q i) V), E V' (ζ.map g.appTop.hom) (Sec.res g s) = (E V ζ s).comap ⟨g, g.continuous⟩ := by
  intro q _ i
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hM : Presheaf.IsSheaf Scheme.etaleTopology (tw q i).obj := (tw q i).property
  have hN : Presheaf.IsSheaf Scheme.etaleTopology (UpperTheory.Et.cSh (ZMod q) (ZMod q)).obj :=
    Presheaf.IsSheaf.of_le Scheme.etaleTopology_le_proetaleTopology
      (UpperTheory.Et.cSh (ZMod q) (ZMod q)).property
  have hone : ∀ V : Scheme, UpperTheory.Et.Gen Scheme.etaleTopology q (UpperTheory.Et.cSh (ZMod q) (ZMod q)).obj
      (UpperTheory.Et.cSec (ZMod q) (ZMod q) (ContinuousMap.const V (1 : ZMod q))) := by
    intro V
    refine UpperTheory.constantSheaf_cyclic_generator_of_order (ZMod q) (ZMod q) q 1 (by simp) ?_ ?_ V
    · intro c hc
      rw [nsmul_eq_mul, mul_one] at hc
      exact (ZMod.natCast_eq_zero_iff c q).mp hc
    · intro x
      exact ⟨x.val, by simp⟩
  have hgen : ∀ (V : Scheme) (ζ : Prim q Γ(V, ⊤)),
      UpperTheory.Et.Gen Scheme.etaleTopology q (tw q i).obj (twGen i ζ) :=
    fun V ζ => (UpperTheory.tateTwist_generator_of_primitiveRoot_and_roots_etaleLocal q i V).1 ζ
  choose φ hφ using fun (V : Scheme) (ζ : Prim q Γ(V, ⊤)) =>
    exists_sec_addEquiv_secLc_rel_of_gen (tw q i).obj _ hM hN q hq _ _ (hgen V ζ) (hone V)
  let B : ∀ V : Scheme, C(V, ZMod q) ≃+ UpperTheory.Et.sec (UpperTheory.Et.cSh (ZMod q) (ZMod q)).obj V :=
    fun V => AddEquiv.ofBijective
      (AddMonoidHom.mk' (UpperTheory.Et.cSec (ZMod q) (ZMod q)) (UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).2.1)
      (UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).1
  let C : ∀ V : Scheme, LocallyConstant V (ZMod q) ≃+ C(V, ZMod q) :=
    fun V => AddEquiv.ofBijective LocallyConstant.toContinuousMapAddMonoidHom
      ⟨LocallyConstant.toContinuousMap_injective,
        fun f => ⟨⟨f, (IsLocallyConstant.iff_continuous f).mpr f.continuous⟩, rfl⟩⟩
  refine ⟨fun V ζ => (φ V ζ).trans ((B V).symm.trans (C V).symm), ?_⟩
  intro V' V g ζ s
  have hB : ∀ f : C(V, ZMod q), B V' (C V' (((C V).symm f).comap ⟨g, g.continuous⟩)) =
      UpperTheory.Et.rs _ g (B V f) := by
    intro f
    show UpperTheory.Et.cSec (ZMod q) (ZMod q) _ = UpperTheory.Et.rs _ g (UpperTheory.Et.cSec (ZMod q) (ZMod q) f)
    rw [(UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).2.2.1]
    congr 1
    ext x
    exact congrArg (fun u : C(V, ZMod q) => u (g.base x)) ((C V).apply_symm_apply f)
  have e1 : UpperTheory.Et.rs (tw q i).obj g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) :=
    sec_res_twGen q i V' V g ζ
  have e2 : UpperTheory.Et.rs _ g (UpperTheory.Et.cSec (ZMod q) (ZMod q) (ContinuousMap.const V (1 : ZMod q))) =
      UpperTheory.Et.cSec (ZMod q) (ZMod q) (ContinuousMap.const V' (1 : ZMod q)) := by
    rw [(UpperTheory.continuousSections_bijective_additive_natural (ZMod q) (ZMod q) V).2.2.1]
    rfl
  have hr := secLc_rel_rs _ _ _ _ (hφ V ζ s) g
  rw [e1, e2] at hr
  have key := secLc_rel_right_unique_of_gen_of_nsmul_eq_zero _ _ hN q hq _ _ (hgen V' _) (hone V').1 (hφ V' _ (Sec.res g s)) hr
  apply (C V').injective
  apply (B V').injective
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hB, AddEquiv.apply_symm_apply]
  exact key
