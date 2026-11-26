module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPicPatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasis
open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (s : Γ(X, W)) :
    (f.app W').hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (Y.presheaf.map ((Opens.map f.base).map (homOfLE h)).op).hom ((f.app W).hom s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem compat_res {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b) :
    (i'.appLE (p ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_left).hom
        ((X'.presheaf.map ((Opens.map p.base).map (homOfLE h)).op).hom a) =
      (p'.appLE (i ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_right).hom
        ((Z.presheaf.map ((Opens.map i.base).map (homOfLE h)).op).hom b) := by
  have hV : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W) :=
    fun x hx => ⟨h hx.1, h hx.2⟩
  have := congrArg (Z'.presheaf.map (homOfLE hV).op).hom hab
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at this ⊢
  exact this

theorem unique_of_basis {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens) (hbasis : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W)
    (hB : ∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b)
    (s s' : Γ(X, W)) (hs : (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (hs' : (p.app W).hom s' = a ∧ (i.app W).hom s' = b) : s = s' := by
  have hcover : W ≤ ⨆ j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W}, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  refine X.sheaf.eq_of_locally_eq' (fun j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W} => j.1) W
    (fun j => homOfLE j.2.2) hcover s s' fun j => ?_
  have hc := compat_res p i i' p' j.2.2 a b hab
  refine (hB j.1 j.2.1 _ _ hc).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact (app_res p j.2.2 s).trans (congrArg _ hs.1)
  · exact (app_res i j.2.2 s).trans (congrArg _ hs.2)
  · exact (app_res p j.2.2 s').trans (congrArg _ hs'.1)
  · exact (app_res i j.2.2 s').trans (congrArg _ hs'.2)

theorem glues_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) →
    (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  intro X X' Z Z' p i i' p' B hbasis hB W a b hab
  let I := {W' : X.Opens // W' ∈ B ∧ W' ≤ W}
  have hcover : W ≤ ⨆ j : I, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  choose t ht using fun j : I => (hB j.1 j.2.1 _ _ (compat_res p i i' p' j.2.2 a b hab)).exists
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j : I => j.1) t := by
    intro j k
    have hjk : j.1 ⊓ k.1 ≤ W := inf_le_left.trans j.2.2
    refine unique_of_basis p i i' p' B hbasis hB (j.1 ⊓ k.1) _ _ (compat_res p i i' p' hjk a b hab) _ _
      ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · refine (app_res p inf_le_left (t j)).trans ?_
      rw [(ht j).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_left (t j)).trans ?_
      rw [(ht j).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res p inf_le_right (t k)).trans ?_
      rw [(ht k).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_right (t k)).trans ?_
      rw [(ht k).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun j : I => j.1) W (fun j => homOfLE j.2.2)
    hcover t hcompat
  have key : (p.app W).hom s = a ∧ (i.app W).hom s = b := by
    constructor
    · have hcov' : p ⁻¹ᵁ W ≤ ⨆ j : I, p ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (p.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine X'.sheaf.eq_of_locally_eq' (fun j : I => p ⁻¹ᵁ j.1) (p ⁻¹ᵁ W)
        (fun j => (Opens.map p.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res p j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).1
    · have hcov' : i ⁻¹ᵁ W ≤ ⨆ j : I, i ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (i.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine Z.sheaf.eq_of_locally_eq' (fun j : I => i ⁻¹ᵁ j.1) (i ⁻¹ᵁ W)
        (fun j => (Opens.map i.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res i j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).2
  exact ⟨s, key, fun s' hs' => unique_of_basis p i i' p' B hbasis hB W a b hab s' s hs' key⟩

end GlobalTheory.PinchLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasisStatement
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_sections_glue_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) → (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)), (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a = (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  first | exact @GlobalTheory.PinchLift.glues_of_basis | exact GlobalTheory.PinchLift.glues_of_basis | (intros; apply GlobalTheory.PinchLift.glues_of_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsPullbackAffineClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfFlatOfIsPushout
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfFlatOfIsPushout
open CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.FlatFibreProduct

open TensorProduct

theorem injective_exact_of_isBaseChange {R R' M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [Module.Flat R R']
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module R M₁] [Module R M₂] [Module R M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R N₁] [Module R N₂] [Module R N₃]
    [Module R' N₁] [Module R' N₂] [Module R' N₃]
    [IsScalarTower R R' N₁] [IsScalarTower R R' N₂] [IsScalarTower R R' N₃]
    {ι₁ : M₁ →ₗ[R] N₁} {ι₂ : M₂ →ₗ[R] N₂} {ι₃ : M₃ →ₗ[R] N₃}
    (h₁ : IsBaseChange R' ι₁) (h₂ : IsBaseChange R' ι₂) (h₃ : IsBaseChange R' ι₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R'] N₂) (g' : N₂ →ₗ[R'] N₃)
    (hf : ∀ m, f' (ι₁ m) = ι₂ (f m)) (hg : ∀ m, g' (ι₂ m) = ι₃ (g m))
    (hinj : Function.Injective f) (hex : Function.Exact f g) :
    Function.Injective f' ∧ Function.Exact f' g' := by
  have k₁ : ∀ x, h₂.equiv (f.lTensor R' x) = f' (h₁.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hf]
    | add x y hx hy => simp_all
  have k₂ : ∀ x, h₃.equiv (g.lTensor R' x) = g' (h₂.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hg]
    | add x y hx hy => simp_all
  have inj := Module.Flat.lTensor_preserves_injective_linearMap (M := R') f hinj
  have ex := Module.Flat.lTensor_exact R' hex
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · apply h₁.equiv.symm.injective
    apply inj
    apply h₂.equiv.injective
    rw [k₁, k₁]
    simpa using hab
  · obtain ⟨x, rfl⟩ := h₂.equiv.surjective y
    rw [← k₂, LinearEquiv.map_eq_zero_iff, ex x]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨h₁.equiv z, (k₁ z).symm⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := h₁.equiv.surjective z
      refine ⟨w, h₂.equiv.injective ?_⟩
      rw [k₁, hz]

theorem exists_unique_of_flat_of_isPushout : ∀ {A B C D A' B' C' D' : CommRingCat.{0}} (fB : A ⟶ B) (fC : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D) (e : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C') (eD : D ⟶ D') (aB : A' ⟶ B') (aC : A' ⟶ C') (u' : B' ⟶ D') (v' : C' ⟶ D'), e.hom.Flat → IsPushout e fB aB eB → IsPushout e fC aC eC → IsPushout e (fB ≫ u) (aB ≫ u') eD → eB ≫ u' = u ≫ eD → eC ≫ v' = v ≫ eD → aB ≫ u' = aC ≫ v' → fB ≫ u = fC ≫ v → (∀ (b : B) (c : C), u.hom b = v.hom c → ∃! a : A, fB.hom a = b ∧ fC.hom a = c) → ∀ (b' : B') (c' : C'), u'.hom b' = v'.hom c' → ∃! a' : A', aB.hom a' = b' ∧ aC.hom a' = c' := by
  intro A B C D A' B' C' D' fB fC u v e eB eC eD aB aC u' v' hfl hB hC hD h1 h2 h3 h4 hfib
  letI : Algebra A A' := e.hom.toAlgebra
  letI : Algebra A B := fB.hom.toAlgebra
  letI : Algebra A C := fC.hom.toAlgebra
  letI : Algebra A D := (fB ≫ u).hom.toAlgebra
  letI : Algebra A' B' := aB.hom.toAlgebra
  letI : Algebra A' C' := aC.hom.toAlgebra
  letI : Algebra A' D' := (aB ≫ u').hom.toAlgebra
  letI : Algebra B B' := eB.hom.toAlgebra
  letI : Algebra C C' := eC.hom.toAlgebra
  letI : Algebra D D' := eD.hom.toAlgebra
  letI : Algebra A B' := (e ≫ aB).hom.toAlgebra
  letI : Algebra A C' := (e ≫ aC).hom.toAlgebra
  letI : Algebra A D' := (e ≫ aB ≫ u').hom.toAlgebra
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' D' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hB.w)
  haveI : IsScalarTower A C C' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hC.w)
  haveI : IsScalarTower A D D' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hD.w)
  haveI : Module.Flat A A' := hfl
  have PB : Algebra.IsPushout A A' B B' := CommRingCat.isPushout_iff_isPushout.mp hB
  have PC : Algebra.IsPushout A A' C C' := CommRingCat.isPushout_iff_isPushout.mp hC
  have PD : Algebra.IsPushout A A' D D' := CommRingCat.isPushout_iff_isPushout.mp hD
  have hb₁ : IsBaseChange A' (Algebra.linearMap A A') := IsBaseChange.linearMap A A'
  have hb₂ := IsBaseChange.prodMap _ _ PB.out PC.out
  have hb₃ := PD.out
  let uL : B →ₗ[A] D :=
    { toFun := u.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u.hom (fB.hom a * b) = (fB ≫ u).hom a * u.hom b
        rw [map_mul]; rfl }
  let vL : C →ₗ[A] D :=
    { toFun := v.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v.hom (fC.hom a * c) = (fB ≫ u).hom a * v.hom c
        rw [map_mul, h4]; rfl }
  let u'L : B' →ₗ[A'] D' :=
    { toFun := u'.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u'.hom (aB.hom a * b) = (aB ≫ u').hom a * u'.hom b
        rw [map_mul]; rfl }
  let v'L : C' →ₗ[A'] D' :=
    { toFun := v'.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v'.hom (aC.hom a * c) = (aB ≫ u').hom a * v'.hom c
        rw [map_mul, h3]; rfl }
  let f : A →ₗ[A] B × C := (Algebra.linearMap A B).prod (Algebra.linearMap A C)
  let g : B × C →ₗ[A] D := uL.coprod (-vL)
  let f' : A' →ₗ[A'] B' × C' := (Algebra.linearMap A' B').prod (Algebra.linearMap A' C')
  let g' : B' × C' →ₗ[A'] D' := u'L.coprod (-v'L)
  have hf : ∀ m, f' (Algebra.linearMap A A' m) =
      ((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) (f m) := by
    intro m
    refine Prod.ext ?_ ?_
    · exact congrArg (fun φ => φ.hom m) hB.w
    · exact congrArg (fun φ => φ.hom m) hC.w
  have hg : ∀ m, g' (((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) m) =
      (IsScalarTower.toAlgHom A D D').toLinearMap (g m) := by
    rintro ⟨b, c⟩
    change u'.hom (eB.hom b) + -v'.hom (eC.hom c) = eD.hom (u.hom b + -v.hom c)
    have e₁ : u'.hom (eB.hom b) = eD.hom (u.hom b) := congrArg (fun φ => φ.hom b) h1
    have e₂ : v'.hom (eC.hom c) = eD.hom (v.hom c) := congrArg (fun φ => φ.hom c) h2
    rw [map_add (f := _), map_neg, e₁, e₂]
  have hinj : Function.Injective f := by
    intro a₁ a₂ h
    have hb : fB.hom a₁ = fB.hom a₂ := congrArg Prod.fst h
    have hc : fC.hom a₁ = fC.hom a₂ := congrArg Prod.snd h
    obtain ⟨a, -, ha⟩ := hfib (fB.hom a₁) (fC.hom a₁)
      (by simpa using congrArg (fun φ => φ.hom a₁) h4)
    exact (ha a₁ ⟨rfl, rfl⟩).trans (ha a₂ ⟨hb.symm, hc.symm⟩).symm
  have hex : Function.Exact f g := by
    rintro ⟨b, c⟩
    change u.hom b + -v.hom c = 0 ↔ _
    rw [← sub_eq_add_neg, sub_eq_zero]
    constructor
    · intro h
      obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := hfib b c h
      exact ⟨a, Prod.ext ha₁ ha₂⟩
    · rintro ⟨a, ha⟩
      have hb : fB.hom a = b := congrArg Prod.fst ha
      have hc : fC.hom a = c := congrArg Prod.snd ha
      subst hb hc
      simpa using congrArg (fun φ => φ.hom a) h4
  obtain ⟨inj', ex'⟩ := injective_exact_of_isBaseChange hb₁ hb₂ hb₃ f g f' g' hf hg hinj hex
  intro b' c' h
  have h0 : g' (b', c') = 0 := by
    change u'.hom b' + -v'.hom c' = 0
    rw [h, add_neg_cancel]
  obtain ⟨a', ha'⟩ := (ex' (b', c')).1 h0
  refine ⟨a', ⟨congrArg Prod.fst ha', congrArg Prod.snd ha'⟩, fun y hy => inj' ?_⟩
  rw [ha']
  exact Prod.ext hy.1 hy.2

end GlobalTheory.FlatFibreProduct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfFlatOfIsPushoutStatement
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_preimage_pair_of_pushout_of_compat : ∀ {A B C D A' B' C' D' : CommRingCat.{0}} (fB : A ⟶ B) (fC : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D) (e : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C') (eD : D ⟶ D') (aB : A' ⟶ B') (aC : A' ⟶ C') (u' : B' ⟶ D') (v' : C' ⟶ D'), e.hom.Flat → IsPushout e fB aB eB → IsPushout e fC aC eC → IsPushout e (fB ≫ u) (aB ≫ u') eD → eB ≫ u' = u ≫ eD → eC ≫ v' = v ≫ eD → aB ≫ u' = aC ≫ v' → fB ≫ u = fC ≫ v → (∀ (b : B) (c : C), u.hom b = v.hom c → ∃! a : A, fB.hom a = b ∧ fC.hom a = c) → ∀ (b' : B') (c' : C'), u'.hom b' = v'.hom c' → ∃! a' : A', aB.hom a' = b' ∧ aC.hom a' = c' := by
  first | exact @GlobalTheory.FlatFibreProduct.exists_unique_of_flat_of_isPushout | exact GlobalTheory.FlatFibreProduct.exists_unique_of_flat_of_isPushout | (intros; apply GlobalTheory.FlatFibreProduct.exists_unique_of_flat_of_isPushout <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift.FlatBC

theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S}
    {iY : Y ⟶ T} (H : IsPullback g iY iX f) {US : S.Opens} {UT : T.Opens} {UX : X.Opens} {UY : Y.Opens}
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US) (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (h₁ : UY ≤ g ⁻¹ᵁ UX) (h₂ : UY ≤ iY ⁻¹ᵁ UT) :
    IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) (g.appLE UX UY h₁) (iY.appLE UT UY h₂) :=
  (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX)

theorem appLE_congr_of_eq {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) (U : B.Opens) (V : A.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

end GlobalTheory.PinchLift.FlatBC

namespace GlobalTheory.PinchLift.FlatBC

theorem glues_affine_of_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hglue V W hV hW hWV a b hab
  have hcl : i'.left ≫ p.left = p'.left ≫ i.left := by
    rw [← Over.comp_left, ← Over.comp_left, hc]
  have hcE : (E ◁ i').left ≫ (E ◁ p).left = (E ◁ p').left ≫ (E ◁ i).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hc]
  have nat : ∀ {Y Y' : Over S} (j : Y' ⟶ Y),
      (E ◁ j).left ≫ (snd E Y).left = (snd E Y').left ≫ j.left := by
    intro Y Y' j
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  haveI : IsAffineHom i.left := inferInstance
  haveI : IsClosedImmersion i'.left := MorphismProperty.of_isPullback hpb.flip ‹_›
  haveI : IsAffineHom p'.left := MorphismProperty.of_isPullback hpb ‹_›
  haveI : Flat (snd E X).left := by
    change Flat (pullback.snd E.hom X.hom); infer_instance
  have eV : p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcl]
  have eW : (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) = (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcE]
  have hDV : i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = (i'.left ≫ p.left) ⁻¹ᵁ V := by
    rw [eV, inf_idem]; rfl
  have hDW : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W := by
    rw [eW, inf_idem]; rfl
  have hDVa : IsAffineOpen (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDV]; exact hV.preimage _
  have H1 := isPullback_whiskerLeft_snd_left E p
  have H2 := isPullback_whiskerLeft_snd_left E i
  have H3 : IsPullback ((E ◁ i').left ≫ (E ◁ p).left) (snd E Z').left (snd E X).left
      (i'.left ≫ p.left) := by
    have := isPullback_whiskerLeft_snd_left E (i' ≫ p)
    rwa [MonoidalCategory.whiskerLeft_comp, Over.comp_left, Over.comp_left] at this
  have hU1 : (E ◁ p).left ⁻¹ᵁ W = (E ◁ p).left ⁻¹ᵁ W ⊓ (snd E X').left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat p, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have hU2 : (E ◁ i).left ⁻¹ᵁ W = (E ◁ i).left ⁻¹ᵁ W ⊓ (snd E Z).left ⁻¹ᵁ (i.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat i, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have nat3 : ((E ◁ i').left ≫ (E ◁ p).left) ≫ (snd E X).left =
      (snd E Z').left ≫ (i'.left ≫ p.left) := by
    rw [Category.assoc, nat p, ← Category.assoc, nat i', Category.assoc]
  have hU3 : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W ⊓
        (snd E Z').left ⁻¹ᵁ (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDW, hDV]
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage (snd E Z').left (i'.left ≫ p.left) V, ← nat3,
      Scheme.Hom.comp_preimage _ (snd E X).left V]
    exact Scheme.Hom.preimage_mono _ hWV
  have P1 := isPushout_appLE_of_isPullback H1 hV (hV.preimage p.left) hW le_rfl hWV hU1 le_rfl
    (hU1.le.trans inf_le_right)
  have P2 := isPushout_appLE_of_isPullback H2 hV (hV.preimage i.left) hW le_rfl hWV hU2 le_rfl
    (hU2.le.trans inf_le_right)
  have P3 := isPushout_appLE_of_isPullback H3 hV hDVa hW hDV.le hWV hU3 (hU3.le.trans inf_le_left)
    (hU3.le.trans inf_le_right)
  have key := GlobalTheory.T.existsUnique_preimage_pair_of_pushout_of_compat (p.left.appLE V (p.left ⁻¹ᵁ V) le_rfl) (i.left.appLE V (i.left ⁻¹ᵁ V) le_rfl)
    (i'.left.appLE (p.left ⁻¹ᵁ V) _ inf_le_left) (p'.left.appLE (i.left ⁻¹ᵁ V) _ inf_le_right)
    ((snd E X).left.appLE V W hWV)
    ((snd E X').left.appLE (p.left ⁻¹ᵁ V) ((E ◁ p).left ⁻¹ᵁ W) (hU1.le.trans inf_le_right))
    ((snd E Z).left.appLE (i.left ⁻¹ᵁ V) ((E ◁ i).left ⁻¹ᵁ W) (hU2.le.trans inf_le_right))
    ((snd E Z').left.appLE _ _ (hU3.le.trans inf_le_right))
    ((E ◁ p).left.appLE W _ le_rfl) ((E ◁ i).left.appLE W _ le_rfl)
    ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) _ inf_le_left)
    ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) _ inf_le_right)
    ((snd E X).left.flat_appLE hV hW hWV) P1 P2
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]; exact P3)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat i') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat p') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcE _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcl _ _ _ _)
    (fun b c h => by
      have := hglue V b c h
      rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE] at this) a b hab
  rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]

end GlobalTheory.PinchLift.FlatBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  first | exact @GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | exact GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | (intros; apply GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem whiskerLeft_isPullback_affine_closed (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X)
    (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (hc : i' ≫ p = p' ≫ i) (hpb : IsPullback i'.left p'.left p.left i.left)
    [IsAffineHom p.left] [IsClosedImmersion i.left] :
    IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧
      IsClosedImmersion (E ◁ i).left := by
  have hP := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p
  have hI := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E i
  have hP' := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p'
  refine ⟨?_, MorphismProperty.of_isPullback hP.flip ‹_›, MorphismProperty.of_isPullback hI.flip ‹_›⟩
  have hout := hP'.flip.paste_horiz hpb
  refine IsPullback.of_right ?_ ?_ hP.flip
  · have h1 : (E ◁ i').left ≫ (snd E X').left = (snd E Z').left ≫ i'.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    have h2 : (E ◁ i).left ≫ (snd E X).left = (snd E Z).left ≫ i.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    rw [h1, h2]; exact hout
  · rw [← Over.comp_left, ← Over.comp_left, ← whiskerLeft_comp, ← whiskerLeft_comp, hc]

theorem glues_whiskerLeft : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧ IsClosedImmersion (E ◁ i).left ∧ GlobalTheory.PinchLift.Glues (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hg
  obtain ⟨h1, h2, h3⟩ := whiskerLeft_isPullback_affine_closed S E X X' Z Z' p i i' p' hc hpb
  refine ⟨h1, h2, h3, ?_⟩
  refine GlobalTheory.T.pullback_square_sections_glue_of_basis (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left
    {W | IsAffineOpen W ∧ ∃ V : X.left.Opens, IsAffineOpen V ∧ W ≤ (snd E X).left ⁻¹ᵁ V} ?_ ?_
  · intro W x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((snd E X).left x)) isOpen_univ
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ := (E ⊗ X).left.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((W ⊓ (snd E X).left ⁻¹ᵁ V : (E ⊗ X).left.Opens) : Set (E ⊗ X).left) from ⟨hx, hxV⟩)
      (W ⊓ (snd E X).left ⁻¹ᵁ V).isOpen
    exact ⟨W', ⟨hW', V, hV, fun y hy => (hle hy).2⟩, hxW', fun y hy => (hle hy).1⟩
  · rintro W ⟨hW, V, hV, hWV⟩
    exact GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange S E X X' Z Z' p i i' p' hE hc hpb hp hi hg V W hV hW hWV

end GlobalTheory.PinchLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGlueMilnorPatchingArtinLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ArtinPatch

theorem elem_of_isPullback {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) :
    (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem isPushout_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (H : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁.hom) :
    IsPushout f₁ f₂ g₁ g₂ := by
  obtain ⟨-, hex⟩ := elem_of_isPullback H
  have key : ∀ s : PushoutCocone f₁ f₂, RingHom.ker g₁.hom ≤ RingHom.ker s.inl.hom := by
    intro s r hr
    rw [RingHom.mem_ker] at hr ⊢
    obtain ⟨a, ha1, ha2⟩ := hex r 0 (by rw [hr, map_zero])
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [← ha1, e, ha2, map_zero]
  let d : ∀ s : PushoutCocone f₁ f₂, R₀ ⟶ s.pt := fun s =>
    CommRingCat.ofHom (RingHom.liftOfRightInverse g₁.hom (Function.surjInv hg₁)
      (Function.rightInverse_surjInv hg₁) ⟨s.inl.hom, key s⟩)
  have hd : ∀ (s : PushoutCocone f₁ f₂) (r : R₁), (d s).hom (g₁.hom r) = s.inl.hom r := fun s r => by
    simp only [d, CommRingCat.hom_ofHom]
    exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  refine IsPushout.of_isColimit (c := PushoutCocone.mk g₁ g₂ H.w) ?_
  refine PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_
  · intro s
    ext r
    exact hd s r
  · intro s
    ext r₂
    obtain ⟨r₁, hr₁⟩ := hg₁ (g₂.hom r₂)
    obtain ⟨a, ha1, ha2⟩ := hex r₁ r₂ hr₁
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change (d s).hom (g₂.hom r₂) = s.inr.hom r₂
    rw [← hr₁, hd, ← ha1, e, ha2]
  · intro s m h1 _
    ext y
    obtain ⟨r, rfl⟩ := hg₁ y
    have e := congrArg (fun φ => φ.hom r) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change m.hom (g₁.hom r) = (d s).hom (g₁.hom r)
    rw [hd]
    exact e

theorem spec_eq_of_artinian (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P] (x y : Spec P) :
    x = y := by
  have h : ∀ z : PrimeSpectrum P, z.asIdeal = IsLocalRing.maximalIdeal P := fun z =>
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime z.asIdeal)
  exact PrimeSpectrum.ext ((h x).trans (h y).symm)

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem glues_spec {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (H : IsPullback f₁ f₂ g₁ g₂) (hP : ∀ x y : Spec P, x = y) :
    GlobalTheory.PinchLift.Glues (Spec.map f₂) (Spec.map f₁) (Spec.map g₂) (Spec.map g₁) := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback H
  have inj : ∀ {R : CommRingCat.{0}} (u v : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso R).hom.hom u = (Scheme.ΓSpecIso R).hom.hom v → u = v := by
    intro R u v h
    simpa using congrArg (Scheme.ΓSpecIso R).inv.hom h
  have nat : ∀ {R S : CommRingCat.{0}} (f : R ⟶ S) (u : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso S).hom.hom ((Spec.map f).appTop.hom u) = f.hom ((Scheme.ΓSpecIso R).hom.hom u) := by
    intro R S f u
    exact congrArg (fun φ => φ.hom u) (Scheme.ΓSpecIso_naturality f)
  refine GlobalTheory.PinchLift.glues_of_basis _ _ _ _ {⊤} ?_ ?_
  · intro W x hx
    refine ⟨⊤, rfl, trivial, fun y _ => ?_⟩
    rw [hP y x]
    exact hx
  · rintro W rfl a b hab
    set V := Spec.map g₂ ⁻¹ᵁ Spec.map f₂ ⁻¹ᵁ (⊤ : (Spec P).Opens) ⊓
      Spec.map g₁ ⁻¹ᵁ Spec.map f₁ ⁻¹ᵁ (⊤ : (Spec P).Opens) with hVdef
    have hV : V = ⊤ := top_le_iff.1 (fun x _ => ⟨trivial, trivial⟩)
    have hiso : IsIso (homOfLE (le_top : V ≤ ⊤)) := by
      rw [show homOfLE (le_top : V ≤ ⊤) = (eqToIso hV).hom from Subsingleton.elim _ _]
      infer_instance
    set ρ := (Spec R₀).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    have hρ : ∀ u v, ρ.hom u = ρ.hom v → u = v := by
      intro u v h
      simpa using congrArg (inv ρ).hom h
    have e : (Spec.map g₂).appTop.hom a = (Spec.map g₁).appTop.hom b := by
      apply hρ
      exact hab
    have key : g₁.hom ((Scheme.ΓSpecIso R₁).hom.hom b) = g₂.hom ((Scheme.ΓSpecIso R₂).hom.hom a) := by
      rw [← nat g₁ b, ← nat g₂ a, e]
    obtain ⟨x, hx1, hx2⟩ := hex _ _ key
    refine ⟨(Scheme.ΓSpecIso P).inv.hom x, ⟨?_, ?_⟩, ?_⟩
    · apply inj
      change (Scheme.ΓSpecIso R₂).hom.hom ((Spec.map f₂).appTop.hom _) = _
      rw [nat]
      simpa using hx2
    · apply inj
      change (Scheme.ΓSpecIso R₁).hom.hom ((Spec.map f₁).appTop.hom _) = _
      rw [nat]
      simpa using hx1
    · rintro s ⟨hs2, hs1⟩
      apply inj
      simp only [Iso.inv_hom_id_apply]
      apply hinj
      · rw [← nat]
        change (Scheme.ΓSpecIso R₁).hom.hom (((Spec.map f₁).app ⊤).hom s) = _
        rw [hs1, hx1]
      · rw [← nat]
        change (Scheme.ΓSpecIso R₂).hom.hom (((Spec.map f₂).app ⊤).hom s) = _
        rw [hs2, hx2]

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem exists_lb_glue : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hg₁ hg₂ X X₁ X₂ X₀ j₁ j₂ i₁ i₂ hflat h₁ h₂ h₀ hc hc₂ L₁ L₂ hL₁ hL₂ hiso
  haveI := hloc
  haveI := hart
  obtain ⟨-, hex⟩ := elem_of_isPullback hpb
  have hf₁ : Function.Surjective f₁.hom := fun r => by
    obtain ⟨r₂, hr₂⟩ := hg₂ (g₁.hom r)
    obtain ⟨a, ha, -⟩ := hex r r₂ hr₂.symm
    exact ⟨a, ha⟩
  have hw : Spec.map g₂ ≫ Spec.map f₂ = Spec.map g₁ ≫ Spec.map f₁ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpb.w]

  let O : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let O₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let O₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let O₀ : Over (Spec P) := Over.mk (Spec.map g₁ ≫ Spec.map f₁)
  let q : O₂ ⟶ O := Over.homMk (Spec.map f₂) (Category.comp_id _)
  let r : O₁ ⟶ O := Over.homMk (Spec.map f₁) (Category.comp_id _)
  let r' : O₀ ⟶ O₂ := Over.homMk (Spec.map g₂) hw
  let q' : O₀ ⟶ O₁ := Over.homMk (Spec.map g₁) rfl
  have hcomm : r' ≫ q = q' ≫ r := by
    ext1
    simpa [q, r, q', r'] using hw
  have hsq : IsPullback r'.left q'.left q.left r.left :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_of_isPullback hpb hg₁).flip)
  haveI hcl : IsClosedImmersion r.left := IsClosedImmersion.spec_of_surjective f₁ hf₁
  have haff : IsAffineHom q.left := by
    change IsAffineHom (Spec.map f₂)
    infer_instance
  have hgl : GlobalTheory.PinchLift.Glues q.left r.left r'.left q'.left :=
    glues_spec hpb (spec_eq_of_artinian P)
  obtain ⟨hpb', haff', hcl', hgl'⟩ :=
    GlobalTheory.PinchLift.glues_whiskerLeft (Spec P) X O O₂ O₁ O₀ q r r' q' hflat hcomm hsq haff hcl hgl

  have hT : ∀ U : Over (Spec P), IsPullback (fst X U).left (snd X U).left X.hom U.hom :=
    fun U => IsPullback.of_hasPullback X.hom U.hom
  have h₀' : IsPullback (i₁ ≫ j₁) X₀.hom X.hom (Spec.map g₁ ≫ Spec.map f₁) := h₀.paste_horiz h₁
  let ψ₂ := IsPullback.isoIsPullback _ _ h₂ (hT O₂)
  let ψ₁ := IsPullback.isoIsPullback _ _ h₁ (hT O₁)
  let ψ₀ := IsPullback.isoIsPullback _ _ h₀' (hT O₀)
  have p₂f : ψ₂.hom ≫ (fst X O₂).left = j₂ := IsPullback.isoIsPullback_hom_fst _ _ h₂ (hT O₂)
  have p₂s : ψ₂.hom ≫ (snd X O₂).left = X₂.hom := IsPullback.isoIsPullback_hom_snd _ _ h₂ (hT O₂)
  have p₁f : ψ₁.hom ≫ (fst X O₁).left = j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₁ (hT O₁)
  have p₁s : ψ₁.hom ≫ (snd X O₁).left = X₁.hom := IsPullback.isoIsPullback_hom_snd _ _ h₁ (hT O₁)
  have p₀f : ψ₀.hom ≫ (fst X O₀).left = i₁ ≫ j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₀' (hT O₀)
  have p₀s : ψ₀.hom ≫ (snd X O₀).left = X₀.hom := IsPullback.isoIsPullback_hom_snd _ _ h₀' (hT O₀)
  let s : X.left ⟶ (X ⊗ O).left := (hT O).lift (𝟙 _) X.hom (by simp [O])
  have wf : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (fst X V).left = (fst X U).left := by
    intro U V k
    rw [← Over.comp_left, whiskerLeft_fst]
  have ws : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (snd X V).left = (snd X U).left ≫ k.left := by
    intro U V k
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have E₂ : j₂ ≫ s = ψ₂.hom ≫ (X ◁ q).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₂f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₂s]
      exact h₂.w
  have E₁ : j₁ ≫ s = ψ₁.hom ≫ (X ◁ r).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₁f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₁s]
      exact h₁.w
  have E₀₂ : ψ₀.hom ≫ (X ◁ r').left = i₂ ≫ ψ₂.hom := by
    apply (hT O₂).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₂f, hc]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₂s]
      exact hc₂.symm
  have E₀₁ : ψ₀.hom ≫ (X ◁ q').left = i₁ ≫ ψ₁.hom := by
    apply (hT O₁).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₁f]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₁s]
      exact h₀.w.symm

  have hab0 : GlobalTheory.CechPic.pull i₂ (GlobalTheory.CechPic.cls L₂ hL₂) = GlobalTheory.CechPic.pull i₁ (GlobalTheory.CechPic.cls L₁ hL₁) := by
    rw [← GlobalTheory.CechPic.cls_pull hL₂ i₂ (pull_isLB hL₂ i₂), ← GlobalTheory.CechPic.cls_pull hL₁ i₁ (pull_isLB hL₁ i₁)]
    exact ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hiso).symm
  have e2 : (X ◁ r').left ≫ ψ₂.inv = ψ₀.inv ≫ i₂ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e1 : (X ◁ q').left ≫ ψ₁.inv = ψ₀.inv ≫ i₁ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hab : GlobalTheory.CechPic.pull (X ◁ r').left (GlobalTheory.CechPic.pull ψ₂.inv (GlobalTheory.CechPic.cls L₂ hL₂)) =
      GlobalTheory.CechPic.pull (X ◁ q').left (GlobalTheory.CechPic.pull ψ₁.inv (GlobalTheory.CechPic.cls L₁ hL₁)) := by
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, e2, e1, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp, hab0]
  obtain ⟨e', he2, he1⟩ := GlobalTheory.PinchLift.exists_pic_patch _ _ _ _ _ _ _ _ hpb' haff' hcl' hgl' _ _ hab
  obtain ⟨L, hL, hLe⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull s e')
  refine ⟨L, hL, ?_, ?_⟩
  · have h : GlobalTheory.CechPic.cls (L.pull j₁) (pull_isLB hL j₁) = GlobalTheory.CechPic.cls L₁ hL₁ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₁, hLe, ← GlobalTheory.CechPic.pull_comp, E₁, GlobalTheory.CechPic.pull_comp, he1,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)
  · have h : GlobalTheory.CechPic.cls (L.pull j₂) (pull_isLB hL j₂) = GlobalTheory.CechPic.cls L₂ hL₂ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₂, hLe, ← GlobalTheory.CechPic.pull_comp, E₂, GlobalTheory.CechPic.pull_comp, he2,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)

end GlobalTheory.ArtinPatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGlueMilnorPatchingArtinLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_glue_milnorPatching_artinLocal : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := by
  first | exact @GlobalTheory.ArtinPatch.exists_lb_glue | exact GlobalTheory.ArtinPatch.exists_lb_glue | (intros; apply GlobalTheory.ArtinPatch.exists_lb_glue <;> assumption)
end
