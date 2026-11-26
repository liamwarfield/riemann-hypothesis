module

public import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
public import GroundTheory.ProfiniteCohomology.Shapiro

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.CupProducts.Projection
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Coind

variable (U : Subgroup G) (A B : Rep.{u} k G)

def coindTensorRightFun (f : Rep.coind U.subtype (Rep.res U.subtype A)) (b : B) :
    Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  ⟨fun x => (f.1 x ⊗ₜ[k] B.ρ x b : (A ⊗ B : Rep k G)), fun u x => by
    change f.1 (U.subtype u * x) ⊗ₜ[k] B.ρ (U.subtype u * x) b =
      A.ρ (u : G) (f.1 x) ⊗ₜ[k] B.ρ (u : G) (B.ρ x b)
    rw [f.2 u x, map_mul, Module.End.mul_apply]
    rfl⟩

def coindTensorRight :
    Rep.coind U.subtype (Rep.res U.subtype A) ⊗ B ⟶
      Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.mk₂ k (coindTensorRightFun U A B)
      (fun f f' b => Subtype.ext (funext fun x => TensorProduct.add_tmul _ _ _))
      (fun c f b => Subtype.ext (funext fun x => (TensorProduct.smul_tmul' _ _ _).symm))
      (fun f b b' => Subtype.ext (funext fun x => by
        change f.1 x ⊗ₜ[k] B.ρ x (b + b') = f.1 x ⊗ₜ[k] B.ρ x b + f.1 x ⊗ₜ[k] B.ρ x b'
        rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun c f b => Subtype.ext (funext fun x => by
        change f.1 x ⊗ₜ[k] B.ρ x (c • b) = c • (f.1 x ⊗ₜ[k] B.ρ x b)
        rw [map_smul, TensorProduct.tmul_smul]))),
    fun g => TensorProduct.ext' fun f b => Subtype.ext (funext fun x => by
      change f.1 (x * g) ⊗ₜ[k] B.ρ x (B.ρ g b) = f.1 (x * g) ⊗ₜ[k] B.ρ (x * g) b
      rw [map_mul, Module.End.mul_apply])⟩

theorem coindTensorRight_comp_coindEvalOne :
    (Rep.resFunctor U.subtype).map (coindTensorRight U A B) ≫
        coindEvalOne U (Rep.res U.subtype (A ⊗ B)) =
      resTensorHom U.subtype (coindEvalOne U (Rep.res U.subtype A)) (𝟙 _) ≫
        (resTensorIso U.subtype A B).inv := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f b =>
    change f.1 1 ⊗ₜ[k] B.ρ 1 b = f.1 1 ⊗ₜ[k] b
    rw [map_one, Module.End.one_apply]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz']

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem coindTensorRight_comp_coindTrace :
    coindTensorRight U A B ≫ coindTrace U (A ⊗ B) = coindTrace U A ▷ B := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f b =>
    change (coindTrace U (A ⊗ B)).hom ((coindTensorRight U A B).hom (f ⊗ₜ[k] b)) =
      (coindTrace U A).hom f ⊗ₜ[k] b
    rw [coindTrace_hom_apply, coindTrace_hom_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun c _ => ?_
    change (A ⊗ B).ρ c.out (f.1 c.out⁻¹ ⊗ₜ[k] B.ρ c.out⁻¹ b) = A.ρ c.out (f.1 c.out⁻¹) ⊗ₜ[k] b
    rw [GroundTheory.GroupCoh.tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz']

end Coind

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Composition

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* G)
  (hφ : Continuous φ) {p : ℕ}

theorem cohomologyMapAlong_cohomologyMap {A A' : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A]
    [IsDiscreteRep A'] [IsDiscreteRep B] (f : A ⟶ A') (g : Rep.res φ A' ⟶ B)
    (w : cohomology A p) :
    cohomologyMapAlong φ hφ g p (cohomologyMap f p w) =
      cohomologyMapAlong φ hφ ((Rep.resFunctor φ).map f ≫ g) p w := by
  induction w using cohomology_induction_on with | h w => ?_
  rw [cohomologyMap_cohomologyπ, cohomologyMapAlong_cohomologyπ, cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cyclesMap]
  rfl

theorem cohomologyMap_cohomologyMapAlong {A : Rep.{u} k G} {B B' : Rep.{u} k H} [IsDiscreteRep A]
    [IsDiscreteRep B] [IsDiscreteRep B'] (f : Rep.res φ A ⟶ B) (g : B ⟶ B')
    (w : cohomology A p) :
    cohomologyMap g p (cohomologyMapAlong φ hφ f p w) = cohomologyMapAlong φ hφ (f ≫ g) p w := by
  induction w using cohomology_induction_on with | h w => ?_
  rw [cohomologyMapAlong_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesMapAlong]
  rfl

end Composition

section Projection

variable [CompactSpace G] (U : OpenSubgroup G) {A B : Rep.{u} k G} [IsDiscreteRep A]
  [IsDiscreteRep B] {p q n : ℕ}

instance isDiscreteRep_coind_res_tensor_right :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A) ⊗ B) :=
  isDiscreteRep_tensor _ _

theorem shapiroMap_inv_apply {C : Rep.{u} k (U : Subgroup G)} [IsDiscreteRep C] (m : ℕ)
    (w : cohomology C m) : shapiroMap U C m (inv (shapiroMap U C m) w) = w :=
  ConcreteCategory.congr_hom (IsIso.inv_hom_id (shapiroMap U C m)) w

theorem inv_shapiroMap_apply {C : Rep.{u} k (U : Subgroup G)} [IsDiscreteRep C] (m : ℕ)
    (w : cohomology (Rep.coind (U : Subgroup G).subtype C) m) :
    inv (shapiroMap U C m) (shapiroMap U C m w) = w :=
  ConcreteCategory.congr_hom (IsIso.hom_inv_id (shapiroMap U C m)) w

theorem cohomologyCores_shapiroMap (A : Rep.{u} k G) [IsDiscreteRep A]
    (w : cohomology (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) p) :
    cohomologyCores U A p (shapiroMap U (Rep.res (U : Subgroup G).subtype A) p w) =
      cohomologyMap (coindTrace (U : Subgroup G) A) p w := by
  rw [cohomologyCores, ConcreteCategory.comp_apply, inv_shapiroMap_apply]

theorem cohomologyCores_cup_cohomologyRes (h : p + q = n)
    (x : cohomology (Rep.res (U : Subgroup G).subtype A) p) (y : cohomology B q) :
    cohomologyCores U (A ⊗ B) n (cohomologyMap (resTensorIso (U : Subgroup G).subtype A B).inv n
        (cup h x (cohomologyRes B U q y))) =
      cup h (cohomologyCores U A p x) y := by
  obtain ⟨z, rfl⟩ : ∃ z, shapiroMap U (Rep.res (U : Subgroup G).subtype A) p z = x :=
    ⟨_, shapiroMap_inv_apply U p x⟩
  have hkey : cohomologyMap (resTensorIso (U : Subgroup G).subtype A B).inv n
      (cup h (shapiroMap U (Rep.res (U : Subgroup G).subtype A) p z) (cohomologyRes B U q y)) =
        shapiroMap U (Rep.res (U : Subgroup G).subtype (A ⊗ B)) n
          (cohomologyMap (coindTensorRight (U : Subgroup G) A B) n (cup h z y)) := by
    rw [shapiroMap_eq, shapiroMap_eq, cohomologyRes_eq, ← cohomologyMapAlong_resTensorHom_cup,
      cohomologyMap_cohomologyMapAlong, cohomologyMapAlong_cohomologyMap,
      coindTensorRight_comp_coindEvalOne]
  rw [hkey, cohomologyCores_shapiroMap, cohomologyCores_shapiroMap, ← ConcreteCategory.comp_apply,
    ← cohomologyMap_comp, coindTensorRight_comp_coindTrace, cohomologyMap_whiskerRight_cup]

end Projection

end GroundTheory.ProfCoh
end
end

section -- merged from GroundTheory.ProfiniteCohomology.CupProducts.Pairing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section PairingHom

variable {A B C : Rep.{u} k G}

def pairingHom (β : A →ₗ[k] B →ₗ[k] C)
    (hβ : ∀ (g : G) (a : A) (b : B), β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b)) : A ⊗ B ⟶ C :=
  Rep.ofHom ⟨TensorProduct.lift β, fun g => TensorProduct.ext' fun a b => by
    simpa using hβ g a b⟩

@[simp]
theorem pairingHom_tmul (β : A →ₗ[k] B →ₗ[k] C)
    (hβ : ∀ (g : G) (a : A) (b : B), β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b)) (a : A) (b : B) :
    (pairingHom β hβ).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = β a b :=
  TensorProduct.lift.tmul a b

end PairingHom

variable [TopologicalSpace G] [IsTopologicalGroup G]

section CupPairing

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C] {p q n : ℕ}

def cupPairing (μ : A ⊗ B ⟶ C) (h : p + q = n) :
    cohomology A p →ₗ[k] cohomology B q →ₗ[k] cohomology C n :=
  (cup h).compr₂ (cohomologyMap μ n).hom

theorem cupPairing_apply (μ : A ⊗ B ⟶ C) (h : p + q = n) (x : cohomology A p)
    (y : cohomology B q) : cupPairing μ h x y = cohomologyMap μ n (cup h x y) :=
  rfl

theorem cupPairing_cohomologyπ (μ : A ⊗ B ⟶ C) (h : p + q = n) (x : cocycles A p)
    (y : cocycles B q) :
    cupPairing μ h (cohomologyπ A p x) (cohomologyπ B q y) =
      cohomologyπ C n (HomologicalComplex.cyclesMap (cochainsMap μ) n (cupCocycles h x y)) := by
  rw [cupPairing_apply, cup_cohomologyπ, cohomologyMap_cohomologyπ]

theorem cochainOf_cocycleι_cyclesMap_cupCocycles (μ : A ⊗ B ⟶ C) (h : p + q = n)
    (x : cocycles A p) (y : cocycles B q) (s : Fin n → G) :
    cochainOf (A := C) (cocycleι (A := C) (p := n)
        (HomologicalComplex.cyclesMap (cochainsMap μ) n (cupCocycles h x y))) s =
      μ.hom (cochainOf (A := A) (cocycleι (A := A) (p := p) x)
          (fun i : Fin p => s ⟨i, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd s ⟨p, by omega⟩)
          (cochainOf (A := B) (cocycleι (A := B) (p := q) y)
            fun j : Fin q => s ⟨p + j, by omega⟩)) := by
  rw [cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cochainOf_cupLocallyConstant]
  rfl

variable {A' B' C' : Rep.{u} k G} [IsDiscreteRep A'] [IsDiscreteRep B'] [IsDiscreteRep C']

theorem cupPairing_cohomologyMap (μ : A ⊗ B ⟶ C) (f : A' ⟶ A) (g : B' ⟶ B) (h : p + q = n)
    (x : cohomology A' p) (y : cohomology B' q) :
    cupPairing μ h (cohomologyMap f p x) (cohomologyMap g q y) =
      cupPairing ((f ⊗ₘ g) ≫ μ) h x y := by
  rw [cupPairing_apply, cupPairing_apply, ← cohomologyMap_tensorHom_cup, cohomologyMap_comp]
  rfl

theorem cohomologyMap_cupPairing (μ : A ⊗ B ⟶ C) (ν : C ⟶ C') (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyMap ν n (cupPairing μ h x y) = cupPairing (μ ≫ ν) h x y := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMap_comp]
  rfl

theorem cohomologyRes_cupPairing (μ : A ⊗ B ⟶ C) (S : Subgroup G) (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyRes C S n (cupPairing μ h x y) =
      cupPairing ((resTensorIso S.subtype A B).inv ≫ (Rep.resFunctor S.subtype).map μ) h
        (cohomologyRes A S p x) (cohomologyRes B S q y) := by
  rw [cupPairing_apply, cupPairing_apply, ← cohomologyMap_resTensorIso_cohomologyRes_cup,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, cohomologyMap_comp_cohomologyRes,
    ← cohomologyMap_comp, Iso.hom_inv_id_assoc]
  rfl

end CupPairing

end GroundTheory.ProfCoh
end
end

section -- merged from GroundTheory.ProfiniteCohomology.CupProducts.GroupCohomology
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Comparison

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

end Comparison

section Levels

variable (U : OpenNormalSubgroup G) {p q n : ℕ}

theorem inflation_π (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    inflation A U p (groupCohomology.π _ p z) =
      cohomologyπ A p (HomologicalComplex.cyclesMap (inflationCochains A U) p z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inflationCochains A U) p) z

theorem cochainOf_cocycleι_cyclesMap_inflationCochains (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    cochainOf (A := A) (cocycleι (A := A) (p := p)
      (HomologicalComplex.cyclesMap (inflationCochains A U) p z)) =
      fun g => (groupCohomology.iCocycles (A.quotientToInvariants (U : Subgroup G)) p z
        (fun i => (g i : G ⧸ (U : Subgroup G))) : A) :=
  congrArg (fun ψ => cochainOf (A := A) (ψ.hom z))
    (HomologicalComplex.cyclesMap_i (inflationCochains A U) p)

theorem inflationCochains_comp_cochainsMap {A A' : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep A'] (f : A ⟶ A') :
    inflationCochains A U ≫ cochainsMap f =
      groupCohomology.cochainsMap (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) ≫ inflationCochains A' U := by
  ext n x : 3
  rfl

theorem inflation_comp_cohomologyMap {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (n : ℕ) :
    inflation A U n ≫ cohomologyMap f n =
      groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n ≫ inflation A' U n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (inflationCochains_comp_cochainsMap U f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

theorem cohomologyMap_inflation {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) n) :
    cohomologyMap f n (inflation A U n x) =
      inflation A' U n (groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n x) :=
  ConcreteCategory.congr_hom (inflation_comp_cohomologyMap U f n) x

variable (A B : Rep.{u} k G) [IsDiscreteRep A] [IsDiscreteRep B]

theorem cup_inflation (h : p + q = n)
    (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) p)
    (y : groupCohomology (B.quotientToInvariants (U : Subgroup G)) q) :
    GroundTheory.ProfCoh.cup h (inflation A U p x) (inflation B U q y) =
      inflation (A ⊗ B) U n (groupCohomology.map (MonoidHom.id _)
        (invariantsTensorHom A B (U : Subgroup G)) n (GroundTheory.GroupCoh.cupH h x y)) := by
  refine groupCohomology_induction_on x fun x => ?_
  refine groupCohomology_induction_on y fun y => ?_
  rw [inflation_π, inflation_π, cup_cohomologyπ, GroundTheory.GroupCoh.cupH_π,
    GroundTheory.GroupCoh.map_π_apply, inflation_π]
  congr 1
  apply cocycles_ext
  rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cyclesMap_inflationCochains, cochainOf_cocycleι_cyclesMap_inflationCochains,
    cochainOf_cocycleι_cyclesMap_inflationCochains, GroundTheory.GroupCoh.iCocycles_cocyclesMap,
    GroundTheory.GroupCoh.iCocycles_cupCocycles]
  funext g
  simp only [GroundTheory.GroupCoh.cupCochain_apply]
  have hP : Fin.partialProd (fun i => (g i : G ⧸ (U : Subgroup G))) ⟨p, by omega⟩ =
      ((Fin.partialProd g ⟨p, by omega⟩ : G) : G ⧸ (U : Subgroup G)) :=
    partialProd_comp_monoidHom (QuotientGroup.mk' (U : Subgroup G)) g _
  rw [hP]
  rfl

end Levels

end GroundTheory.ProfCoh
end
end
