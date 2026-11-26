module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiPiBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (J : Type) [Finite J] (M M' : J → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) (g : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i)), (∀ x i, g x i = f i (x i)) → (∀ i, Function.Bijective (liftSemi (f i))) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ J _ M M' _ _ _ _ f g hg hf
  classical
  haveI := Fintype.ofFinite J
  have key : ∀ y : R' ⊗[R] (∀ i, M i),
      liftSemi g y = Pi.map (fun i => liftSemi (f i)) (TensorProduct.piRight R R' R' M y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => funext i; simp [Pi.map]
    | tmul x m =>
      funext i
      simp [liftSemi_tmul, hg, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]; funext i; simp
  have : (liftSemi g : R' ⊗[R] (∀ i, M i) → ∀ i, M' i)
      = Pi.map (fun i => liftSemi (f i)) ∘ (TensorProduct.piRight R R' R' M) := funext key
  rw [this]
  exact (Function.Bijective.piMap hf).comp (TensorProduct.piRight R R' R' M).bijective

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinear
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_prod_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (f : M →ₛₗ[algebraMap R R'] M') (f' : N →ₛₗ[algebraMap R R'] N') (g : (M × N) →ₛₗ[algebraMap R R'] (M' × N')), (∀ x, g x = (f x.1, f' x.2)) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi f') → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ f f' g hg hf hf'
  have key : ∀ y, liftSemi g y =
      (liftSemi f (TensorProduct.prodRight R R' R' M N y).1,
        liftSemi f' (TensorProduct.prodRight R R' R' M N y).2) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp; rfl
    | tmul x c => simp [liftSemi_tmul, hg]
    | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _)]; ext <;> simp
  have e : ⇑(liftSemi g) = Prod.map (liftSemi f) (liftSemi f') ∘ (TensorProduct.prodRight R R' R' M N) :=
    funext key
  rw [e]
  exact (hf.prodMap hf').comp (TensorProduct.prodRight R R' R' M N).bijective

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeProdBijectiveSemilinearStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseChange_prod_bijective_semilinear : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (f : M →ₛₗ[algebraMap R R'] M') (f' : N →ₛₗ[algebraMap R R'] N') (g : (M × N) →ₛₗ[algebraMap R R'] (M' × N')), (∀ x, g x = (f x.1, f' x.2)) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi f') → Function.Bijective (liftSemi g) := by
  first | exact @GlobalTheory.liftSemi_prod_bijective | exact GlobalTheory.liftSemi_prod_bijective | (intros; apply GlobalTheory.liftSemi_prod_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def piSL {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {J : Type} {M M' : J → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[σ] M' i) : (∀ i, M i) →ₛₗ[σ] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := by funext i; simp
  map_smul' r x := by funext i; simp [map_smulₛₗ]

private theorem piSL_bij {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} [Finite J]
    {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i)
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f _ (fun _ _ ↦ rfl) hf

theorem liftSemi_pullTot1_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs h
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add (α T), map_smul' := hs T }
  have ha : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ h T (a T) fun _ ↦ rfl
  have hsh : ∀ T, SemiHom (algebraMap R R') (α T) := fun T ↦
    semiHom_coef (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F') T
  refine GlobalTheory.T.liftBaseChange_prod_bijective_semilinear R R' _ _ _ _
    (piSL fun T : C ↦ piSL fun T' : C ↦ piSL fun _ : T ⟶ T' ↦ a T')
    (piSL fun T : C ↦ (hsh T).m1) _ (fun _ ↦ rfl) ?_ ?_
  · exact piSL_bij _ fun T ↦ piSL_bij _ fun T' ↦ piSL_bij _ fun _ ↦ ha T'
  · exact piSL_bij _ fun T ↦
      GlobalTheory.T.bijective_liftSemi_of_semilinear_hom R R' _ _ (α T) (hsh T) (a T) (fun _ ↦ rfl) (ha T)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullTot1_bijective | exact GlobalTheory.liftSemi_pullTot1_bijective | (intros; apply GlobalTheory.liftSemi_pullTot1_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalTwoCochainsFiniteCategoryBaseChangeBijectiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiMOm
set_option autoImplicit false

noncomputable section

open TensorProduct GlobalTheory.CechDR GlobalTheory.DeRham

namespace GlobalTheory.FormsBaseChange

theorem bijective_liftSemi_iff {R R' B B' M N : Type} [CommRing R] [CommRing R'] [CommRing B]
    [CommRing B'] [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R R' B'] [Algebra.IsPushout R R' B B']
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [AddCommGroup N] [Module B N] [Module B' N] [Module R' N] [IsScalarTower B B' N]
    [IsScalarTower R' B' N] (φ : M →ₗ[B] N) (g : M →ₛₗ[algebraMap R R'] N) (e : ∀ x, g x = φ x) :
    Function.Bijective (liftSemi g) ↔ IsBaseChange B' φ := by
  have hc : (liftSemi g : R' ⊗[R] M → N) =
      φ.liftBaseChange B' ∘ (Algebra.IsPushout.cancelBaseChange R R' B B' M).symm := by
    funext z
    induction z with
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul s m => simp [e]
  rw [hc, Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]
  constructor
  · intro H
    exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ H) fun x ↦ by simp
  · intro H
    have : (φ.liftBaseChange B' : B' ⊗[B] M → N) = H.equiv := by
      funext z
      induction z with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s m => simp
    rw [this]
    exact H.equiv.bijective

theorem bijective_liftSemi_mOm (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type)
    [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B')
    (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h0 : Function.Bijective (liftSemi f)) (h1 : Function.Bijective (liftSemi h.m1)) (j : ℕ) :
    Function.Bijective (liftSemi (h.mOm j)) := by
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h0) fun x ↦ by
      change liftSemi f (1 ⊗ₜ x) = α x
      rw [liftSemi_tmul, one_smul, hf]⟩
  let φ : Ω[B⁄R] →ₗ[B] Ω[B'⁄R'] :=
    { toFun := h.m1
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.oneFormMap_smul_semilinear, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  have hφ : IsBaseChange B' φ := (bijective_liftSemi_iff φ h.m1 fun _ ↦ rfl).1 h1
  refine (bijective_liftSemi_iff _ (h.mOm j) ?_).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ j)
  let ψ : Om R B j →ₗ[B] Om R' B' j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.mOm_smul, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  suffices H : ψ = _ from fun x ↦ LinearMap.congr_fun H x
  apply exteriorPower.linearMap_ext
  ext1 v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
  refine Subtype.ext ?_
  change h.mDR (exteriorPower.ιMulti B j v : DR R B) = _
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext k
  exact h.mDR_ι _

end GlobalTheory.FormsBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalTwoCochainsFiniteCategoryBaseChangeBijectiv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TotTwoBaseChange

section Pi

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} {M M' : J → Type}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)]

def piSL (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := funext fun i ↦ map_add (f i) (x i) (y i)
  map_smul' r x := funext fun i ↦ map_smulₛₗ (f i) r (x i)

theorem piSL_bijective [Finite J] {f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i}
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f (piSL f) (fun _ _ ↦ rfl) hf

end Pi

section Prod

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M N M' N' : Type}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']

def prodSL (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N') :
    (M × N) →ₛₗ[algebraMap R R'] (M' × N') where
  toFun x := (f x.1, g x.2)
  map_add' x y := Prod.ext (map_add f x.1 y.1) (map_add g x.2 y.2)
  map_smul' r x := Prod.ext (map_smulₛₗ f r x.1) (map_smulₛₗ g r x.2)

theorem prodSL_bijective {f : M →ₛₗ[algebraMap R R'] M'} {g : N →ₛₗ[algebraMap R R'] N'}
    (hf : Function.Bijective (liftSemi f)) (hg : Function.Bijective (liftSemi g)) :
    Function.Bijective (liftSemi (prodSL f g)) :=
  liftSemi_prod_bijective R R' M N M' N' f g (prodSL f g) (fun _ ↦ rfl) hf hg

end Prod

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot2 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs H
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add _, map_smul' := hs T }
  have h : ∀ T : C, SemiHom (algebraMap R R') (α T) := hs
  have h0 : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ H T (a T) fun _ ↦ rfl
  have h1 : ∀ T, Function.Bijective (liftSemi (h T).m1) := fun T ↦
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T)
  have h2 : ∀ T, Function.Bijective (liftSemi ((h T).mOm 2)) := fun T ↦
    GlobalTheory.FormsBaseChange.bijective_liftSemi_mOm R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T) (h1 T) 2
  have k2 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦ piSL_bijective fun T'' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ piSL_bijective fun _ : T' ⟶ T'' ↦ h0 T''
  have k1 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ h1 T'
  have k0 := piSL_bijective h2
  have k := prodSL_bijective k1 k0
  refine liftSemi_prod_bijective R R' (C2 F) (A1 F × W0 F 2) (C2 F') (A1 F' × W0 F' 2) _ _ _ ?_ k2 k
  intro x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ; exact cechDeRhamPullbackTotalDegreeTwo_function_part _ φ ψ x
  · funext T T' φ; exact pullTot2_a _ φ x
  · funext T; exact pullTot2_η _ x T

end GlobalTheory.TotTwoBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalTwoCochainsFiniteCategoryBaseChangeBijectivStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot2 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.TotTwoBaseChange.main | exact GlobalTheory.TotTwoBaseChange.main | (intros; apply GlobalTheory.TotTwoBaseChange.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijecti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijecti
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem totalZeroCochains_finiteCategory_baseChange_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ C _ _ _ F F' α _ hs hb g hg
  let f : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T =>
    { toFun := α T
      map_add' := fun a b => map_add (α T) a b
      map_smul' := fun r b => hs T r b }
  exact liftSemi_pi_bijective R R' C (fun T => F.obj T) (fun T => F'.obj T) f g
    (fun x T => hg x T) (fun T => hb T (f T) (fun _ => rfl))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijectiStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_liftSemi_tot0_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  first | exact @GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | exact GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | (intros; apply GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactCokernel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_bijective_of_exact_cokernel : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (N : Type) [AddCommGroup N] [Module R N] (Z : Type) [AddCommGroup Z] [Module R Z] (Q : Type) [AddCommGroup Q] [Module R Q] (N' : Type) [AddCommGroup N'] [Module R' N'] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (Q' : Type) [AddCommGroup Q'] [Module R' Q'] (d : N →ₗ[R] Z) (p : Z →ₗ[R] Q) (d' : N' →ₗ[R'] Z') (p' : Z' →ₗ[R'] Q') (fN : N →ₛₗ[algebraMap R R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fQ : Q →ₛₗ[algebraMap R R'] Q'), Function.Exact d p → Function.Surjective p → Function.Exact d' p' → Function.Surjective p' → (∀ x, d' (fN x) = fZ (d x)) → (∀ z, p' (fZ z) = fQ (p z)) → Function.Surjective (liftSemi fN) → Function.Bijective (liftSemi fZ) → Function.Bijective (liftSemi fQ) := by
  intro R R' _ _ _ N _ _ Z _ _ Q _ _ N' _ _ Z' _ _ Q' _ _ d p d' p' fN fZ fQ hdp hp hdp' hp' sN sZ hN hZ
  have sqN : ∀ x, liftSemi fZ (d.lTensor R' x) = d' (liftSemi fN x) := by
    intro x
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sN]
  have sqZ : ∀ z, liftSemi fQ (p.lTensor R' z) = p' (liftSemi fZ z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sZ]
  have ex : Function.Exact (d.lTensor R') (p.lTensor R') := lTensor_exact R' hdp hp
  have ps : Function.Surjective (p.lTensor R') := LinearMap.lTensor_surjective R' hp
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := ps y
    rw [sqZ] at hy
    obtain ⟨x', hx'⟩ := (hdp' (liftSemi fZ z)).1 hy
    obtain ⟨x, rfl⟩ := hN x'
    have : d.lTensor R' x = z := hZ.1 (by rw [sqN, hx'])
    rw [← this]
    exact (ex _).2 ⟨x, rfl⟩
  · intro q'
    obtain ⟨z', rfl⟩ := hp' q'
    obtain ⟨z, rfl⟩ := hZ.2 z'
    exact ⟨p.lTensor R' z, sqZ z⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestSide
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlat

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type) [AddCommGroup Z] [Module R Z] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' ci cd hM hN
  have c1 : ∀ x : R' ⊗[R] Z, i' (liftSemi fZ x) = liftSemi fM (LinearMap.lTensor R' i x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r z => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, ci]
  have c2 : ∀ x : R' ⊗[R] M, d' (liftSemi fM x) = liftSemi fN (LinearMap.lTensor R' d x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => simp only [liftSemi_tmul, LinearMap.lTensor_tmul, map_smul, cd]
  have hiB : Function.Injective (LinearMap.lTensor R' i) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (LinearMap.lTensor R' i) (LinearMap.lTensor R' d) :=
    Module.Flat.lTensor_exact R' hid
  refine ⟨fun x y hxy => hiB (hM.1 ?_), fun z' => ?_⟩
  · rw [← c1, ← c1, hxy]
  · obtain ⟨y, hy⟩ := hM.2 (i' z')
    have h0 : LinearMap.lTensor R' d y = 0 := by
      apply hN
      rw [← c2, hy, map_zero]
      exact (hid' (i' z')).2 ⟨z', rfl⟩
    obtain ⟨x, rfl⟩ := (hex y).1 h0
    exact ⟨x, hi' (by rw [c1, hy])⟩

end GlobalTheory.KerFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pullHyp1_bijective_of_finite : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ _ C _ _ _ F F' α hn hs hb
  let m : CoefMap (algebraMap R R') F F' := ⟨𝟭 C, α, hn, hs⟩
  let g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F' :=
    { toFun := fun x T ↦ α T (x T)
      map_add' := fun x y ↦ funext fun T ↦ map_add (α T) (x T) (y T)
      map_smul' := fun r x ↦ funext fun T ↦ hs T r (x T) }
  have h0 : Function.Bijective (liftSemi g) :=
    GlobalTheory.T.bijective_liftSemi_tot0_of_bijective R R' C F F' α hn hs hb g fun _ _ ↦ rfl
  have h1 : Function.Bijective (liftSemi (pullTot1 m)) := GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory R R' C F F' α hn hs hb
  have h2 : Function.Bijective (liftSemi (pullTot2 m)) := GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective R R' C F F' α hn hs hb
  have hZ : Function.Bijective (liftSemi (pullZZ1 m)) :=
    GlobalTheory.KerFlat.main R R' (cechDeRhamTotalCocyclesOne F) (Tot1 F) (Tot2 F) (cechDeRhamTotalCocyclesOne F') (Tot1 F') (Tot2 F')
      (cechDeRhamTotalCocyclesOne F).subtype (dTot1 F) (cechDeRhamTotalCocyclesOne F').subtype (dTot1 F') (pullZZ1 m) (pullTot1 m) (pullTot2 m)
      (cechDeRhamTotalCocyclesOne F).injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F))
      (cechDeRhamTotalCocyclesOne F').injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F'))
      (fun _ ↦ rfl) (fun x ↦ (pullTot2_dTot1 m x).symm) h1 h2.1
  exact GlobalTheory.liftSemi_bijective_of_exact_cokernel R R' (Tot0 F) (cechDeRhamTotalCocyclesOne F) (Hyp1 F) (Tot0 F') (cechDeRhamTotalCocyclesOne F') (Hyp1 F')
    ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F)) (Hyp1.mk F)
    ((dTot0 F').codRestrict (cechDeRhamTotalCocyclesOne F') (dTot0_mem F')) (Hyp1.mk F') g (pullZZ1 m) (pullHyp1 m)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F')
    (fun x ↦ Subtype.ext (pullTot1_dTot0 m x).symm) (fun z ↦ (pullHyp1_mk m z).symm) h0.2 hZ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | exact GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | (intros; apply GlobalTheory.liftSemi_pullHyp1_bijective_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem restrict_cover_affine_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  intro R _ X s J U hU
  apply restrict_bijective_one_of_basis s
  · intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let G : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span G = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  · intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩

end GlobalTheory.CechDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinementStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hyper_cohomology_cover_refinement : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  first | exact @GlobalTheory.CechDR.restrict_cover_affine_bijective | exact GlobalTheory.CechDR.restrict_cover_affine_bijective | (intros; apply GlobalTheory.CechDR.restrict_cover_affine_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverHyp

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) incl)) :=
    GlobalTheory.T.cech_hyper_cohomology_cover_refinement R X s J (fun i => (U i).1) hcov
  have b2 := GlobalTheory.T.hyper_cohomology_restrict_adjoint_bijective R Bᵒᵖ Jᵒᵖ (incl ⋙ OAff s) gc.monotone_u.functor.op gc.monotone_l.functor.op
    gc.adjunction.op
  have e : ∀ c, pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c =
      pullHyp1 (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op)
        (pullHyp1 (CoefMap.restrict (OAff s) incl) c) := fun c =>
    (pullHyp1_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (pullHyp1_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverHyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  first | exact @GlobalTheory.CoverHyp.restrict_bijective | exact GlobalTheory.CoverHyp.restrict_bijective | (intros; apply GlobalTheory.CoverHyp.restrict_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestTail
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' hc
  have key : (e' ∘ liftSemi f) = (liftSemi g ∘ e.baseChange R') := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => simp [liftSemi_tmul, LinearMap.baseChange_tmul, hc]
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  have hb : Function.Bijective (e.baseChange R') := by
    have h := ((LinearEquiv.ofBijective e he).baseChange R R' M N).bijective
    convert h using 1
    refine congrArg DFunLike.coe ?_
    ext m
    simp
  rw [← Function.Bijective.of_comp_iff' he' (liftSemi f), key, Function.Bijective.of_comp_iff _ hb]

end GlobalTheory.Div.BaseChangeIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyFlatBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.HypFlatBaseChange

theorem square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X X' : Scheme.{0}}
    {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap σ)
    {J : Type} [Preorder J] (U : J → X.affineOpens) (hU : Monotone U) (U' : J → X'.affineOpens)
    (hU' : Monotone U') (hle : ∀ i, (U' i).1 ≤ φ ⁻¹ᵁ (U i).1)
    (g : CoefMap σ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')) (θ : 𝟭 _ ⟶ g.G)
    (hg : ∀ T b, g.α T (mp (hU.functor.op ⋙ OAff s) (θ.app T) b) =
      GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), hle _⟩ b) (c : HH1 s) :
    pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op) (pullHH1 w c) =
      pullHyp1 g (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c) := by
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), hle i⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  have k := congrArg (pullHyp1 (CoefMap.restrict (OPair φ s') hp.functor.op)) (isPull1_pullHH1 w c)
  rw [← pullHyp1_comp, ← pullHyp1_comp] at k
  rw [← pullHyp1_comp]
  have k1 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairRes φ s').comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    (CoefMap.restrict (OAff s') hU'.functor.op) (𝟙 _) (fun T b ↦ mp_id (OAff s') _ b) (pullHH1 w c)
  have k2 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairPull w).comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    ((CoefMap.restrict (OAff s) hU.functor.op).comp g) (Functor.whiskerRight θ hU.functor.op)
    (fun T b ↦ hg T b) c
  exact k1.symm.trans (k.symm.trans k2)

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  intro R R' _ _ _ _ X X' s s' φ h hs hq
  obtain ⟨J, _, _, U, hU, hinf, hcov⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s hs hq
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  let U' : J → X'.affineOpens := fun i ↦ ⟨φ ⁻¹ᵁ (U i).1, (U i).2.preimage φ⟩
  have hU' : Monotone U' := fun i j hij x hx ↦ hU hij hx
  have hinf' : ∀ i j, (U' (i ⊓ j)).1 = (U' i).1 ⊓ (U' j).1 := fun i j ↦ by
    change φ ⁻¹ᵁ (U (i ⊓ j)).1 = _
    rw [hinf]; rfl
  have hcov' : ⨆ i, (U' i).1 = ⊤ := by
    change ⨆ i, φ ⁻¹ᵁ (U i).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), le_rfl⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  haveI : Finite Jᵒᵖ := Finite.of_equiv J Opposite.equivToOpposite
  haveI : ∀ T T' : Jᵒᵖ, Finite (T ⟶ T') := fun T T' ↦
    Finite.of_injective (β := T'.unop ⟶ T.unop) Quiver.Hom.unop Quiver.Hom.unop_inj
  have hb := GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective R R' Jᵒᵖ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')
    (fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b)
    (fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun T f hf ↦ GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h ⟨(U' T.unop, U T.unop), le_rfl⟩ rfl f hf)
  have hsq := fun c ↦ square h.w U hU U' hU' (fun _ ↦ le_rfl)
    ⟨𝟭 _, fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩,
      fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b,
      fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩⟩ (𝟙 _)
    (fun T b ↦ congrArg (GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
      (mp_id (hU.functor.op ⋙ OAff s) T b)) c
  exact (GlobalTheory.Div.BaseChangeIso.main R R' (HH1 s) (Hyp1 (hU.functor.op ⋙ OAff s)) (HH1 s')
    (Hyp1 (hU'.functor.op ⋙ OAff s')) (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op))
    (pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op)) (pullHH1 h.w) _
    (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R X s J U hU hinf hcov) (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R' X' s' J U' hU' hinf' hcov') hsq).2 hb

end GlobalTheory.Div.HypFlatBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyFlatBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_cohomology_flat_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  first | exact @GlobalTheory.Div.HypFlatBaseChange.main | exact GlobalTheory.Div.HypFlatBaseChange.main | (intros; apply GlobalTheory.Div.HypFlatBaseChange.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeBijectiveLinearEquivSquareUniv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeBijectiveLinearEquivSquareUniv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BaseChangeIso

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  intro R R' _ _ _ M _ _ N _ _ M' _ _ N' _ _ e e' f g he he' h
  have hsq : ∀ x : R' ⊗[R] M, e' (liftSemi f x) = liftSemi g (e.lTensor R' x) := by
    intro x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, h]
  have hb : Function.Bijective (e.lTensor R') := by
    have := (TensorProduct.congr (LinearEquiv.refl R R') (LinearEquiv.ofBijective e he)).bijective
    convert this using 1
    funext x
    induction x with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul r m => rfl
  have hcomp : (⇑e') ∘ (⇑(liftSemi f)) = (⇑(liftSemi g)) ∘ (⇑(e.lTensor R')) := funext hsq
  constructor
  · intro hf
    have h1 : Function.Bijective ((⇑e') ∘ (⇑(liftSemi f))) := he'.comp hf
    rw [hcomp] at h1
    exact (Function.Bijective.of_comp_iff _ hb).mp h1
  · intro hg
    have h1 : Function.Bijective ((⇑(liftSemi g)) ∘ (⇑(e.lTensor R'))) := hg.comp hb
    rw [← hcomp] at h1
    exact (Function.Bijective.of_comp_iff' he' _).mp h1

end GlobalTheory.BaseChangeIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeBijectiveLinearEquivSquareUnivStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseChange_bijective_linearEquiv_square_univ : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type) [AddCommGroup N'] [Module R' N'] (e : M →ₗ[R] N) (e' : M' →ₗ[R'] N') (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N'), Function.Bijective e → Function.Bijective e' → (∀ x, e' (f x) = g (e x)) → (Function.Bijective (liftSemi f) ↔ Function.Bijective (liftSemi g)) := by
  first | exact @GlobalTheory.BaseChangeIso.main | exact GlobalTheory.BaseChangeIso.main | (intros; apply GlobalTheory.BaseChangeIso.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

open KaehlerDifferential DividedPowers GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm

namespace GlobalTheory.SmoothLift

private theorem crystallineSmoothLift_natural_local :
    ∃ e₁ : ∀ D : Data, CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s,
      ∀ (D D' : Data) (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (h : φ ≫ D.s = D'.s ≫ spMap σ)
        (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c,
        IsPull1 h (e₁ D c) (e₁ D' (m.pull1 c)) := by
  let Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (GlobalTheory.T.nonempty_smoothLiftAffineThickenings D)
  obtain ⟨hr1, -⟩ := GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.1
  choose e₁ he₁ using E1
  refine ⟨e₁, ?_⟩
  intro D D' σ φ φ₀ h m hc c
  exact GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _
    ((he₁ D c _).1 rfl) ((he₁ D' _ _).1 rfl)

end GlobalTheory.SmoothLift

namespace GlobalTheory.CrysFlatBC

open GlobalTheory.SmoothLift

theorem bijective_liftSemi_pull1 : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] (π : D →+* R) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : R, π (algebraMap R D a) = a) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (t : X ⟶ Sp D) (φ : X ⟶ X), Smooth s → IsSeparated s → QuasiCompact s → t = s ≫ spMap π → φ = 𝟙 X → ∀ m : IsMor (dp0 R) s κ t (algebraMap R D) φ, Function.Bijective (liftSemi m.pull1) := by
  intro R D _ _ _ _ π κ hκ hπ X s t φ hs hs' hs'' ht hφ m
  subst hφ ht
  obtain ⟨e₁, n⟩ := GlobalTheory.SmoothLift.crystallineSmoothLift_natural_local
  have hb : spMap π ≫ spMap (algebraMap R D) = 𝟙 _ := by
    rw [← Cris.spMap_comp, show π.comp (algebraMap R D) = RingHom.id R from RingHom.ext hπ, Cris.spMap_id]
  obtain ⟨X', q, s', H⟩ : ∃ (X' : Scheme.{0}) (q : X' ⟶ X) (s' : X' ⟶ Sp D),
      IsPullback q s' s (spMap (algebraMap R D)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  let i : X ⟶ X' := H.lift (𝟙 X) (s ≫ spMap π) (by rw [Category.assoc, hb]; simp)
  have hiq : i ≫ q = 𝟙 X := H.lift_fst _ _ _
  have his : i ≫ s' = s ≫ spMap π := H.lift_snd _ _ _
  have hp : IsPullback i s s' (spMap π) :=
    IsPullback.of_right (by rw [hiq, hb]; exact IsPullback.id_horiz s) his H
  have k1 : Smooth s' := MorphismProperty.of_isPullback (P := @Smooth) H hs
  have k2 : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) H hs'
  have k3 : QuasiCompact s' := MorphismProperty.of_isPullback (P := @QuasiCompact) H hs''
  let D₀ := Data.self s hs hs' hs''
  let D' := Data.ofQuot κ hκ π (fun a ↦ ⟨_, hπ a⟩) rfl s' s i k1 k2 k3 hp _ rfl
  have w : 𝟙 X ≫ 𝟙 X = i ≫ q := by rw [hiq, Category.id_comp]
  have key := n D₀ D' (algebraMap R D) q (𝟙 X) H.w m w
  obtain ⟨e, e', he⟩ : ∃ (e : Cris.H1 (dp0 R) s ≃ₗ[R] HH1 s) (e' : Cris.H1 κ (s ≫ spMap π) ≃ₗ[D] HH1 s'),
      ∀ c, IsPull1 H.w (e c) (e' (m.pull1 c)) := ⟨e₁ D₀, e₁ D', key⟩
  exact (GlobalTheory.T.liftBaseChange_bijective_linearEquiv_square_univ R D (Cris.H1 (dp0 R) s) (HH1 s) (Cris.H1 κ (s ≫ spMap π)) (HH1 s')
    e.toLinearMap e'.toLinearMap m.pull1 (pullHH1 H.w) e.bijective e'.bijective fun c ↦ (he c).eq_pullHH1).2
    (GlobalTheory.T.hyper_cohomology_flat_base_change R D X X' s s' q H hs' hs'')

end GlobalTheory.CrysFlatBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFrobeniusSemilinearBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_thickening_pullback_bijective : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] [Module.Flat R D] (π : D →+* R) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : R, π (algebraMap R D a) = a) → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (t : X ⟶ Sp D) (φ : X ⟶ X), Smooth s → IsSeparated s → QuasiCompact s → t = s ≫ spMap π → φ = 𝟙 X → ∀ m : IsMor (dp0 R) s κ t (algebraMap R D) φ, Function.Bijective (liftSemi m.pull1) := by
  first | exact @GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 | exact GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 | (intros; apply GlobalTheory.CrysFlatBC.bijective_liftSemi_pull1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSemiBijectiveOfExactLarge
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatKerLarge

theorem liftSemi_bijective_of_exact {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    [Module.Flat R R'] {Z M N Z' M' N' : Type*}
    [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Z'] [Module R' Z'] [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']
    (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N')
    (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M')
    (fN : N →ₛₗ[algebraMap R R'] N')
    (hi : Function.Injective i) (hid : Function.Exact i d) (hi' : Function.Injective i')
    (hid' : Function.Exact i' d') (hZ : ∀ z, i' (fZ z) = fM (i z)) (hN : ∀ x, d' (fM x) = fN (d x))
    (hM : Function.Bijective (liftSemi fM)) (hNi : Function.Injective (liftSemi fN)) :
    Function.Bijective (liftSemi fZ) := by
  have sqZ : ∀ w, i' (liftSemi fZ w) = liftSemi fM (i.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hZ]
  have sqN : ∀ w, d' (liftSemi fM w) = liftSemi fN (d.lTensor R' w) := fun w ↦ by
    induction w with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x z => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, hN]
  have hinj : Function.Injective (i.lTensor R') :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hex : Function.Exact (i.lTensor R') (d.lTensor R') := Module.Flat.lTensor_exact R' hid
  refine ⟨fun a b hab ↦ hinj (hM.1 ?_), fun z' ↦ ?_⟩
  · rw [← sqZ, ← sqZ, hab]
  · obtain ⟨m, hm⟩ := hM.2 (i' z')
    have h0 : d.lTensor R' m = 0 := hNi (by rw [← sqN, hm, hid'.apply_apply_eq_zero, map_zero])
    obtain ⟨w, rfl⟩ := (hex m).1 h0
    exact ⟨w, hi' (by rw [sqZ, hm])⟩

theorem liftSemi_bijective_of_exact_large : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (Z : Type 1) [AddCommGroup Z] [Module R Z] (M : Type 1) [AddCommGroup M] [Module R M] (N : Type 1) [AddCommGroup N] [Module R N] (Z' : Type 1) [AddCommGroup Z'] [Module R' Z'] (M' : Type 1) [AddCommGroup M'] [Module R' M'] (N' : Type 1) [AddCommGroup N'] [Module R' N'] (i : Z →ₗ[R] M) (d : M →ₗ[R] N) (i' : Z' →ₗ[R'] M') (d' : M' →ₗ[R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fM : M →ₛₗ[algebraMap R R'] M') (fN : N →ₛₗ[algebraMap R R'] N'), Function.Injective i → Function.Exact i d → Function.Injective i' → Function.Exact i' d' → (∀ z, i' (fZ z) = fM (i z)) → (∀ x, d' (fM x) = fN (d x)) → Function.Bijective (liftSemi fM) → Function.Injective (liftSemi fN) → Function.Bijective (liftSemi fZ) := by
  intro R R' _ _ _ _ Z _ _ M _ _ N _ _ Z' _ _ M' _ _ N' _ _ i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi
  exact liftSemi_bijective_of_exact i d i' d' fZ fM fN hi hid hi' hid' hZ hN hM hNi

end GlobalTheory.FlatKerLarge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickenin
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem primCris_isBC_of_nilThick : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  intro A₀ _ g hA _ D _ _ π κ hκ hπ k
  haveI : Smooth A₀.hom := hA.smooth
  haveI : IsProper A₀.hom := hA.proper
  let P : Over (Sp ℂ) := A₀ ⊗ A₀
  haveI : Smooth P.hom := smooth_tensorObj_hom A₀ A₀
  haveI : IsProper P.hom := by
    change IsProper (A₀ ⊗ A₀).hom
    rw [Over.tensorObj_hom]; infer_instance
  have m2 : IsMor (dp0 ℂ) (P.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) (𝟙 P.left) :=
    ⟨k.dp, by rw [Category.assoc, ← k.base]; simp⟩
  have key : ∀ (f : P ⟶ A₀) (x : FirstDeRham (A₀.hom ≫ 𝟙 _)),
      pullOver κ (spMap π) f (k.isMor.pull1 x) = m2.pull1 (pullOver (dp0 ℂ) (𝟙 _) f x) := by
    intro f x
    have h'' : IsMor (dp0 ℂ) (A₀.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) f.left :=
      ⟨k.dp, by rw [← Category.assoc, Over.w f, Category.assoc, ← k.base]; simp⟩
    exact (IsMor.pullback1_comp k.isMor
        (IsMor.of_over κ (φ := f.left) (by rw [← Category.assoc, Over.w])) h'' (fun _ ↦ rfl)
        (by simp) x).trans
      (IsMor.pullback1_comp (IsMor.of_over (dp0 ℂ) (φ := f.left) (by rw [← Category.assoc, Over.w]))
        m2 h'' (fun _ ↦ rfl) (by simp) x).symm
  have hM : Function.Bijective (liftSemi k.isMor.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ A₀.left (A₀.hom ≫ 𝟙 _) (A₀.hom ≫ spMap π) (Over.Hom.left (𝟙 A₀))
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) (by simp) k.isMor
  have hN : Function.Bijective (liftSemi m2.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ P.left (P.hom ≫ 𝟙 _) (P.hom ≫ spMap π) (𝟙 P.left)
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) rfl m2
  have hZ : Function.Bijective (liftSemi k.pull) := by
    refine GlobalTheory.FlatKerLarge.liftSemi_bijective_of_exact_large ℂ D _ _ _ _ _ _ (prim (dp0 ℂ) (𝟙 _) A₀).subtype
      (pullOver (dp0 ℂ) (𝟙 _) μ[A₀] - pullOver (dp0 ℂ) (𝟙 _) (fst A₀ A₀) - pullOver (dp0 ℂ) (𝟙 _) (snd A₀ A₀))
      (prim κ (spMap π) A₀).subtype
      (pullOver κ (spMap π) μ[A₀] - pullOver κ (spMap π) (fst A₀ A₀) - pullOver κ (spMap π) (snd A₀ A₀))
      k.pull k.isMor.pull1 m2.pull1 (Submodule.injective_subtype _) ?_ (Submodule.injective_subtype _) ?_
      (fun _ ↦ rfl) ?_ hM hN.1
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro x
      simp only [LinearMap.sub_apply, map_sub, key]
  refine ⟨hZ, eq_top_iff.2 fun y _ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hZ.2 y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickeninStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  first | exact @GlobalTheory.primCris_isBC_of_nilThick | exact GlobalTheory.primCris_isBC_of_nilThick | (intros; apply GlobalTheory.primCris_isBC_of_nilThick <;> assumption)
end
