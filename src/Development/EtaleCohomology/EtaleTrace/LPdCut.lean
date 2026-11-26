module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleTrace.LPdCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LPdCut

def Dp (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) : (PN k N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

def LChart : Prop := ∀ (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)),
  ∃ j : Spec (CommRingCat.of (MvPolynomial (Fin N) k)) ⟶ PN k N, IsOpenImmersion j ∧
    j ≫ PNto k N = Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k)) ∧
    Set.range j = (Dp k N i : Set (PN k N))

def LProper : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsProper (PNto k N)

def LSmooth : Prop := ∀ (k : Type) [Field k] (N : ℕ), SmoothOfRelativeDimension N (PNto k N)

def LEmpty : Prop := A5 → A9 → ∀ (R : Type) [CommRing R] (X : Scheme.{0}), IsEmpty X → ∀ (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj X) F n)

theorem unit_of {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) {q : ℕ} (h : IsUnit (q : k)) : IsUnit (q : Γ(X, ⊤)) := by
  simpa using (h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom

end LateralTheory.EtaleTrace.LPdCut

end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem freeGen_nat (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x : uliftFunctor.{1, 0}.obj (P.obj (op U)))))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  simp only [Sec.res, freeGen]
  refine h.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)))
    (by simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map]
        exact Finsupp.mapDomain_single)

theorem evNat : EvNat := by
  intro R _ F X U α x
  have h := freeGen_nat R ((sch.obj X).obj (op (SimplexCategory.mk 0))) x (𝟙 X : Sx (sch.obj X) 0 X)
  have hx : ((sch.obj X).obj (op (SimplexCategory.mk 0))).map x.op (𝟙 X : Sx (sch.obj X) 0 X) = (x : Sx (sch.obj X) 0 U) :=
    Category.comp_id x
  rw [hx] at h
  simp only [ev]
  rw [← h]
  simp only [Sec.res]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenOutGluePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOnAgree : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (U U' : X.Opens) (πU : U.toScheme ⟶ PN k N) (πU' : U'.toScheme ⟶ PN k N),
  GenOn p w U πU → GenOn p w U' πU' → pullback.fst U.ι U'.ι ≫ πU = pullback.snd U.ι U'.ι ≫ πU'

def GenOnGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (π : X ⟶ PN k N) (U : X.Opens),
  genericPoint X ∈ U → GenOn p w U (U.ι ≫ π) → Gen p π w

theorem GenOutGlue_of (h1 : GenOnAgree) (h2 : GenOnGen) : GenOutGlue := by
  intro k _ X _ p N w hloc
  choose U πU hxU hover hgen using hloc
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨x, hxU x⟩
  let 𝒰 := X.openCoverOfIsOpenCover U hcov
  have hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ πU x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ πU y :=
    fun x y => h1 k p N w (U x) (U y) (πU x) (πU y) (hgen x) (hgen y)
  refine ⟨𝒰.glueMorphisms πU hf, ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun x => ?_
    have e : 𝒰.f x ≫ 𝒰.glueMorphisms πU hf = πU x := 𝒰.ι_glueMorphisms πU hf x
    rw [← Category.assoc, e]
    exact hover x
  · have hη := 𝒰.ι_glueMorphisms πU hf (genericPoint X)
    refine h2 k p N w _ (U (genericPoint X)) (hxU _) ?_
    have : (U (genericPoint X)).ι ≫ 𝒰.glueMorphisms πU hf = πU (genericPoint X) := hη
    rw [this]
    exact hgen _

theorem genOnGen : GenOnGen := by
  intro k _ X _ p N w π U hη hG n hn f hf
  obtain ⟨h1, h2⟩ := hG hη n hn f hf
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact Iff.rfl
  · intro m g hg h
    have h' := h2 m g hg h
    have hinj : Function.Injective (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom :=
      haveI : IsIso (U.ι.stalkMap ⟨genericPoint X, hη⟩) :=
        (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
      ((asIso (U.ι.stalkMap ⟨genericPoint X, hη⟩)).commRingCatIsoToRingEquiv).injective
    apply hinj
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ?_ (map_pow _ _ _)).trans h')
    rw [Scheme.Hom.comp_app]
    exact (Scheme.Hom.germ_stalkMap_apply U.ι (π ⁻¹ᵁ Proj.basicOpen _ f) ⟨genericPoint X, hη⟩ h
      (π.app _ (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))))

theorem GenOutGlue_of_agree (h1 : GenOnAgree) : GenOutGlue :=
  GenOutGlue_of h1 genOnGen

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.PNIntegralPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem hl_reduced (k : Type) [Field k] (d : ℕ) (P : Ideal (MvPolynomial (Fin (d + 1)) k)) [P.IsPrime] :
    _root_.IsReduced (HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) P) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  apply HomogeneousLocalization.val_injective
  have h : a.val ^ n = 0 := by
    rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]
  rw [HomogeneousLocalization.val_zero]
  exact IsReduced.eq_zero _ ⟨n, h⟩

theorem pn_reduced (k : Type) [Field k] (d : ℕ) : IsReduced (PN k d) := by
  have : ∀ x : PN k d, _root_.IsReduced ((PN k d).presheaf.stalk x) := by
    intro x
    haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    haveI := hl_reduced k d x.asHomogeneousIdeal.toIdeal
    let e := Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) x
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk _

theorem mvPolynomial_irrelevantIdeal_not_le_bot_projective (k : Type) [Field k] (d : ℕ) :
    ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ≤ ⊥ := by
  intro h
  have hm : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k 0)) (by decide)
  have h2 : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)).toIdeal := h hm
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h2
  exact X_ne_zero _ h2

def gen (k : Type) [Field k] (d : ℕ) : PN k d where
  asHomogeneousIdeal := ⊥
  isPrime := by
    show (⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := mvPolynomial_irrelevantIdeal_not_le_bot_projective k d

theorem pn_irred (k : Type) [Field k] (d : ℕ) : IrreducibleSpace (PN k d) := by
  rw [irreducibleSpace_def]
  have : (Set.univ : Set (PN k d)) = closure {gen k d} := by
    ext y
    simp only [Set.mem_univ, true_iff]
    exact (ProjectiveSpectrum.le_iff_mem_closure (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) (gen k d) y).1
      (show (gen k d).asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (PN k d))
  rw [this]
  exact isIrreducible_singleton.closure

theorem PNIntegral_of : PNIntegral := fun k _ d => by
  haveI := pn_reduced k d
  haveI := pn_irred k d
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.EtaleTrace.Cov
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenEtalePfData
section -- merged from Development.EtaleCohomology.EtaleTrace.GenEtalePfCut
section -- merged from Development.EtaleCohomology.EtaleTrace.GenEtalePfBasic
section -- merged from Development.EtaleCohomology.EtaleTrace.GenEtalePf
namespace LateralTheory.EtaleTrace.GenEtaleRing

theorem ring_gen_etale (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [Algebra.IsEtaleAt A (⊥ : Ideal B)] :
    ∃ a : A, a ≠ 0 ∧ ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap A B a) B' → Algebra.Etale A' B' := by
  haveI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  obtain ⟨f, hf, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  have hf0 : f ≠ 0 := by simpa using hf
  obtain ⟨a, ha, g, hg⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf0)
  refine ⟨a, ha, fun A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have hloc : Algebra.Etale A (Localization.Away (algebraMap A B a)) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at hEt ⊢
    refine subset_trans ?_ hEt
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  haveI : Algebra.Etale A B' := Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B a))
      (Localization.Away (algebraMap A B a)) B').restrictScalars A)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) B' := by
    rw [Algebra.algebraMapSubmonoid_powers]; exact hB
  haveI : Algebra.FormallyEtale A' B' := Algebra.FormallyEtale.localization_base (Submonoid.powers a)
  haveI : Algebra.FiniteType A A' := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) A'
  haveI : Algebra.FinitePresentation A' B' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.GenEtaleRing

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineSetup : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom ∧
    ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime, (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

def EtaleOverBasic : Prop := ∀ {X P : Scheme.{0}} (π : X ⟶ P) (U : P.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) →
  ∀ a : Γ(P, U), (letI := (π.app U).hom.toAlgebra;
    ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra Γ(P, U) A'] [Algebra Γ(X, π ⁻¹ᵁ U) B']
      [Algebra A' B'] [Algebra Γ(P, U) B'] [IsScalarTower Γ(P, U) A' B'] [IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap Γ(P, U) Γ(X, π ⁻¹ᵁ U) a) B' → Algebra.Etale A' B') →
  Etale (π ∣_ P.basicOpen a)

theorem GenEtale_of (h1 : GenAffineSetup) (h2 : EtaleOverBasic) : GenEtale := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hnoeth, hfinU, hinj, _, het⟩ := h1 k p r π hπ hr hfin hsurj hun
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  haveI : Nonempty (π ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := hsurj.surj hne.some
    exact ⟨⟨x, show π x ∈ U by rw [hx]; exact hne.some_mem⟩⟩
  letI := (π.app U).hom.toAlgebra
  haveI : Module.Finite Γ(P, U) Γ(X, π ⁻¹ᵁ U) := hfinU
  haveI : FaithfulSMul Γ(P, U) Γ(X, π ⁻¹ᵁ U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  obtain ⟨a, ha, H⟩ := LateralTheory.EtaleTrace.GenEtaleRing.ring_gen_etale Γ(P, U) Γ(X, π ⁻¹ᵁ U)
  refine ⟨P.basicOpen a, ?_, h2 π U hU hU' a H⟩
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  have : P.basicOpen a = ⊥ := by ext1; simpa using hc
  exact ha ((basicOpen_eq_bot_iff a).1 this)

end LateralTheory.EtaleTrace.Cov
end

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem etaleOverBasic : EtaleOverBasic := by
  intro X P π U hU hU' a H
  have hle : π ⁻¹ᵁ P.basicOpen a ≤ π ⁻¹ᵁ U := π.preimage_mono (P.basicOpen_le a)
  have key : RingHom.Etale (π.app (P.basicOpen a)).hom := by
    letI := (π.app U).hom.toAlgebra
    letI : Algebra Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    letI : Algebra Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app _).hom.toAlgebra
    letI : Algebra Γ(P, U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(P, U) Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      show (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom =
        (P.presheaf.map (homOfLE (P.basicOpen_le a)).op ≫ π.app (P.basicOpen a)).hom
      rw [π.naturality]; rfl
    have hA : IsLocalization.Away a Γ(P, P.basicOpen a) := hU.isLocalization_basicOpen a
    have gen : ∀ (W : X.Opens) (e : W ≤ π ⁻¹ᵁ U), W = X.basicOpen (π.app U a) →
        @IsLocalization.Away _ _ (π.app U a) Γ(X, W) _ (X.presheaf.map (homOfLE e).op).hom.toAlgebra := by
      rintro W e rfl; exact hU'.isLocalization_basicOpen _
    exact H _ _ hA (gen _ hle (π.preimage_basicOpen a))
  haveI : IsAffine (P.basicOpen a).toScheme := hU.basicOpen a
  haveI : IsAffine (π ⁻¹ᵁ P.basicOpen a).toScheme := by
    have := hU'.basicOpen (π.app U a); rw [← π.preimage_basicOpen a] at this; exact this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have hW : (P.basicOpen a).ι ''ᵁ ⊤ = P.basicOpen a := by simp
  have gen2 : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = P.basicOpen a →
      RingHom.Etale (π.app W ≫ X.presheaf.map (eqToHom h).op).hom := by
    rintro W T h rfl
    subst h
    simpa using key
  exact gen2 _ _ _ hW

end LateralTheory.EtaleTrace.Cov
end

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineData : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom

def GenEtaleAtBot : Prop := ∀ {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (π : X ⟶ P) (U : P.Opens), IsAffineOpen U →
  (U : Set P).Nonempty → IsAffineOpen (π ⁻¹ᵁ U) → (π.app U).hom.Finite → Function.Injective (π.app U).hom →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime,
    (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

theorem GenAffineSetup_of (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenAffineSetup := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hN, hf, hi⟩ := h1 k p r π hπ hr hfin hsurj
  exact ⟨U, hU, hne, hU', hN, hf, hi, h2 π U hU hne hU' hf hi hun⟩

theorem GenEtale_of' (h1 : GenAffineData) (h2 : GenEtaleAtBot) : GenEtale :=
  GenEtale_of (GenAffineSetup_of h1 h2) etaleOverBasic

end LateralTheory.EtaleTrace.Cov
end

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem genAffineData : GenAffineData := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj
  obtain ⟨x⟩ : Nonempty P := inferInstance
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens (show x ∈ (⊤ : P.Opens) from trivial)
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  refine ⟨U, hU, ⟨x, hxU⟩, hU', ?_, ?_, ?_⟩
  · have hft : (r.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) r hr ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    letI := (r.appLE ⊤ U le_top).hom.toAlgebra
    haveI : IsNoetherianRing Γ(S k, ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
    haveI : Algebra.FiniteType Γ(S k, ⊤) Γ(P, U) := hft
    exact Algebra.FiniteType.isNoetherianRing Γ(S k, ⊤) Γ(P, U)
  · haveI : IsAffine U := hU
    have h0 : (π ∣_ U).appTop.hom.Finite := (π ∣_ U).finite_appTop
    rw [morphismRestrict_appTop] at h0
    have gen : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = U →
        RingHom.Finite (π.app W ≫ X.presheaf.map (eqToHom h).op).hom → RingHom.Finite (π.app U).hom := by
      rintro W T h rfl
      subst h
      simp
    exact gen _ _ _ (by simp) h0
  · haveI : IsDominant π := inferInstance
    haveI : IsSchemeTheoreticallyDominant π := .of_isDominant π
    exact π.app_injective U

theorem GenEtale_of_atBot (h : GenEtaleAtBot) : GenEtale := GenEtale_of' genAffineData h

end LateralTheory.EtaleTrace.Cov
end

section -- merged from Development.EtaleCohomology.EtaleTrace.TwZeroPfSplit
section -- merged from Development.EtaleCohomology.EtaleTrace.TwZeroPf
section -- merged from Development.EtaleCohomology.EtaleTrace.TwZeroPfGlue
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_sec_eq_of_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated F U S hS y z (fun _ g hg => hP _ g hg)

theorem tz_twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen (q := q) 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  Loc U fun V g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val

theorem TwZero_of_primLoc (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hP : PrimLoc) : TwZero := by
  intro q _ U ζ ξ
  obtain ⟨-, -, T3⟩ := hTw q 0
  apply tz_sec_eq_of_loc
  obtain ⟨S, hS, hP'⟩ := hP q U ζ ξ
  refine ⟨S, hS, fun _ g hg => ?_⟩
  obtain ⟨a, ha⟩ := hP' _ g hg
  rw [T3, T3]
  exact (tz_twGen_eq_of_pow _ _ a ha).symm

end LateralTheory.EtaleTrace
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

def PrimSplit : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A), ∃ e : Fin q → A,
  (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ.1 = e i * ζ.1 ^ (i : ℕ)) ∧ (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0)

def SplitLoc : Prop := ∀ (U : Scheme.{0}) (n : ℕ) (e : Fin n → Γ(U, ⊤)), (∀ i, IsIdempotentElem (e i)) → ∑ i, e i = 1 →
  Loc U fun V g => ∃ i, g.appTop.hom (e i) = 1

theorem primLoc_of (hS : PrimSplit) (hL : SplitLoc) : PrimLoc := by
  intro q _ U ζ ξ
  obtain ⟨e, he, hs, hx, hc⟩ := hS q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hSc, hP⟩ := hL U q e he hs
  refine ⟨S, hSc, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have key : g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (i : ℕ) := by
    have := congrArg g.appTop.hom (hx i)
    simpa [map_mul, map_pow, hi] using this
  by_cases hcop : Nat.Coprime (i : ℕ) q
  · refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _
    rw [key, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  · have h0 := hc i hcop
    rw [h0, map_zero] at hi
    have : Subsingleton Γ(V, ⊤) := subsingleton_of_zero_eq_one hi
    exact ⟨1, Subsingleton.elim _ _⟩

theorem TwZero_of (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) (hL : SplitLoc) : TwZero :=
  TwZero_of_primLoc hTw (primLoc_of hS hL)

end LateralTheory.EtaleTrace
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_isUnit_ι (X : Scheme.{0}) (f : Γ(X, ⊤)) : IsUnit ((X.basicOpen f).ι.appTop.hom f) := by
  have h := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  rw [Scheme.Opens.ι_appTop]
  have e1 : (X.basicOpen f).ι ''ᵁ ⊤ = X.basicOpen f := by simp
  have key : ∀ (W : X.Opens) (_ : W = X.basicOpen f) (hle : W ≤ ⊤), IsUnit ((X.presheaf.map (homOfLE hle).op).hom f) := by
    rintro W rfl hle
    exact h
  exact key _ e1 _

theorem tz_idem_one {A : Type} [CommRing A] {x : A} (h : IsIdempotentElem x) (hu : IsUnit x) : x = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have := congrArg (· * ((u⁻¹ : Aˣ) : A)) h.eq
  simpa [mul_assoc] using this

theorem splitLoc : SplitLoc := by
  intro U n e he hs
  let W : Fin n → U.Opens := fun i => U.basicOpen (e i)
  have hW : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
    rw [TopologicalSpace.Opens.mem_iSup]
    by_contra hx
    push Not at hx
    have hm : ∀ i, U.presheaf.germ ⊤ x trivial (e i) ∈ IsLocalRing.maximalIdeal (U.presheaf.stalk x) := fun i =>
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 ((Scheme.mem_basicOpen_top _ _ x).not.1 (hx i)))
    have hsum := Ideal.sum_mem (IsLocalRing.maximalIdeal _) (t := Finset.univ) (fun i _ => hm i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hs, map_one] at hsum
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hsum)
  let 𝒰 := U.openCoverOfIsOpenCover W hW
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, ?_, ?_⟩
  · exact Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰)
  · rintro V g ⟨Y, h, f, ⟨i⟩, rfl⟩
    let j : Fin n := i
    refine ⟨j, ?_⟩
    have h1 : (W j).ι.appTop.hom (e i) = 1 := tz_idem_one ((he j).map _) (tz_isUnit_ι U (e j))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    change h.appTop.hom ((W j).ι.appTop.hom (e j)) = 1
    rw [h1]; exact map_one _

theorem TwZero_of_split (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) : TwZero :=
  TwZero_of hTw hS splitLoc

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenOfAwayPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

def pg {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) (U : (PN (k := k) N).Opens)
    (hU : genericPoint X ∈ ι ⁻¹ᵁ U) : Γ(PN (k := k) N, U) →+* X.functionField :=
  (ι.app U ≫ X.presheaf.germ _ (genericPoint X) hU).hom

theorem pg_res {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) {U V : (PN (k := k) N).Opens} (hVU : V ≤ U)
    (hV : genericPoint X ∈ ι ⁻¹ᵁ V) (hU : genericPoint X ∈ ι ⁻¹ᵁ U) (s : Γ(PN (k := k) N, U)) :
    pg ι V hV ((PN (k := k) N).presheaf.map (homOfLE hVU).op s) = pg ι U hU s := by
  show (((PN (k := k) N).presheaf.map (homOfLE hVU).op ≫ ι.app V) ≫ X.presheaf.germ _ _ hV).hom s = _
  rw [Scheme.Hom.naturality, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem away_eq {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n)) :
    away ι f hf h m g hg = pg ι _ h (Proj.awayToSection _ f (Away.mk _ hf m g hg)) := rfl

theorem away_identity (x f g : MvPolynomial (Fin (N + 1)) k) {n m : ℕ} (hx : x ∈ A k N 1) (hf : f ∈ A k N n)
    (hg : g ∈ A k N (m • n)) (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    awayMap (A k N) hx (show x * f = f * x from mul_comm _ _) (Away.mk _ hf m g hg) *
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx n f hf') ^ m =
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx (m * n) g hg') := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, awayMap_mk,
    Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, one_mul]
  ring

theorem away_self_pow (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) (n : ℕ)
    (h : x ^ n ∈ A k N (n • 1)) : Away.mk (A k N) hx n (x ^ n) h = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem away_self_pow' (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) {m n : ℕ} (hmn : m = n)
    (h : x ^ n ∈ A k N (m • 1)) : Away.mk (A k N) hx m (x ^ n) h = 1 := by
  subst hmn; exact away_self_pow x hx m h

theorem key {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) (i : Fin (N + 1))
    (hi : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (hfη : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n))
    (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    away ι f hf hfη m g hg * away ι (MvPolynomial.X i) (X_mem k N i) hi n f hf' ^ m =
      away ι (MvPolynomial.X i) (X_mem k N i) hi (m * n) g hg' := by
  have hF : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i * f) := by
    rw [Proj.basicOpen_mul]; exact ⟨hi, hfη⟩
  have e1 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) hf (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl) y)) =
      pg ι _ hi (Proj.awayToSection _ (MvPolynomial.X i) y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) hf
      (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hi _
  have e2 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) (X_mem k N i) (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _) y)) =
      pg ι _ hfη (Proj.awayToSection _ f y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) (X_mem k N i)
      (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hfη _
  rw [away_eq, away_eq, away_eq, ← e2, ← e1, ← e1, ← map_pow, ← map_mul, ← away_identity _ _ _ _ hf hg hf' hg',
    map_mul, map_pow]
  simp only [map_mul, map_pow]

theorem basicOpen_le (i : Fin (N + 1)) {n : ℕ} (hn : 0 < n) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ A k N n) (hf' : f ∈ A k N (n • 1)) :
    (PN (k := k) N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) ≤
      Proj.basicOpen (A k N) f := by
  intro y hy
  have hyU : y ∈ Proj.basicOpen (A k N) (MvPolynomial.X i) := (PN (k := k) N).basicOpen_le _ hy
  let y' : (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).toScheme := ⟨y, hyU⟩
  have h1 : y' ∈ (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).ι ⁻¹ᵁ
      (PN (k := k) N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) := hy
  rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen, ← SpecMap_preimage_basicOpen] at h1
  have ht : Away.isLocalizationElem (X_mem k N i) hf = Away.mk _ (X_mem k N i) n f hf' := by
    apply val_injective; simp [Away.val_mk]
  have h2 : y' ∈ Proj.basicOpenToSpec (A k N) (MvPolynomial.X i) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem k N i) hf) := by
    rw [ht]; exact h1
  rw [← Proj.awayι_preimage_basicOpen (A k N) (X_mem k N i) one_pos hf hn, ← Scheme.Hom.comp_preimage,
    ← Proj.basicOpenIsoSpec_inv_ι _ _ (X_mem k N i) one_pos, ← Proj.basicOpenIsoSpec_hom _ _ (X_mem k N i) one_pos,
    Iso.hom_inv_id_assoc] at h2
  exact h2

theorem GenOfAway_of : GenOfAway := by
  intro k _ X _ p N ι hp i h hE n hn f hf
  have hf' : f ∈ A k N (n • 1) := by simpa using hf
  have hfv : away ι (MvPolynomial.X i) (X_mem k N i) h n f hf' = eval₂ (kHom p) (coordAt ι i h) f := hE n f hf'
  refine ⟨⟨fun hfη => ?_, fun hne => ?_⟩, fun m g hg hfη => ?_⟩
  · have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N (1 • n) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have hx' : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N ((1 * n) • 1) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have h1 : away ι (MvPolynomial.X i) (X_mem k N i) h (1 * n) _ hx' = 1 := by
      rw [away_eq, away_self_pow' _ _ (one_mul n), map_one, map_one]
    have := key ι i h f hf hfη 1 _ hx hf' hx'
    rw [h1, hfv] at this
    intro h0
    rw [h0] at this
    simp at this
  · have hu : IsUnit (X.presheaf.germ _ (genericPoint X) h
        (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')))) := by
      rw [← hfv] at hne; exact isUnit_iff_ne_zero.mpr hne
    rw [← Scheme.mem_basicOpen, ← Scheme.preimage_basicOpen] at hu
    exact basicOpen_le i hn f hf hf' hu
  · have hg' : g ∈ A k N ((m * n) • 1) := by simpa using hg
    have := key ι i h f hf hfη m g hg hf' hg'
    rw [hfv, hE (m * n) g hg'] at this
    exact this

end LateralTheory.EtaleTrace.Cov.GenInPf
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.GenAwayEvalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

theorem fromSpec_eq {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Proj.isAffineOpen_basicOpen (A k N) f hf hd).fromSpec =
      Spec.map (Proj.awayToSection (A k N) f) ≫ Proj.awayι (A k N) f hf hd := by
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
  have e : (Proj.isAffineOpen_basicOpen (A k N) f hf hd).isoSpec.hom ≫ Spec.map (Proj.awayToSection (A k N) f) =
      (Proj.basicOpenIsoSpec (A k N) f hf hd).hom := by
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, IsAffineOpen.isoSpec_hom]
  rw [e, Iso.hom_inv_id, Category.id_comp]

theorem constSecC {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (CommRingCat.of (A k N 0))).inv ≫
      (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top =
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f := by
  have hU := Proj.isAffineOpen_basicOpen (A k N) f hf hd
  have key : hU.fromSpec ≫ Proj.toSpecZero (A k N) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f) := by
    rw [fromSpec_eq hf hd, Category.assoc, Proj.awayι_toSpecZero, Spec.map_comp]
  have h1 : (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top ≫
      hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge =
      (hU.fromSpec ≫ Proj.toSpecZero (A k N)).appLE ⊤ ⊤ (by simp) := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  simp only [key] at h1
  have h3 : hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((congrArg _ (Subsingleton.elim _ (𝟙 _))).trans ((Spec _).presheaf.map_id _))).trans
      (Category.comp_id _)
  have h4 : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) e, (Spec.map g).appLE ⊤ ⊤ e = (Spec.map g).appTop := fun _ _ => rfl
  rw [h3, h4] at h1
  rw [← cancel_mono (Scheme.ΓSpecIso _).inv, Category.assoc, h1, Scheme.ΓSpecIso_inv_naturality]

theorem kHom_eq {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (ι : X ⟶ PN k N) (hp : ι ≫ PNto k N = p)
    (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) (c : k) :
    kHom p c = X.presheaf.germ _ (genericPoint X) h ((ι.app _).hom ((Proj.awayToSection (A k N) (MvPolynomial.X i)).hom
      (HomogeneousLocalization.fromZeroRingHom _ _ (algebraMap k (A k N 0) c)))) := by
  subst hp
  have hC := constSecC (X_mem k N i) one_pos
  have e1 : kHom (ι ≫ PNto k N) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
      X.presheaf.germ _ (genericPoint X) h).hom := by
    rw [kHom, ← X.presheaf.germ_res (homOfLE (le_top : ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) ≤ ⊤)) _ h]
    rfl
  have e2 : (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
        ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e3 : (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap k (A k N 0)))).appTop ≫
        (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top :=
    Scheme.Hom.comp_appLE _ _ _ _ _
  have e4 : ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl = ι.app _ := Scheme.Hom.appLE_eq_app _
  have e5 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      CommRingCat.ofHom (algebraMap k (A k N 0)) ≫ (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫
        Proj.awayToSection (A k N) (MvPolynomial.X i)) ≫ ι.app _ := by
    rw [e2, e3, e4, ← hC]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (A k N 0)))
    simp only [Category.assoc] at n ⊢
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) n.symm).trans (by simp only [Category.assoc]))
  rw [e1, ← Category.assoc, e5]
  rfl

theorem eval₂_mul_pow {σ R L : Type} [CommSemiring R] [CommRing L] (F : R →+* L) (a b : σ → L) (t : L)
    (hab : ∀ j, a j * t = b j) {m : ℕ} {g : MvPolynomial σ R} (hg : g.IsHomogeneous m) :
    eval₂ F a g * t ^ m = eval₂ F b g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_eval₂Hom, map_sum, ← coe_eval₂Hom, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  rw [mul_assoc]
  congr 1
  have hm : m = ∑ j ∈ s.support, s j := by
    rw [← hd]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hm, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [← mul_pow, hab]

theorem mk_eq_eval (i : Fin (N + 1)) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)) :
    HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg =
      eval₂ ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0)))
        (fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) g := by
  apply HomogeneousLocalization.val_injective
  let vH : HomogeneousLocalization (A k N) (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) →+*
      Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) :=
    { toFun := fun y => y.val, map_one' := HomogeneousLocalization.val_one,
      map_mul' := HomogeneousLocalization.val_mul, map_zero' := HomogeneousLocalization.val_zero,
      map_add' := HomogeneousLocalization.val_add }
  change _ = vH _
  rw [eval₂_comp_left]
  have hgh : g.IsHomogeneous m := by simpa using (mem_homogeneousSubmodule _ _).1 hg
  set L := Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k))
  have hF : vH.comp ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0))) =
      (algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C := by
    ext c
    simp [vH, HomogeneousLocalization.fromZeroRingHom]
    rfl
  have hab : ∀ j, (vH ∘ fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) j *
      algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i) = algebraMap (MvPolynomial (Fin (N + 1)) k) L (X j) := by
    intro j
    simp only [Function.comp_apply, vH, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    simp only [pow_one]
    exact IsLocalization.mk'_spec _ _ _
  have key := eval₂_mul_pow ((algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C) _ _ _ hab hgh
  rw [hF, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change _ = _ * algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i ^ m)
  rw [map_pow, key]
  exact (congrArg _ (eval₂_eta g)).symm.trans (eval₂_comp_left _ _ _ _)

theorem GenAwayEval_of : GenAwayEval := by
  intro k _ X _ p N ι hp i h m g hg
  let φ : HomogeneousLocalization.Away (A k N) (MvPolynomial.X i) →+* X.functionField :=
    (X.presheaf.germ _ (genericPoint X) h).hom.comp
      ((ι.app _).hom.comp (Proj.awayToSection (A k N) (MvPolynomial.X i)).hom)
  have e : away ι (MvPolynomial.X i) (X_mem k N i) h m g hg =
      φ (HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg) := rfl
  rw [e, mk_eq_eval, eval₂_comp_left]
  congr 1
  ext c
  exact (kHom_eq p ι hp i h c).symm

end LateralTheory.EtaleTrace.Cov.GenInPf
end
end
