module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemMovedToAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteExtensionClassicalPointFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteExtensionClassicalPointFactors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TraitExtLab

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp S.R ⟶ F.X) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → ∃ (T' : Trait F) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : S.R →+* FractionRing T'.V) (e : T'.D.toPre.X ≃+ T.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₀ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.β a b = k * T.β (e a) (e b) := by
  intro g n F o Ω _ _ _ _ S u' p _ y₀ T ι hι hy
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  have hQ := GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl p T.V T.complete ι hι
  obtain ⟨W, _, _, _, hWc, _, fV, fK, κ, hfV, hfVl, -, hfK, hκι, hκ, hy₀⟩ :=
    GlobalTheory.T.exists_finite_extension_complete_dvr_padicAlgCl p T.V T.complete ι hι hQ S.R y₀
  have hbase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T', f, gK, hf, hfl, hff, hgK, hTy⟩ :=
    traitExtSt g n _ (zetaAway n) F W hbase inferInstance (spMap fK ≫ T.y)
  letI : Algebra (FractionRing W) (FractionRing T'.V) := gK.toAlgebra
  letI : Algebra W T'.V := f.toAlgebra
  haveI : Module.Finite W T'.V := hff
  haveI : Algebra.IsIntegral W T'.V := Algebra.IsIntegral.of_finite W T'.V
  haveI : IsLocalHom (algebraMap W T'.V) := hfl
  have hcomp : (algebraMap (FractionRing W) (FractionRing T'.V)).comp (algebraMap W (FractionRing W)) =
      (algebraMap T'.V (FractionRing T'.V)).comp (algebraMap W T'.V) := RingHom.ext hgK
  have hI : ∀ a : T'.V, _root_.IsIntegral (FractionRing W) (algebraMap T'.V (FractionRing T'.V) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap W (FractionRing W)) (algebraMap T'.V (FractionRing T'.V)) hcomp
      (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing W) (FractionRing T'.V) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T'.V) x
    rw [div_eq_mul_inv]
    exact (hI a).isAlgebraic.mul (hI b).isAlgebraic.inv⟩
  letI : Algebra (FractionRing W) (PadicAlgCl p) := κ.toAlgebra
  let ιA : FractionRing T'.V →ₐ[FractionRing W] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι' : FractionRing T'.V →+* PadicAlgCl p := ιA
  have hι'κ : ι'.comp gK = κ := ιA.comp_algebraMap
  have hint := GlobalTheory.unitBall_eq_of_integral_dvr p W T'.V hf κ ι' (fun v => by
    show ι' (algebraMap T'.V (FractionRing T'.V) (f v)) = _
    rw [← hgK]
    exact congrArg (fun h : FractionRing W →+* PadicAlgCl p => h (algebraMap W (FractionRing W) v)) hι'κ) hκ
  have hιc : ι'.comp (gK.comp fK) = ι := by rw [← RingHom.comp_assoc, hι'κ, hκι]

  have hr : ∀ a, y₀ a ∈ ι'.range := fun a => by
    obtain ⟨x, hx⟩ := hy₀ a
    exact ⟨gK x, by rw [← hx, ← hι'κ]; rfl⟩
  let eι : FractionRing T'.V ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b hab => ι'.injective (congrArg Subtype.val hab), ι'.rangeRestrict_surjective⟩
  let yK : S.R →+* FractionRing T'.V := eι.symm.toRingHom.comp (y₀.codRestrict ι'.range hr)
  have hyK : ι'.comp yK = y₀ := RingHom.ext fun a =>
    congrArg Subtype.val (eι.apply_symm_apply (y₀.codRestrict ι'.range hr a))

  have hne : f (fV T.ϖ) ≠ 0 := fun h => T.irr.ne_zero (hfV (hf (by rw [h, map_zero, map_zero])))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T'.irr
  have hbase' : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  haveI : IsLocalHom (f.comp fV) := by
    haveI : IsLocalHom f := hfl
    haveI : IsLocalHom fV := hfVl
    exact RingHom.isLocalHom_comp f fV
  obtain ⟨e₀, he₀⟩ := TraitUniq.traitUniq g n _ (zetaAway n) F T T' T'.V (f.comp fV) (RingHom.id _) (gK.comp fK)
    (RingHom.id _) hbase' inferInstance (hf.comp hfV) Function.injective_id inferInstance inferInstance
    (fun a => by simp only [RingHom.comp_apply, hfK, hgK]) (fun a => rfl)
    (by rw [hTy, spMap_comp', Category.assoc]; rw [show spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    T'.ϖ m 1 T'.irr hm (by rw [pow_one, RingHom.id_apply])
  refine ⟨T', ι', yK, e₀.symm, m, hint, hyK, ?_, ?_, ?_⟩
  · haveI : Epi (spMap ι') := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (spMap ι'), ← Category.assoc, ← spMap_comp', hyK, hy, hTy, ← hιc, spMap_comp', spMap_comp',
      Category.assoc, Category.assoc]
  · obtain ⟨u, hu⟩ := hm
    have hunit : ∀ w : T'.Vˣ, ‖ι' (algebraMap T'.V _ (w : T'.V))‖ = 1 := fun w => by
      have h1 := (hint _).2 ⟨(w : T'.V), rfl⟩
      have h2 := (hint _).2 ⟨((w⁻¹ : T'.Vˣ) : T'.V), rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (w : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (w : T'.V))),
        norm_nonneg (ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V)))]
    have e1 : ι (algebraMap T.V _ T.ϖ) = ι' (algebraMap T'.V _ (f (fV T.ϖ))) := by
      rw [← hιc, RingHom.comp_apply, RingHom.comp_apply, hfK, hgK]
    have e2 : f (fV T.ϖ) = T'.ϖ ^ m * ((u⁻¹ : T'.Vˣ) : T'.V) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e1, e2, map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]
  · intro a b
    have h := he₀ (e₀.symm a) (e₀.symm b)
    simp only [AddEquiv.apply_symm_apply, Nat.cast_one, one_mul] at h
    exact h.symm

end GlobalTheory.TraitExtLab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteExtensionClassicalPointFactorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_finiteExtension_classicalPoint_factors : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp S.R ⟶ F.X) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → ∃ (T' : Trait F) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : S.R →+* FractionRing T'.V) (e : T'.D.toPre.X ≃+ T.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₀ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.β a b = k * T.β (e a) (e b) := by
  first | exact @GlobalTheory.TraitExtLab.main | exact GlobalTheory.TraitExtLab.main | (intros; apply GlobalTheory.TraitExtLab.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DiagPull


open MonObj in
theorem isDiagEnd_pull {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A))
    (hS : IsDiagEnd F W P u ε) (hφ : IsGrpPullback P'.A P.A f φ) (hL : LBIso P'.L (P.L.pull φ))
    (hε' : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left) : IsDiagEnd F W P' (f ≫ u) ε' := by
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hε⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  refine ⟨c', hc'u, pr', hmon, huniv', ?_, fun E a => injψ ?_⟩
  swap
  · have e₁ : pushPt hφ.1.w (ε' E) = pushPt hφ.1.w (𝟙 P'.A) ≫ ε E := Over.OverMorphism.ext (by
      show (ε' E).left ≫ φ = ((𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ) ≫ (ε E).left
      rw [hε', Over.id_left, Category.id_comp])
    rw [push_comp, e₁, Category.assoc, hε]
    change diagPrecomp (M := c.A) (pushPt hφ.1.w (𝟙 P'.A)) _ = pushHom hψ _ _
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    refine (map_zpow (diagPrecomp (M := c.A) (pushPt hφ.1.w (𝟙 P'.A))) (pr b) (E a b)).trans
      (Eq.trans ?_ (map_zpow (pushHom hψ P'.A) (pr' b) (E a b)).symm)
    congr 1
    have e₂ := push_comp (𝟙 P'.A) b
    rw [Category.id_comp] at e₂
    exact e₂.symm
  let ε₀ : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c.P q ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε₀
  have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε₀
  have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε₀).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε₀
  have l3 : (LB.LinComb c'.P q' ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε₀
  have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε₀).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
  have i3 : LBIso ((LB.LinComb c.P q ε₀).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) :=
    LBIso.chartPull (chartPullOut c.P q ε₀ φ _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) (LB.LinComb (c.P.pull ψ₂) q' ε₀) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε₀ (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε₀) (LB.LinComb c'.P q' ε₀) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε₀
  have h1 := pull_isLB P.isLB φ
  have h2 := pull_isLB l0 φ
  exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

theorem exists_pull_field : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  intro g n F W R _ P ε u' hS K _ yK
  let A : PolAV (Sp K) := by
    open GlobalTheory GlobalTheory.Ex GlobalTheory.ModelData GlobalTheory.DegPull in
      exact {
        A := (Over.pullback (spMap yK)).obj P.A
        isAb := TLinPf.isAb_pullback (spMap yK) P.A P.isAb
        g := P.g
        smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
          (isGrpPullback_pullback P.A (spMap yK)).1 P.smoothDim
        L := P.L.pull (pullback.fst P.A.hom (spMap yK))
        isLB := pull_isLB P.isLB _
        rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A (spMap yK)) P.rigid
        sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A (spMap yK)) P.sym
        ample := by
          haveI := P.isAb.proper
          exact AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom (spMap yK))
        ktriv := by
          obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom (spMap yK)))
          exact kTriv_pull (isGrpPullback_pullback P.A (spMap yK)) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv }
  let φ : A.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap yK)
  have hφ : IsGrpPullback A.A P.A (spMap yK) φ := isGrpPullback_pullback P.A (spMap yK)
  have hL : LBIso A.L (P.L.pull φ) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ A.isLB
  have w : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = A.A.hom ≫ spMap yK := fun E => by
    rw [Category.assoc, Over.w, hφ.1.w]
  let εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A) := fun E =>
    Over.homMk (hφ.1.lift (φ ≫ (ε E).left) A.A.hom (w E)) (hφ.1.lift_snd _ _ _)
  have hεA : ∀ E, (εA E).left ≫ φ = φ ≫ (ε E).left := fun E => hφ.1.lift_fst _ _ _
  refine ⟨A, φ, hφ, hL, εA, isDiagEnd_pull F W P A u' (spMap yK) φ ε εA hS hφ hL hεA, fun Y x x' E h => ?_⟩
  refine Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  rw [h, Over.comp_left, Category.assoc, hεA]

end GlobalTheory.Poinc.DiagPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  first | exact @GlobalTheory.Poinc.DiagPull.exists_pull_field | exact GlobalTheory.Poinc.DiagPull.exists_pull_field | (intros; apply GlobalTheory.Poinc.DiagPull.exists_pull_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem traitLabels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW o Ω _ _ _ _ S ρ ε u' hD p _ y₀ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hβ⟩ := GlobalTheory.T.exists_trait_finiteExtension_classicalPoint_factors g n F o Ω S u' p y₀ T ι hι hsp
  obtain ⟨A, φ, cart, lb, εA, hDA, huniq⟩ := GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point g n F W S.R ρ.P ε u' hD (FractionRing T'.V) yK
  rw [hy'] at hDA
  obtain ⟨G', _, _, hsemi, D', U', j', hpsi, hcong⟩ := GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight g n F W hW T' A εA hDA
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p y₀ := { V := T'.V, complete := T'.complete, norm_le := hι', yK := yK, fac := hfac, A := A, φ := φ, cart := cart, lb := lb, G := G', semi := hsemi, D := D', U := U' }
  obtain ⟨l⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p y₀ u hint
  let jj : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X) := j'.trans (AddEquiv.piCongrRight fun _ => e)
  refine ⟨u, l, jj, ?_, ?_⟩
  · intro χ

    obtain ⟨v, hv⟩ := hpsi χ
    obtain ⟨jc, hjc, hval⟩ := GlobalTheory.T.psi_value_fractionRing_of_psiCoord T'.V D'.toPre χ _ hv
    have hq := l.q_eq χ jc hjc
    change ‖algebraMap (FractionRing T'.V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing T'.V))) _ ((D'.toPre.psi χ).s jc).val)‖ = _ at hq
    rw [hval, RingHom.algebraMap_toAlgebra] at hq

    have hunit : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ = 1 := by
      have h1 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h2 : ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (v : T'.V))), norm_nonneg (ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V)))]
    set a := ‖ι' (algebraMap T'.V _ T'.ϖ)‖ with ha
    have hq0 : 0 ≤ qW W T'.β (j' χ) :=
      qW_nonneg_of_posW W hW.1 T'.β T'.symm (GlobalTheory.Poinc.Basic₂.trait_nonneg T') (j' χ)
    have hsc : qW W T'.β (j' χ) = (k : ℤ) * qW W T.β (jj χ) := by
      simp only [qW, hβ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply]
      ring
    rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
    rw [← ha] at hq
    have hN : ((qW W T'.β (j' χ)).toNat : ℝ) = ((k : ℤ) : ℝ) * (qW W T.β (jj χ) : ℝ) := by
      rw [← Int.cast_mul, ← hsc]
      exact_mod_cast Int.toNat_of_nonneg hq0
    have hapos : 0 < a := by
      rw [ha, norm_pos_iff]
      intro h0
      have : algebraMap T'.V (FractionRing T'.V) T'.ϖ = 0 := ι'.injective (by rw [h0, map_zero])
      exact T'.irr.ne_zero (IsFractionRing.injective T'.V (FractionRing T'.V) (by rw [this, map_zero]))
    have hl : -l.q χ = ((qW W T'.β (j' χ)).toNat : ℝ) * Real.log a := by
      rw [← Real.log_pow, hq, Real.log_exp]
    rw [hϖ, Real.log_pow]
    rw [hN] at hl
    push_cast at hl ⊢
    linarith
  · intro m pk pk' x x' E hm h1 h2 hx
    have hc := hcong (PadicAlgCl p) m pk pk' x x' E hm h1 h2 (huniq _ x x' E hx)
    obtain ⟨w, hw⟩ := hc
    refine ⟨fun a => e (w a), ?_⟩
    funext a
    have := congrFun hw a
    simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply] at this ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_add (f := _), map_sum, map_nsmul]
    simp [map_zsmul]

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  first | exact @GlobalTheory.Poinc.traitLabels | exact GlobalTheory.Poinc.traitLabels | (intros; apply GlobalTheory.Poinc.traitLabels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemRechartAffineOpenAtClassicalTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemRechartAffineOpenAtClassicalTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.Poinc

theorem rechart_at_classical_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp R' ⟶ F.X), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ IsDiagEnd F W ρ'.P u' ε' ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) ∧ spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y ∧ ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  have h1 : X₁.π ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∈ Set.range i := by
    have e1 := congrArg (fun f : Sp (PadicAlgCl p) ⟶ Z => f (closedPoint (PadicAlgCl p))) c.comm
    simp only [Scheme.Hom.comp_apply] at e1
    exact ⟨_, by simp only [Scheme.Hom.comp_apply]; exact e1.symm⟩
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hU, hwU, -, hSame, hi₀, hdiag', hpt⟩ :=
    GlobalTheory.T.exists_thetaSystem_moved_to_affineOpen g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag _ h1
  set w := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X₁.M.ringOn U ≤ X₁.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ c.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X₁.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ c.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X₁.M.ringOn U, y₀ a = X₁.M.val (gPt p ≫ c.y) a := fun a => rfl

  let e : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z :=
    Spec.map (CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X₁.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X₁.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ c.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ c.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X₁.M.ringOn U).val.toRingHom ≫ e = X₁.M.pt := by
    refine ext_of_valR hU (he _).1 (X₁.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (X₁.M.ringOn U).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsSeparated X₁.z := X₁.isProper_compactificationMap.toIsSeparated
  have hgen2 : spMap (X₁.M.ringOn U).val.toRingHom ≫ (e ≫ X₁.π) =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (u' ≫ i) := by
    rw [← Category.assoc, hgen, X₁.comp, ← Category.assoc _ u' i, hpt, Category.assoc]
  have hb : e ≫ X₁.π = u' ≫ i :=
    ext_of_isDominant_of_isSeparated X₁.z
      (ext_of_isDominant (spMap (X₁.M.ringOn U).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (X₁.M.ringOn U).val.toRingHom) hgen2
  haveI := himm
  have hpt' : spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y := by
    rw [← cancel_mono i, Category.assoc, ← hb, ← Category.assoc, ha, Category.assoc, c.comm, Category.assoc]

  let τ := Spec.preimage (c.y ≫ X₁.M.s)
  have hσ : (gPt p ≫ c.y) ≫ X₁.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (c.y ≫ X₁.M.s), ← Spec.map_comp]; rfl
  refine ⟨c₀, hc, X₁.M.ringOn U, fg, frac, hth', hev, ρ', ε', u', hSame, hi₀, hle, hdiag', y₀, hy₀, hpt',
    fun a => ?_⟩
  rw [hy₀]
  show ‖X₁.M.val (gPt p ≫ c.y) (algebraMap X₁.o₁ X₁.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemRechartAffineOpenAtClassicalTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_rechart_affineOpen_at_classicalTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp R' ⟶ F.X), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ IsDiagEnd F W ρ'.P u' ε' ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) ∧ spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y ∧ ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := by
  first | exact @GlobalTheory.Poinc.rechart_at_classical_trait | exact GlobalTheory.Poinc.rechart_at_classical_trait | (intros; apply GlobalTheory.Poinc.rechart_at_classical_trait <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_isLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X), IsLab X₁ ε₁ c yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', u', hsame, hi₀, hle, hdiag', y₀, hy₀, hpt, hint⟩ :=
    GlobalTheory.T.thetaSystem_rechart_affineOpen_at_classicalTrait g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p z₁ c
  obtain ⟨u, l, j, hq, hcong⟩ :=
    GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait g n F W he8 X₁.o₁ X₁.Ω₁ _ ρ' ε' u' hdiag' p y₀ c.T c.ι c.int hpt hint
  let jm : ModN (X₁.S.r * X₁.S.N) u.D.toPre.X →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X) :=
    QuotientAddGroup.map _ _ j.toAddMonoidHom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, by simp⟩)
  refine ⟨jm.comp l.yy, c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame, hi₀, hle, y₀, hy₀, u, l, j, hq, ?_, hcong⟩
  intro a χ ha
  simp only [AddMonoidHom.comp_apply, ha, jm]
  rfl

end GlobalTheory.Poinc
