module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsTauCoord

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R]

def baseK (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] : TFK (R := R) F ⟶ TFK (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F
    rw [jFK, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

variable (A : PolAV (Sp (FractionRing R)))

def secBase (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left

abbrev SecF (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) : Type :=
  SecOver (secBase A F) (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (N : ℤ)))

variable (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F]
    [IsScalarTower (FractionRing R) E F]

def secMap : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) E ⊗ A.A := lift (fst _ _ ≫ baseK E F) (snd _ _)

theorem secMap_snd : secMap A E F ≫ snd _ _ = snd _ _ := lift_snd _ _

theorem secMap_fst : secMap A E F ≫ fst _ _ = fst _ _ ≫ baseK E F := lift_fst _ _

theorem secMap_base : (secMap A E F).left ≫ secBase A E =
    secBase A F ≫ Spec.map (CommRingCat.ofHom (algebraMap E F)) :=
  congrArg (fun q => q.left) (secMap_fst A E F)

def secPull (N : ℕ) : SecF A E N →ₛₗ[algebraMap E F] SecF A F N :=
  pullOver A.L _ (secMap_base A E F) (fun _ => (congrArg (fun q => q.left) (secMap_snd A E F)).symm)

theorem isPullback_secMap : IsPullback (secMap A E F).left (secBase A F) (secBase A E)
    (Spec.map (CommRingCat.ofHom (algebraMap E F))) := by
  have h₁ : IsPullback (snd (TFK (R := R) E) A.A).left (secBase A E)
      A.A.hom (TFK (R := R) E).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TFK (R := R) F) A.A).left (secBase A F)
      A.A.hom (TFK (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (secMap_base A E F) h₁
  have e₁ : (secMap A E F).left ≫ (snd (TFK (R := R) E) A.A).left =
      (snd (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (secMap_snd A E F)
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫
      (TFK (R := R) E).hom = (TFK (R := R) F).hom := Over.w (baseK (R := R) E F)
  rw [e₁, e₂]
  exact h₂

instance noeth : TopologicalSpace.NoetherianSpace (TFK (R := R) E ⊗ A.A).left := by
  have := A.isAb.proper
  have : IsProper (secBase A E) := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (TFK (R := R) E ⊗ A.A).left := LocallyOfFiniteType.isLocallyNoetherian (secBase A E)
  have : CompactSpace (TFK (R := R) E ⊗ A.A).left := QuasiCompact.compactSpace_of_compactSpace (secBase A E)
  have : IsNoetherian (TFK (R := R) E ⊗ A.A).left := {}
  infer_instance

theorem isExtension_secPull (N : ℕ) : IsExtension (secPull A E F N) :=
  isExtension_pullOver (isPullback_secMap A E F) A.isLB _ _

end GlobalTheory.Mum.UpExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.FieldBaseChange

def basisOfIsExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) : Module.Basis I F W :=
  Module.Basis.mk (GlobalTheory.ConstFam.linearIndependent_of_isExtension ha B.linearIndependent) (by
    have h : Submodule.span K (Set.range B) ≤
        Submodule.comap a (Submodule.span F (Set.range fun i => a (B i))) :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [← ha.span, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range B) := B.span_eq ▸ Submodule.mem_top
    exact h hv)

theorem basisOfIsExtension_apply {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) (i : I) : basisOfIsExtension ha B i = a (B i) := by
  simp [basisOfIsExtension]

theorem exists_bijective_extension : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  intro K F V V' W W' _ _ _ _ _ _ _ _ _ _ _ a d ha hd e he
  let B := Module.Basis.ofVectorSpace K V
  let B' := B.map (LinearEquiv.ofBijective e he)
  let C := basisOfIsExtension ha B
  let C' := basisOfIsExtension hd B'
  let E := C.equiv C' (Equiv.refl _)
  refine ⟨E.toLinearMap, E.bijective, fun v => ?_⟩
  have key : (E.toLinearMap.comp a : V →ₛₗ[algebraMap K F] W') = d.comp e := B.ext fun i => by
    have h1 : a (B i) = C i := (basisOfIsExtension_apply ha B i).symm
    have h2 : d (e (B i)) = C' i := by
      rw [basisOfIsExtension_apply hd B' i]; simp [B']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, h2, E, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun key v

end GlobalTheory.FieldBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_bijective_extension | exact GlobalTheory.FieldBaseChange.exists_bijective_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_bijective_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbac
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbac
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.UpExt

theorem over_famPull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  intro R _ _ I D k F₀ E F _ _ _ _ _ _ s h α
  have hL := D.P.isLB
  have g1 : ∀ {W : Scheme.{0}} (w : W), gs (𝟙 W) w ⊤ (1 : Γ(W, ⊤)) = 1 := fun w => by
    rw [gs_eq _ w ⊤ trivial, map_one, map_one]
  have h1 := (secScal_iff_val hL _ _ _ _).1 (h α)
  refine (secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  have e1 : (𝟙 _ ≫ (DegPre.prB D F).left) = (famMap D E F).left ≫ (𝟙 _ ≫ (DegPre.prB D E).left) := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, famMap_snd]
  have e2 : (𝟙 _ ≫ (famMap D E F).left) = (famMap D E F).left ≫ 𝟙 _ := by
    rw [Category.id_comp, Category.comp_id]
  change _ = _ * sval (termPull D E F k α (s.s α)) _ y J
  rw [g1, _root_.one_mul, show sval (termPull D E F k α (s.s α)) (𝟙 _) y J =
      sval (s.s α) (𝟙 _ ≫ (famMap D E F).left) y J from sval_pullOver _ _ _ _ hJ, e1, e2, GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ,
    GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ, h1 _ _ (fun ψ => hJ _), g1, _root_.one_mul]

end GlobalTheory.Mum.UpExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbacStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  first | exact @GlobalTheory.Mum.UpExt.over_famPull | exact GlobalTheory.Mum.UpExt.over_famPull | (intros; apply GlobalTheory.Mum.UpExt.over_famPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpExt

theorem torsion_from_closure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  intro R _ _ A F _ _ _ em N hN x hx
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp (FractionRing R)) A.A A.isAb N hN).1
  let i : K' →ₐ[FractionRing R] Kb R := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let : Algebra K' (Kb R) := i.toRingHom.toAlgebra
  have : IsScalarTower (FractionRing R) K' (Kb R) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hmul : x ≫ mulN A.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  let t0 : _ ⟶ torsion A.A N := pullback.lift x (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A N = x := pullback.lift_fst _ _ _
  have hs : (TFK (R := R) F).hom = spMap (em.toRingHom.comp (algebraMap (FractionRing R) (Kb R))) :=
    congrArg spMap em.comp_algebraMap.symm
  obtain ⟨w, hw⟩ := H (Kb R) F em.toRingHom t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A N).hom = (TFK (R := R) (Kb R)).hom := by
    have : Surjective (spMap em.toRingHom) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
    have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
    apply (cancel_epi (spMap em.toRingHom)).1
    rw [← Category.assoc, hw, Over.w t0, hs, ← spMap_comp_spMap]
    rfl
  let w1 : TFK (R := R) (Kb R) ⟶ torsion A.A N := Over.homMk w hw2
  refine ⟨w1 ≫ torsion.ι A.A N, ?_, ?_⟩
  · have hc : torsion.ι A.A N ≫ mulN A.A N = toUnit _ ≫ η :=
      pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    have h1 : (w1 ≫ torsion.ι A.A N) ≫ mulN A.A N = toUnit _ ≫ η := by
      rw [Category.assoc, hc, ← Category.assoc, comp_toUnit]
    rwa [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, ← Hom.one_def] at h1
  · rw [← ht0, Over.comp_left, ← hw, Category.assoc]
    rfl

end GlobalTheory.Mum.UpExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  first | exact @GlobalTheory.Mum.UpExt.torsion_from_closure | exact GlobalTheory.Mum.UpExt.torsion_from_closure | (intros; apply GlobalTheory.Mum.UpExt.torsion_from_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpAct
open GlobalTheory.UT GlobalTheory.ThetaScalar

variable {R : Type} [CommRing R] [IsDomain R] {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E]
  [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem exists_frame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : w.IsGen) :
    ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J := by
  obtain ⟨hy, hb, hs⟩ := h
  have h0 : (baseMap (R := R) E F).left ≫ (DegPre.zeroF D E).left = (DegPre.zeroF D F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (baseMap (R := R) E F))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F p'.g.b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.P.L _ _ w (baseMap (R := R) E F).left) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem txFrame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : TXFrame k p w) {w' : Frm D F k p'.g.b} (hw' : w'.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) : TXFrame k p' w' := by
  obtain ⟨hy, hb, hs⟩ := h
  have hL := D.P.isLB
  have hb' : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ p.g.b.left = p'.g.b.left := by
    rw [Category.id_comp]; exact hb.symm
  refine ⟨hw', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have c : LB.Gen.Corr D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w 2)
        (LB.mulGen D.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.P.L _ _ ν p.g.b.left)) :=
      corr_of_val hL fun y I hI => (map_pow _ _ _).trans ((hw.2.1 ν hν y I hI).trans (by
        rw [val_mul hI, val_pull hI, Category.id_comp]))
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    rw [val_mul hJ, val_pull hJ, hb'] at e
    rw [hv _ _ z J hJ, val_corr hJ (hs p'.y), val_pull hJ, hy]
    exact (map_pow _ _ _).symm.trans e
  · have c : LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w k) (LB.pullGen D.P.L _ _ κ p.g.b.left))
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi p.y) (jFK (R := R) E))
          (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (TF (R := R) E).hom)) :=
      corr_of_val hL fun y I hI => by
        rw [val_mul hI, val_mul hI, val_pull hI, val_pull hI, val_pull hI, Category.id_comp, Category.id_comp,
          Category.id_comp]
        exact (congrArg (· * _) (map_pow _ _ _)).trans (hw.2.2 κ hκ y I hI)
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    have e₁ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ jFK (R := R) E = jFK (R := R) F := by
      rw [Category.id_comp]; exact specMap_jFK E F
    have e₂ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ (TF (R := R) E).hom = (TF (R := R) F).hom := by
      rw [Category.id_comp]; exact Over.w _
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb', e₁, e₂] at e
    rw [hv _ _ z J hJ, hy]
    exact (congrArg (· * _) (map_pow _ _ _)).symm.trans e

theorem phiVal_pull (hG : GlobalFnsSt) {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} {w' : Frm D F k p'.g.b}
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) (s t : Fam D E k) (H : PhiVal p w s.s t.s) :
    PhiVal p' w' (famPull D E F hG k s).s (famPull D E F hG k t).s := by
  obtain ⟨hy, hb, hs⟩ := h
  have hb' : p'.g.b = baseMap (R := R) E F ≫ p.g.b := Over.OverMorphism.ext hb
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D F p'.g.b ≫ famMap D E F = famMap D E F ≫ DegPre.trPt D E p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D E F)).trans (tr_pr D F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D E _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D E F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) E F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D E k α p.g.b (ρ ≫ famMap D E F) z J = uVal D F k α p'.g.b ρ z J := by
    have : famMap D E F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D E F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, hv _ _ z J hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

theorem secMap_eq (A : PolAV (Sp (FractionRing R))) : secMap A E F = baseK (R := R) E F ▷ A.A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [secMap_fst, whiskerRight_fst]
  · rw [secMap_snd, whiskerRight_snd]

theorem actVal_secPull {A : PolAV (Sp (FractionRing R))} {N : ℕ} (hN : Odd N) {x : TFK (R := R) E ⟶ A.A}
    {θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) E)} {θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)}
    (H : SymLift A.A A.L N N x θ) (H' : SymLift A.A A.L N N (baseK (R := R) E F ≫ x) θ')
    {t u : SecF A E N} (h : ActVal θ t u) : ActVal θ' (UpExt.secPull A E F N t) (UpExt.secPull A E F N u) := by
  obtain ⟨ξ, Hξ, v⟩ := SymLiftGlobal.exists_symLift_pull_val A.isLB (baseK (R := R) E F) H
  have c := SymLiftOdd.symLift_unique GlobalTheory.globalFns_holds A.isAb A.isLB hN θ' ξ H' Hξ
  intro Z r z J hJ
  have h₂ : thetaVal θ' r z J = thetaVal θ (r ≫ (secMap A E F).left) z J := by
    rw [secMap_eq]; exact (val_corr hJ c _).trans (v _ _ z J hJ)
  refine (sval_pullOver _ _ _ _ hJ).trans ((h _ _ z J hJ).trans (congrArg₂ (· * ·)
    (congrArg Units.val h₂.symm) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm)))
  have e : (translT A.A θ'.pt).left ≫ (secMap A E F).left = (secMap A E F).left ≫ (translT A.A θ.pt).left := by
    rw [H'.pt_eq, H.pt_eq, secMap_eq]
    exact congrArg (fun q => q.left) (CommPairing.whisker_translT (baseK (R := R) E F) x)
  rw [Category.assoc, Category.assoc, e]
  rfl

end GlobalTheory.Mum.UpAct


open GlobalTheory.Mum.UpAct GlobalTheory.UT GlobalTheory.ThetaScalar in
theorem GlobalTheory.Mum.UpAct.act_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = UpExt.secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  intro R _ _ _ hR D A N hN lab E₀ hE F _ _ _ _ _ lab' hlab E' hE' p w θ s s' hw hθ hs
  have : CharZero R := hR.2
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨p₀, hp, -⟩ := (qkPt_algClosure_bijective R D.toPre F
    (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) N hN.pos).2 p
  have hx : lab' p = baseK (R := R) (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp)
  replace hp : QkExt (algebraMap (Kb R) F) p₀ p := hp
  obtain ⟨w₀, hw₀⟩ := hE.frame p₀
  obtain ⟨θ₀, hθ₀⟩ := hE.lift p₀
  obtain ⟨w', hw', hv'⟩ := exists_frame_pull hp hw₀.1
  have hu := (GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R _ hR.1 D F N hN p).2 w w' hw (txFrame_pull hp hw₀ hw' hv')
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.toPre.P.L z J →
      val w r z J = val w₀ (r ≫ (baseMap (R := R) (Kb R) F).left) z J := fun Z r z J hJ =>
    (val_corr hJ (corr_of_val D.toPre.P.isLB hu) r).trans (hv' Z r z J hJ)
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of_globalFns hG R _ D (Kb R) N hN.pos p₀ w₀ hw₀.1
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R _ D F N hN.pos p w hw.1
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : SecF A F N →ₗ[F] SecF A F N, ∀ t, ActVal θ t (Θ t) := GlobalTheory.TorsionExt.exists_act θ
  rw [hx] at hθ
  have key : E' ∘ₗ Φ = Θ ∘ₗ E' := LinearMap.ext_on
    (isExtension_famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds hN.pos).span (by
      rintro _ ⟨u, rfl⟩
      have r₀ : PhiRel D.toPre (Kb R) N p₀ w₀ u (Φ₀ u) := (hΦ₀ u _).2 rfl
      have r := (hΦ _ _).1 ((phiRel_iff hG p w hw.1 _ _).2
        (phiVal_pull GlobalTheory.globalFns_holds hp hv u _ ((phiRel_iff hG p₀ w₀ hw₀.1 _ _).1 r₀)))
      have a := actVal_secPull hN hθ₀ hθ (ThetaBaseChange.actVal_of_isActOf (hE.act p₀ w₀ θ₀ u _ hw₀ hθ₀ r₀))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← r, hE', hE']
      exact GlobalTheory.TorsionExt.actVal_unique a (hΘ _))
  obtain rfl := (hΦ _ _).1 hs
  have e : E' (Φ s) = Θ (E' s) := LinearMap.congr_fun key s
  rw [e]
  exact (hΘ _).isActOf A.isLB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_linearExtension_to_algClosedField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  first | exact @GlobalTheory.Mum.UpAct.act_extension | exact GlobalTheory.Mum.UpAct.act_extension | (intros; apply GlobalTheory.Mum.UpAct.act_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  intro R _ _ _ hR D A N hN lab E₀ Φ hE hΦ F _ _ _ em lab' hlab
  have hN1 : 1 ≤ N := hN.pos
  haveI : CharZero R := hR.2
  letI : Algebra (Kb R) F := em.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
  have hem : IsScalarTower.toAlgHom (FractionRing R) (Kb R) F = em := AlgHom.ext fun _ => rfl
  let e : Fam D.toPre (Kb R) N →ₗ[Kb R] SecF A (Kb R) N :=
    { toFun := E₀
      map_add' := fun s t => SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecOver.ext _ _ fun j => hE.smul c s (c • s) ((isSmul_iff _ _ _).2 rfl) j }
  obtain ⟨e', he', hc⟩ := GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange _ _ _ _ _ _ (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N) (secPull A (Kb R) F N)
    (isExtension_famPull _ _ _ GlobalTheory.globalFns_holds hN1) (isExtension_secPull A (Kb R) F N) e hE.bij
  have hq := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1
  have onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure R A F em N hN1 x hx
      obtain ⟨p₀, hp₀⟩ := (hE.onto y).1 hy
      obtain ⟨p', hp', -⟩ := hq.1 p₀
      refine ⟨p', Over.OverMorphism.ext ?_⟩
      rw [hlab p₀ p' hp', hp₀, hxy]
    · rintro ⟨p, rfl⟩
      obtain ⟨p₀, hp₀, -⟩ := hq.2 p
      have hy := (hE.onto (lab p₀)).2 ⟨p₀, rfl⟩
      have e1 : lab' p = baseK (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp₀)
      rw [e1, ← MonObj.comp_pow, hy, MonObj.comp_one]
  refine ⟨fun s => e' s, ⟨he', fun s s' s'' h j => ?_, fun c s s' h j => ?_, onto,
    fun p => ((GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hR.1 D F N hN p).1),
    fun p => GlobalTheory.SymFrameClause.exists_symLift R A F N hN (lab' p) ((onto _).2 ⟨p, rfl⟩),
    fun p w θ s s' hw hθ hs => GlobalTheory.T.equivariant_linearExtension_to_algClosedField R hR D A N hN lab E₀ hE F lab' (hem ▸ hlab) e' hc p w θ s s' hw hθ hs⟩, ?_⟩
  · obtain rfl : s'' = s + s' := fam_ext h
    rw [map_add (f := _)]
    rfl
  · obtain rfl : s' = c • s := (isSmul_iff _ _ _).1 h
    rw [map_smul]
    rfl
  · intro F₀ s hs
    obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
    have h1 := GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback R (maximalIdeal R) D.toPre N F₀ (Kb R) F s₀ hs₀
    obtain rfl := (GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ F).unique hs h1
    intro Z p p' hpp z J hJ
    show sval (e' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s₀)) p z J = _
    rw [hc]
    refine (sval_pullOver _ _ _ _ hJ).trans (hΦ F₀ s₀ hs₀ Z (p ≫ (secMap A (Kb R) F).left) p' ?_ z J hJ)
    rw [Category.assoc, ← hpp]
    exact congrArg (p ≫ ·) (congrArg (fun q => q.left) (secMap_snd A (Kb R) F))
end GlobalTheory.Mum.UpExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_bijection_larger_closed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  first | exact @GlobalTheory.Mum.UpExt.exists_eqv_ext | exact GlobalTheory.Mum.UpExt.exists_eqv_ext | (intros; apply GlobalTheory.Mum.UpExt.exists_eqv_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFamilyExpansionEqConstMulAlgClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_liftFun_top {S0 : Scheme.{0}} (A : Over S0) {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤))
    {Z : Scheme.{0}} (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem fvalue_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  intro R _ _ _ hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W _ _ _ T F _ _ _ _ em hem
  obtain ⟨lab, E, hlab, hE, hT⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W T F em hem
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hAg⟩ := GlobalTheory.T.exists_equivariant_bijection_larger_closed_field R hR D C.A (C.n ^ j) hodd (C.lab j) E₀ Φ₀ hE₀ hΦ₀ F em lab hlab
  haveI : CharZero R := hR.2
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.Mum.eqv_eq_smul R (maximalIdeal R) D C.A F (C.n ^ j) hodd lab E E' hE hE'
  refine ⟨(c₀ : F)⁻¹, inv_ne_zero c₀.ne_zero, ?_⟩
  intro F₀ σ hσ Z p p' h1 h2 z J hJ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre (C.n ^ j) F₀ F
  obtain ⟨J', hJ', -⟩ := exists_good C.A.L C.A.isLB z (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun a => a.elim) (fun k => k.elim)
  set q := p' ≫ (snd (TFK (R := R) F) C.A.A).left with hq
  have e1 := hT F₀ s σ hs hσ Z p p' h1 h2 z J J' hJ hJ'
  have e2 : sval (E' s) p' z J' = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) * sval (E s) p' z J' := by
    unfold sval
    refine (congrArg (gs p' z _) (hc₀ s _)).trans ?_
    exact (gs_mul p' z _ (hJ'.mem _ p') _ _).trans (congrArg (· * _) (gs_liftFun_top _ _ _ _ _ (hJ'.mem _ p')))
  have e3 := hAg F₀ s hs Z p' q (Category.comp_id _).symm z J' hJ'
  have e4 := hΦ F₀ Z q z J J' hJ hJ'
  have hβ : J (q ≫ C.α) = J (p ≫ T.β) := by rw [h1, hq, Category.assoc]
  rw [hβ] at e4
  have huv : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)⁻¹) *
      gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) = 1 := by
    rw [← gs_mul (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ c₀.ne_zero,
      map_one, gs_eq (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, map_one, map_one]
  rw [e1, e4, ← e3, e2]
  linear_combination (-(gw wA q z (J (p ≫ T.β)) (J' q) ^ (C.n ^ j)).val * sval (E s) p' z J') * huv

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFamilyExpansionEqConstMulAlgClosureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  first | exact @GlobalTheory.Mum.fvalue_const | exact GlobalTheory.Mum.fvalue_const | (intros; apply GlobalTheory.Mum.fvalue_const <;> assumption)
end
