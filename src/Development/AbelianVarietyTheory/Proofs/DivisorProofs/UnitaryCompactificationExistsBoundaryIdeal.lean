module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSetupIdealOverComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImageStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionMulRamificationIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionMulRamificationIndex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.UTraitRam

theorem evalZ_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → φ.evalZ T'.be = m * φ.evalZ T.be := by
  intro E _ _ _ H Dw l Xo c _ T T' f fK hf hl hK hy m hm φ hφ
  obtain ⟨hdvr, hcpl, hz⟩ := T'.cdvr
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hz⟩
  have hself : Associated (RingHom.id T'.V T'.ϖ) (T'.ϖ ^ 1) := by simp [Associated.refl]
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices E H Dw l Xo c T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB hdvr hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    hself
  have hon : IsPolFanOn H.bar φ T.P.D.toPre.X := by
    haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
    exact hφ _ (GlobalTheory.UPoinc.UTrait.finrank_le_min E H Dw l Xo c T)
  have hc : toReal T.be ∈ psdCone (bar := H.bar) (X := T.P.D.toPre.X) :=
    GlobalTheory.PolFan.StrictData.toReal_mem_psdCone ((balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev)
      fun y => by simpa using T.mono.nonneg 0 y
  rw [← evalR_toReal φ T.be, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.UPoinc.UTraitRam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionMulRamificationIndexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationFunction_mul_ramificationIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → φ.evalZ T'.be = m * φ.evalZ T.be := by
  first | exact @GlobalTheory.UPoinc.UTraitRam.evalZ_eq_mul | exact GlobalTheory.UPoinc.UTraitRam.evalZ_eq_mul | (intros; apply GlobalTheory.UPoinc.UTraitRam.evalZ_eq_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryNormDescentIdealToComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryNormDescentIdealToComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UNormDown

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (k : ℕ) (J : C.Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ ∀ (T : UTrait Xo c) (ξ₁ : Sp T.V ⟶ X₁.M.Z), T.y ≫ C.i = jK T.V ≫ ξ₁ ≫ X₁.π → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm X₁ ι J₁ hι hπ hsupp hv
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z C.Z X₁.π X₁.fin inferInstance hLN X₁.normal C.normal
    (by rw [hπ]; exact hAc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff T.V).1 T.cdvr
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V hcpl (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π := by
    intro χ hχ
    have e1 : jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ (χ ≫ X₁.π) := by
      simp only [Category.assoc]
    have e2 : (jK V' ≫ spMap f) ≫ ξ₁ ≫ X₁.π = spMap fK ≫ T.y ≫ C.i := by
      rw [jK_spMap f fK hfK, Category.assoc, hgen]
    rw [e1, hχ, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'), e2, hy₂]
    simp only [Category.assoc]
  have hord : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T₂.be ∧ idlAlong J₁ (spMap f₂ ≫ χ) = Ideal.span {T₂.ϖ ^ a} := by
    intro χ hχ
    obtain ⟨tK, h1, h2⟩ := T₂.gen
    exact hv T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ χ) T₂.y (hover χ hχ) trivial T₂.t tK h1 h2 T₂.P T₂.be T₂.lev
      T₂.mono
  obtain ⟨a₀, ha₀, h₀⟩ := hord (spMap f ≫ ξ₁) (Category.assoc _ _ _)
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord (ψ j) (hψ j)
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  have idlAlong_eq_map_local {X : Scheme.{0}} (I : X.IdealSheafData) {R : Type}
      [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X) (U : X.affineOpens)
      (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong I χ = (I.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    have hx : χ (closedPoint R) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map I U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have idlAlong_comp_local {X : Scheme.{0}} (I : X.IdealSheafData) {R S : Type}
      [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
      (χ : Sp R ⟶ X) (g : R →+* S) : idlAlong I (spMap g ≫ χ) = (idlAlong I χ).map g := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap g ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap g x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [idlAlong_eq_map_local I χ ⟨U, hU⟩ hle, idlAlong_eq_map_local I _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap g ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap g).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  apply GlobalTheory.TraitOrder.map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← idlAlong_comp_local, hcomp, Category.assoc, h₀, hmp]
  simp only [← idlAlong_comp_local, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.UPoinc.UNormDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryNormDescentIdealToComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_normDescent_ideal_to_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (k : ℕ) (J : C.Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ ∀ (T : UTrait Xo c) (ξ₁ : Sp T.V ⟶ X₁.M.Z), T.y ≫ C.i = jK T.V ≫ ξ₁ ≫ X₁.π → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  first | exact @GlobalTheory.UPoinc.UNormDown.normDescent | exact GlobalTheory.UPoinc.UNormDown.normDescent | (intros; apply GlobalTheory.UPoinc.UNormDown.normDescent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLiftsToThetaSetupModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLiftsToThetaSetupModel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc


open GlobalTheory.Poinc.TraitLift in
theorem exists_uTrait_lift_setup (hExt : UTraitExtSt) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π := by
  intro E _ _ _ H Dw l Xo c C X₁ hcl T ξ hξ hc
  haveI : IsFinite X₁.π := X₁.fin
  obtain ⟨hdvr, hcpl, hch⟩ := T.cdvr
  haveI := hdvr
  haveI := hcpl
  haveI := hch
  have hgen : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ Set.range X₁.π :=
    mem_of_closedPoint _ hcl.isOpen T.V ξ hc _
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point X₁.π (FractionRing T.V) (jK T.V ≫ ξ) hgen
  obtain ⟨V₂, _, _, _, j, e, hB, hD, hj, hjl, he⟩ := exists_closure T.V L
  have hring : (algebraMap V₂ (FractionRing V₂)).comp j =
      (e.comp (algebraMap (FractionRing T.V) L)).comp (algebraMap T.V (FractionRing T.V)) :=
    RingHom.ext fun a => (he a).symm
  haveI : ValuationRing V₂ := inferInstance
  have hsq : (spMap e ≫ η) ≫ X₁.π = jK V₂ ≫ (spMap j ≫ ξ) := by
    rw [Category.assoc, hη, ← Category.assoc, spMap_comp', ← Category.assoc, ← Category.assoc, spMap_comp',
      show jK V₂ = spMap (algebraMap V₂ (FractionRing V₂)) from rfl, spMap_comp', hring]
  obtain ⟨l₁, hl1, -⟩ := exists_lift_of_isFinite X₁.π V₂ (spMap e ≫ η) (spMap j ≫ ξ) hsq
  obtain ⟨T', f'', fK'', hinj'', hloc'', -, hc'', hy''⟩ := hExt E H Dw l Xo c V₂ hB hD
    (spMap (e.comp (algebraMap (FractionRing T.V) L)) ≫ T.y)
  have hring2 : (algebraMap T'.V (FractionRing T'.V)).comp (f''.comp j) =
      (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))).comp (algebraMap T.V (FractionRing T.V)) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [← hc'', ← he]
  have key : jK T'.V ≫ spMap (f''.comp j) = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V := by
    rw [show jK T'.V = spMap (algebraMap T'.V (FractionRing T'.V)) from rfl,
      show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl, spMap_comp', spMap_comp', hring2]
  haveI := hloc''
  refine ⟨T', f''.comp j, fK''.comp (e.comp (algebraMap (FractionRing T.V) L)), spMap f'' ≫ l₁, hinj''.comp hj,
    inferInstance, fun a => (RingHom.congr_fun hring2 a).symm, ?_, ?_, ?_⟩
  · rw [hy'', ← Category.assoc, spMap_comp']
  · rw [Category.assoc, hl1, ← Category.assoc, spMap_comp']
  · symm
    calc jK T'.V ≫ (spMap f'' ≫ l₁) ≫ X₁.π = jK T'.V ≫ spMap (f''.comp j) ≫ ξ := by
          rw [Category.assoc, hl1, ← spMap_comp', Category.assoc]
      _ = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V ≫ ξ := by
          rw [← Category.assoc, key, Category.assoc]
      _ = T'.y ≫ C.i := by
          rw [← hξ, hy'', ← spMap_comp']
          simp only [Category.assoc]

theorem uTraitLift_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π :=
  exists_uTrait_lift_setup GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLiftsToThetaSetupModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTrait_lifts_to_thetaSetup_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π := by
  first | exact @GlobalTheory.UPoinc.uTraitLift_setup | exact GlobalTheory.UPoinc.uTraitLift_setup | (intros; apply GlobalTheory.UPoinc.uTraitLift_setup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoincDown

theorem exists_assoc_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {ϖ : V} (hϖ : Irreducible ϖ)
    {ϖ' : V'} (hϖ' : Irreducible ϖ') : ∃ m : ℕ, 1 ≤ m ∧ Associated (f ϖ) (ϖ' ^ m) := by
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ'
  refine ⟨m, Nat.one_le_iff_ne_zero.2 fun e => ?_, hm⟩
  subst e
  rw [pow_zero] at hm
  exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hm))

theorem map_eq_span_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) {ϖ' : V'} (hϖ' : Irreducible ϖ') {m : ℕ}
    (hm : Associated (f ϖ) (ϖ' ^ m)) {I : Ideal V} {b : ℕ} (h : I.map f = Ideal.span {ϖ' ^ b}) :
    ∃ a : ℕ, b = m * a ∧ I = Ideal.span {ϖ ^ a} := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact pow_ne_zero _ hϖ'.ne_zero h
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨a, ?_, rfl⟩
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton] at h
  have h2 : Associated (ϖ' ^ (m * a)) (ϖ' ^ b) := by
    rw [pow_mul]; exact (hm.pow_pow (n := a)).symm.trans h
  have e1 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.dvd
  have e2 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.symm.dvd
  omega

theorem idealDescent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) A φ J d := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAn X₁ ι J₁ hι hπ hsupp hord
  obtain ⟨k, J, hk, hJs, hJo⟩ := GlobalTheory.T.unitary_normDescent_ideal_to_component E H Dw hpq φ hφ l Xo c C A hAc hAi hAn X₁ ι J₁ hι hπ hsupp hord
  refine ⟨k * ι, J, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hJs, ?_⟩
  intro W _ _ _ hW ϖ hϖ χ y hy hA t tK h1 h2 P be hbe hmono
  let T : UTrait Xo c := { V := W, cdvr := hW, ϖ := ϖ, irr := hϖ, y := y, t := t, gen := ⟨tK, h1, h2⟩, P := P, be := be, lev := hbe, mono := hmono }
  have hy' : T.y ≫ C.i = jK T.V ≫ χ := by simpa using hy
  have hc : IsClopen (Set.range X₁.π) := by rw [hπ]; exact hAc
  obtain ⟨T', f, fK, ξ₁, hf, hfl, hfK, hyy, hsq, hgen⟩ := GlobalTheory.T.unitaryTrait_lifts_to_thetaSetup_model E H Dw l Xo c C X₁ hc T χ hy' (by rw [hπ]; exact hA)
  obtain ⟨tK', g1, g2⟩ := T'.gen
  obtain ⟨a₁, ha₁, hJ₁⟩ := hord T'.V T'.cdvr T'.ϖ T'.irr ξ₁ T'.y hgen trivial T'.t tK' g1 g2 T'.P T'.be T'.lev T'.mono
  have hJ := hJo T' ξ₁ hgen
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  obtain ⟨m, hm1, hm⟩ := exists_assoc_pow f hf T.irr T'.irr
  have hφ' := GlobalTheory.T.polarisationFunction_mul_ramificationIndex E H Dw l Xo c hpq T T' f fK hf hfl hfK hyy m hm φ hφ
  have e1 : (idlAlong J χ).map f = Ideal.span {T'.ϖ ^ (a₁ * k)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hsq, hJ, hJ₁, Ideal.span_singleton_pow, ← pow_mul]
  obtain ⟨a, hb, ha⟩ := map_eq_span_pow f T.irr T'.irr hm e1
  refine ⟨a, ?_, ha⟩
  have hb' : ((a₁ : ℝ) * k) = m * a := by exact_mod_cast hb
  rw [ha₁, hφ'] at hb'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  apply mul_left_cancel₀ hm0.ne'
  have : (T.be : LinearMap.BilinForm ℤ T.P.D.toPre.X) = be := rfl
  linarith [hb']

end GlobalTheory.UPoincDown
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentToComponentCompactificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_descent_to_component_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) A φ J d := by
  first | exact @GlobalTheory.UPoincDown.idealDescent | exact GlobalTheory.UPoincDown.idealDescent | (intros; apply GlobalTheory.UPoincDown.idealDescent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uIdealSt_holds : UIdealSt := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C
  haveI : IsNoetherianRing C.o := C.ded.toIsDedekindRing.toIsNoetherian
  haveI : AlgebraicGeometry.IsNoetherian C.Z := GlobalTheory.isNoetherian_of_isProjOver C.proj
  have hdom : ∀ x : C.Z, IsDomain (C.Z.presheaf.stalk x) := fun x => C.normal.isDomain_stalk x
  have hfin : (irreducibleComponents C.Z).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  letI : Fintype (irreducibleComponents C.Z) := hfin.fintype
  have hclo : ∀ k : irreducibleComponents C.Z, IsClopen (k : Set C.Z) := fun k =>
    ⟨isClosed_of_mem_irreducibleComponents _ k.2, GlobalTheory.CompPart.isOpen_of_mem hdom k.2⟩
  have key : ∀ k : irreducibleComponents C.Z, ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, x ∈ (k : Set C.Z) ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) k φ J d := by
    intro k
    by_cases hk : ((k : Set C.Z) ∩ Set.range C.i).Nonempty
    · obtain ⟨X₁, ι, J₁, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unitaryThetaSetup_ideal_over_component E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk
      exact GlobalTheory.T.ideal_descent_to_component_compactification E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk X₁ ι J₁ h1 h2 h3 h4
    · refine ⟨1, ⊤, le_rfl, fun x hx => ?_, uValThru_top_of_disjoint (hclo k).2 (Set.not_nonempty_iff_eq_empty.1 hk) φ 1⟩
      rw [Scheme.IdealSheafData.support_top] at hx
      exact absurd hx (by simp [← SetLike.mem_coe])
  choose d J hd hJ hv using key
  exact exists_uValOn_of_pieces (ι := irreducibleComponents C.Z) C.i φ (fun k => (k : Set C.Z)) J d (GlobalTheory.CompPart.existsUnique_mem hdom) hd hJ hv

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCompactification_exists_boundary_ideal : UIdealSt := by
  first | exact @GlobalTheory.UPoinc.uIdealSt_holds | exact GlobalTheory.UPoinc.uIdealSt_holds | (intros; apply GlobalTheory.UPoinc.uIdealSt_holds <;> assumption)
end
