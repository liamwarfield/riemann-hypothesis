module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodSpacesFixedByCmCurveTorsionFixingAutomorph
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsParPinsCanon
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

noncomputable section

namespace GlobalTheory.Member.ParExist

theorem datLaws_all (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

def parAtLevel (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
    (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datLaws_all D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datLaws_all D) j) l (datumAtLift_pq_pos D _ (datLaws_all D) j))
  eO := eOf D hF

theorem exists_par_pins_canon (D : D7) (hF : OFull D) (hz : OZeta D)
    (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) :
    ∃ Q : Par D, Q.Pins ∧ Q.Canon ∧ (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) ∧
      Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  obtain ⟨l, hl, hb⟩ := levelPb_exists D pb hg
  refine ⟨parAtLevel D hF hz GlobalTheory.Moduli.moduli_scheme_exists l hl, ?_, ⟨rfl, fun j hj => ?_⟩, fun j => datumAtLift_pq_pos D _ (datLaws_all D) j, hb⟩
  · refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, hl, eOf_spec D hF, fun j hj => ?_⟩
    show IsDatW D j (datumAtLift D _ (datLaws_all D) j)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact isDatW_datumOf D _ j _ _
  · show ∃ hP hd, HEq (datumAtLift D _ (datLaws_all D) j) (datumOfRecord D j hj hP hd)
    unfold datumAtLift
    rw [dite_eq_left hj]
    exact ⟨Formalism.IndefR.Fin.factPrincipalDatum, datDom_holds D j hj _, HEq.rfl⟩

end GlobalTheory.Member.ParExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FnAlgClosedOfCurveOverLcm
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedInFunctionFieldOfAutFixPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedInFunctionFieldOfAutFixPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.FixedConstLevel

open Polynomial GlobalTheory.CompRat.FixedConst

theorem fnAlgClosed_of_permutes_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff ).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, (RingHom.ext hA : σ = algebraMap (KA l) ℂ), ← Spec.map_comp]
    rfl)
  obtain ⟨P', hP', hu'⟩ := hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP
  have key := GlobalTheory.T.regularFunction_const_of_finite_values_any_level E H D l Xo σ g ty F h1 hσ hty c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP
    (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by
      rw [Category.assoc, hx, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k) hu.symm hx
  rwa [valAt'_top, valAt'_top, ev_conj, hev, hf] at key

end GlobalTheory.CompRat.FixedConstLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedInFunctionFieldOfAutFixPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffField_algClosed_in_functionField_of_aut_fix_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id | exact GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id | (intros; apply GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem fnAlgClosed_of_curveOver_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M' → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo c hD hsig hC
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine GlobalTheory.T.coeffField_algClosed_in_functionField_of_aut_fix_periods E H D l Xo _ g ty F hD rfl hty (fun _ => rfl) c fun τ hτ => ?_
  exact GlobalTheory.T.periodSpaces_fixed_by_cmCurveTorsionFixingAutomorphism E H D l Xo _ g ty F hD rfl hty (fun _ => rfl) hsig τ (fun x => hτ _ (c.le x.2)) (hC τ hτ)

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat

namespace GlobalTheory.FinalJoin.FieldAlg

theorem fnAlgClosed_of_weberIn : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l' : Level Q.H) (Xo' : Moduli (Q.Dw j) l') (c' : Coeff l') (n : ℕ), 0 < n → l'.M' ∣ n → (WeberIn Q.H c'.F n ∨ CurveOver Q.H c'.F n) → FnAlgClosed (Xo := Xo') (c := c') := by
  intro D Q hP j hj l' Xo' c' n hn hM hW
  obtain ⟨⟨ι, hι⟩, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 := GlobalTheory.RankOneDatum.exists_datum_rank_one D Q.H (Q.Dw j) (D.sp.W j) ι hι (by omega)
  have h0 : Q.H.rt0 ∈ c'.F := c'.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hC := GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ Q.H c'.F n hn
  have hc : CurveOver Q.H c'.F l'.M' := hC.2 _ hM (hW.elim (hC.1 h0) id)
  exact GlobalTheory.CompRat.fnAlgClosed_of_curveOver_lcm _ Q.H (Q.Dw j) l' Xo' c' (by omega)
    (Or.inr (Or.inr ⟨by omega, h1⟩)) hc

end GlobalTheory.FinalJoin.FieldAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValuesStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIrreducible_components_weberValues : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l' : Level Q.H) (Xo' : Moduli (Q.Dw j) l') (c' : Coeff l') (n : ℕ), 0 < n → l'.M' ∣ n → (WeberIn Q.H c'.F n ∨ CurveOver Q.H c'.F n) → FnAlgClosed (Xo := Xo') (c := c') := by
  first | exact @GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | exact GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | (intros; apply GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModel
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatAtPoint

theorem exists_ext_containing (T : CDVR) (hT : T.FinRes) {C : Type} [Field C] [CharZero C] (e : T.Fr →+* C)
    {F : Type} [Field F] [CharZero F] [FiniteDimensional ℚ F] (f : F →+* C) :
    ∃ (T₁ : CDVR) (φ : T.V →+* T₁.V) (e₁ : T₁.Fr →+* C) (f₁ : F →+* T₁.Fr), Function.Injective φ ∧ φ.Finite ∧ T₁.FinRes ∧
      e₁.comp f₁ = f ∧ ∀ a, e₁ (algebraMap T₁.V T₁.Fr (φ a)) = e (algebraMap T.V T.Fr a) := by
  have : Finite (ResidueField T.V) := hT
  have : CharZero T.Fr := IsFractionRing.charZero_of_isFractionRing T.V
  letI : Algebra T.Fr C := e.toAlgebra
  let b := Module.finBasis ℚ F
  let L : IntermediateField T.Fr C := IntermediateField.adjoin T.Fr (Set.range fun i => f (b i))
  have hfin : FiniteDimensional T.Fr L := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨i, rfl⟩
    have h₁ : IsIntegral ℚ (f (b i)) := (Algebra.IsIntegral.isIntegral (R := ℚ) (b i)).map f.toRatAlgHom
    exact h₁.tower_top
  have hmem : ∀ x, f x ∈ L := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem L _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  letI : Algebra T.V L := ((algebraMap T.Fr L).comp (algebraMap T.V T.Fr)).toAlgebra
  have : IsScalarTower T.V T.Fr L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hB : Module.Finite T.V (integralClosure T.V L) := IsIntegralClosure.finite T.V T.Fr L _
  have hBd : IsDiscreteValuationRing (integralClosure T.V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr T.V T.Fr L
  have hfr : IsFractionRing (integralClosure T.V L) L := integralClosure.isFractionRing_of_finite_extension T.Fr L
  have hinj : Function.Injective (algebraMap T.V (integralClosure T.V L)) := fun a a' h =>
    IsFractionRing.injective T.V T.Fr ((algebraMap T.Fr L).injective (congrArg Subtype.val h))
  have : FaithfulSMul T.V (integralClosure T.V L) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hz : CharZero (integralClosure T.V L) := charZero_of_injective_ringHom hinj
  have hc := GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local T.V (integralClosure T.V L)
  have hr : Finite (ResidueField (integralClosure T.V L)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Module.finite_of_finite (ResidueField T.V)
  let q : FractionRing (integralClosure T.V L) ≃ₐ[integralClosure T.V L] L := FractionRing.algEquiv _ L
  refine ⟨{ V := integralClosure T.V L }, algebraMap _ _, (algebraMap L C).comp q.toRingEquiv.toRingHom,
    q.symm.toRingEquiv.toRingHom.comp (f.codRestrict L hmem), hinj, RingHom.finite_algebraMap.2 hB, hr,
    RingHom.ext fun x => ?_, fun a => ?_⟩
  · exact congrArg Subtype.val (q.apply_symm_apply ⟨f x, hmem x⟩)
  · exact congrArg Subtype.val (q.commutes _)

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem eq_of_field_ext {K C O : Type} [Field K] [Field C] [CommRing O] (e : K →+* C) (u v : Sp K ⟶ Sp O)
    (h : spMap e ≫ u = spMap e ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := Spec.map_surjective u
  obtain ⟨v, rfl⟩ := Spec.map_surjective v
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact e.injective (congrArg (fun w => w.hom a) h')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_lift_to_open (Y : Model Xo c β) {K C : Type} [Field K] [Field C] (e : K →+* C) (f : c.F →+* K)
    (x : Sp K ⟶ Y.X) (y : Sp C ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap (e.comp f))
    (h : spMap e ≫ x = y ≫ Y.j) : ∃ z : Sp K ⟶ Xo.XF c, z ≫ Y.j = x := by
  have hj : Y.j = Y.jQ ≫ pullback.fst _ _ := rfl
  have hc : x ≫ Y.s = spMap f ≫ spMap β := by
    refine eq_of_field_ext e _ _ ?_
    rw [← Category.assoc, h, hj, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, hy, ← Category.assoc, spMap_spMap f]
  let w : Sp K ⟶ pullback Y.s (spMap β) := pullback.lift x (spMap f) hc
  have hw : spMap e ≫ w = y ≫ Y.jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, h, hj, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Y.jQ_over, hy, spMap_spMap]
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    let q' : Sp C := (default : PrimeSpectrum C)
    have hq : spMap e q' = q := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨y q', ?_⟩
    rw [← hq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_⟩
  rw [hj, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem exists_datAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∃ A : DatAt Y P, (∃ _ : IsDiscreteValuationRing A.R, Finite (ResidueField A.R)) ∧ Function.Injective A.f ∧ ∃ φ : T.V →+* A.R, A.f.comp φ = g ∧ A.ι = spMap φ ≫ ιT ∧ φ.Finite := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P _ T g ιT hT hg hloc hfac
  have hinj : Function.Injective ((intO ↥C.S).subtype.comp g) := Subtype.val_injective.comp hg
  let eF : T.Fr →+* ↥C.S := IsFractionRing.lift hinj
  have heF : ∀ a, eF (algebraMap T.V T.Fr a) = ((g a : intO ↥C.S) : ↥C.S) := fun a =>
    IsFractionRing.lift_algebraMap hinj a
  clear_value eF
  have := c.fin
  obtain ⟨T₁, φ₁, e₁, f₁, hi₁, hf₁, hT₁, hef, he₁⟩ := exists_ext_containing T hT eF P.fK
  have hring : (e₁.comp (algebraMap T₁.V T₁.Fr)).comp φ₁ = (intO ↥C.S).subtype.comp g :=
    RingHom.ext fun a => (he₁ a).trans (heF a)
  obtain ⟨z, hz⟩ := exists_lift_to_open Y e₁ f₁ (spMap (algebraMap T₁.V T₁.Fr) ≫ spMap φ₁ ≫ ιT) P.y
    (by rw [hef, P.y_over]) (by
      rw [← P.ext, ← hfac, ← Category.assoc, spMap_spMap, ← Category.assoc, spMap_spMap, hring, ← Category.assoc,
        spMap_spMap])
  obtain ⟨t, m⟩ : ∃ t : SAB H (Sp T₁.V), Nonempty (SABMap t Y.t (spMap φ₁ ≫ ιT)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap φ₁ ≫ ιT) Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m⟩ := m
  obtain ⟨tK, mK⟩ : ∃ tK : SAB H (Sp T₁.Fr), Nonempty (SABMap tK t (spMap (algebraMap T₁.V T₁.Fr))) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ :=
      sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T₁.V T₁.Fr)) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mK⟩ := mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t t _ _ _ m mK
  have cancel : ∀ (q : Sp T₁.Fr ⟶ Y.X) (_ : q = z ≫ Y.j) (_ : SABMap tK Y.t q), Nonempty (SABMap tK Y.oF.t z) := by
    intro q hq n; subst hq
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m'⟩ := cancel _ hz.symm n
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ (pullback.fst _ _) z Y.m0.toSABMap m'
  obtain ⟨T', φ', t', m₂, hi', hf', hT', -, U, hU, hTor⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T₁ t tK mK _ mx hT₁
  have hφ : (φ'.comp φ₁).Finite := hf'.comp hf₁
  obtain ⟨-, -, -, -, -, hext⟩ :=
    GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' (φ'.comp φ₁) (hi'.comp hi₁) hφ
  obtain ⟨f, hfi, hfg, hfl⟩ := hext p C eF (fun a => by rw [heF]; exact (g a).2) (fun a ha => by rw [heF]; exact hloc a ha)
  have hcomp : f.comp (φ'.comp φ₁) = g := RingHom.ext fun a => Subtype.ext ((hfg a).trans (heF a))
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E H _ _ _ Y.t t t' _ _ m m₂
  have hι : spMap φ' ≫ spMap φ₁ ≫ ιT = spMap (φ'.comp φ₁) ≫ ιT := by rw [← Category.assoc, spMap_spMap]
  have hab : (spMap φ' ≫ spMap φ₁ ≫ ιT) ⁻¹' abLocus Y.t.G = abLocus t'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n₂.cart.1 q
  refine ⟨
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ' ≫ spMap φ₁ ≫ ιT
      f := f
      f_loc := hfl
      fac := by rw [hι, ← Category.assoc, spMap_spMap, hcomp, hfac]
      t := t'
      m := n₂
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hTor }, ⟨T'.dvr, hT'⟩, hfi, φ'.comp φ₁, hcomp, hι, hφ⟩

end GlobalTheory.DatAtPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModelStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degeneration_data_algebraic_point_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∃ A : DatAt Y P, (∃ _ : IsDiscreteValuationRing A.R, Finite (ResidueField A.R)) ∧ Function.Injective A.f ∧ ∃ φ : T.V →+* A.R, A.f.comp φ = g ∧ A.ι = spMap φ ≫ ιT ∧ φ.Finite := by
  first | exact @GlobalTheory.DatAtPoint.exists_datAt | exact GlobalTheory.DatAtPoint.exists_datAt | (intros; apply GlobalTheory.DatAtPoint.exists_datAt <;> assumption)
end
end
