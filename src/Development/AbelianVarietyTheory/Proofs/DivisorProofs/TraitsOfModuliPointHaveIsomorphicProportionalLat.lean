module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationsCharacterIsoAssociatedCoord
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationsCharacterIsoAssociatedCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PelUnifUniqCoord

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → ∀ (t : SAB H (Sp W)) (P P' : PELUnif (maximalIdeal W) t),
      ∃ e : P.D.toPre.X ≃ₗ[𝓞 E] P'.D.toPre.X, ∀ y r r', PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (e y) r' →
        Associated (r ^ 2) (r' ^ 2) := by
  intro E _ _ _ H W _ _ _ hW t P P'
  haveI : CharZero W := hW.2
  obtain ⟨m, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨e, he⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H W t t m P P' hW.1.1 hW.1.2.2.1 hW.1.2.2.2
  refine ⟨e, fun y r r' hr hr' => ?_⟩
  obtain ⟨u, hu⟩ := he y r hr
  have h1 : Associated (u * r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  have h2 : Associated r r' := (associated_unit_mul_left r u u.isUnit).symm.trans h1
  exact h2.pow_pow

end GlobalTheory.PelUnifUniqCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationsCharacterIsoAssociatedCoordStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_uniformisations_character_iso_associated_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → ∀ (t : SAB H (Sp W)) (P P' : PELUnif (maximalIdeal W) t),
      ∃ e : P.D.toPre.X ≃ₗ[𝓞 E] P'.D.toPre.X, ∀ y r r', PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (e y) r' →
        Associated (r ^ 2) (r' ^ 2) := by
  first | exact @GlobalTheory.PelUnifUniqCoord.main | exact GlobalTheory.PelUnifUniqCoord.main | (intros; apply GlobalTheory.PelUnifUniqCoord.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitUniq

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {w : W} (hw : Irreducible w) {a b : ℕ}
    (h : Associated (w ^ a) (w ^ b)) : a = b := by
  have key : ∀ {a b : ℕ}, Associated (w ^ a) (w ^ b) → a ≤ b → a = b := by
    intro a b h hab
    by_contra hne
    have hlt : 0 < b - a := by omega
    have h1 : Associated (w ^ a * 1) (w ^ a * w ^ (b - a)) := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]; exact h
    have h2 : Associated 1 (w ^ (b - a)) :=
      Associated.of_mul_left h1 (Associated.refl _) (pow_ne_zero _ hw.ne_zero)
    have h3 : IsUnit (w ^ (b - a)) := associated_one_iff_isUnit.1 h2.symm
    exact hw.not_isUnit ((isUnit_pow_iff hlt.ne').1 h3)
  rcases le_total a b with hab | hab
  · exact key h hab
  · exact (key h.symm hab).symm

theorem sq_associated {V W : Type} [CommRing V] [CommRing W] [IsDomain W] (f : V →+* W) (ϖ : V) (w : W) (m n : ℕ)
    (hm : Associated (f ϖ) (w ^ m)) (v : Wˣ) (u : Vˣ) :
    Associated ((v * f (u * ϖ ^ n)) ^ 2) (w ^ (2 * (m * n))) := by
  have hu : IsUnit (f (u : V)) := (Units.isUnit u).map f
  have e : (v * f (u * ϖ ^ n)) ^ 2 = (((v : W) * f u) ^ 2) * (f ϖ ^ n) ^ 2 := by
    rw [map_mul, map_pow]; ring
  rw [e]
  refine (associated_unit_mul_left _ _ ((v.isUnit.mul hu).pow 2)).trans ?_
  have eq : w ^ (2 * (m * n)) = ((w ^ m) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
  rw [eq]
  exact (hm.pow_pow (n := n)).pow_pow (n := 2)

end GlobalTheory.UPoinc.TraitUniq


open GlobalTheory.UPoinc.TraitUniq in
theorem GlobalTheory.UPoinc.uTraitUniqSt_holds : UTraitUniqSt := by
  intro E _ _ _ H Dw l Xo c T T' W _ _ _ f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy w m m' hw hm hm'
  obtain ⟨tW, ⟨φ⟩, ⟨φ'⟩⟩ := GlobalTheory.T.exists_common_semiAbelian_pullback_two_unitary_traits E H Dw l Xo c T T' W f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy
  obtain ⟨PW, e1, he1⟩ := GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr E H T.V T.cdvr T.t T.P W hB hW f hf hfl tW ⟨φ⟩
  obtain ⟨PW', e1', he1'⟩ := GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr E H T'.V T'.cdvr T'.t T'.P W hB hW f' hf' hfl' tW ⟨φ'⟩
  obtain ⟨e2, he2⟩ := GlobalTheory.T.linear_uniformisations_character_iso_associated_coords E H W hB tW PW PW'
  let e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X := e1.symm.trans (e2.trans e1')

  have diag : ∀ y, (m : ℤ) * T.be y y = m' * T'.be (e y) (e y) := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := T.mono y
    obtain ⟨u', n', hn', hc'⟩ := T'.mono (e y)
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one] at hn hc hn' hc'
    have hc1 : PsiCoord T.P.D.toPre (e1 (e1.symm y)) (u * T.ϖ ^ n 0) := by
      rw [LinearEquiv.apply_symm_apply]; exact hc
    obtain ⟨v, hv⟩ := he1 _ _ hc1
    obtain ⟨v', hv'⟩ := he1' (e2 (e1.symm y)) _ hc'
    have ha := he2 _ _ _ hv hv'
    have h1 := sq_associated f T.ϖ w m (n 0) hm v u
    have h2 := sq_associated f' T'.ϖ w m' (n' 0) hm' v' u'
    have := pow_eq_of_associated hw (h1.symm.trans (ha.trans h2))
    rw [hn 0, hn' 0]
    have : ((2 * (m * n 0) : ℕ) : ℤ) = ((2 * (m' * n' 0) : ℕ) : ℤ) := by rw [this]
    push_cast at this
    linarith
  have hs : ∀ a b, T.be a b = T.be b a := fun a b => (mem_levelForms.1 T.lev).1 a b
  have hs' : ∀ a b, T'.be a b = T'.be b a := fun a b => (mem_levelForms.1 T'.lev).1 a b
  refine ⟨e, fun a b => ?_⟩
  have h := diag (a + b)
  simp only [map_add (f := _), LinearMap.add_apply] at h
  have ha := diag a
  have hb := diag b
  rw [hs b a, hs' (e b) (e a)] at h
  linarith
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitsOfModuliPoint_have_isomorphic_proportional_lattices : UTraitUniqSt := by
  first | exact @GlobalTheory.UPoinc.uTraitUniqSt_holds | exact GlobalTheory.UPoinc.uTraitUniqSt_holds | (intros; apply GlobalTheory.UPoinc.uTraitUniqSt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNonemptyCrystallineTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UPoinc.UCTraitEx

theorem injective_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K]
    (ψ : o →+* K) : Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hbot : RingHom.ker ψ ≠ ⊥ := fun h => ha0 (by
    have h' : a ∈ RingHom.ker ψ := ha
    rwa [h, Ideal.mem_bot] at h')
  haveI hmax : (RingHom.ker ψ).IsMaximal := hP.isMaximal hbot
  haveI := GlobalTheory.finite_quotient_of_finiteType_int (RingHom.ker ψ)
  haveI : CharZero (o ⧸ RingHom.ker ψ) := (RingHom.charZero_iff (RingHom.kerLift_injective ψ)).2 inferInstance
  exact not_finite (o ⧸ RingHom.ker ψ)

theorem exists_lift_genericFibre {o F K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F]
    (b : o →+* F) (hb : letI := b.toAlgebra; IsFractionRing o F) [Field K] [CharZero K] {Z : Scheme.{0}} (z : Z ⟶ Sp o)
    (x : Sp K ⟶ Z) : ∃ x' : Sp K ⟶ pullback z (spMap b), x' ≫ pullback.fst _ _ = x := by
  letI := b.toAlgebra
  haveI := hb
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ z)
  have hinj := injective_of_charZero ψ.hom
  let ψ' : F →+* K := IsFractionRing.lift hinj
  have hc : ψ'.comp b = ψ.hom := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  have e : x ≫ z = spMap ψ' ≫ spMap b := by
    rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', hc, ← hψ]; rfl
  exact ⟨pullback.lift x (spMap ψ') e, pullback.lift_fst _ _ _⟩

theorem exists_finite_point_rat {X : Scheme.{0}} (s : X ⟶ Sp ℚ) [LocallyOfFiniteType s] (p : ℕ) [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := ℚ) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U))
  have hSfin : S.Finite := T.finite_toSet.image _
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : ℚ, φ.hom (a.hom c) ∈ K := fun c => by
    rw [show φ.hom (a.hom c) = (φ.hom.comp a.hom) c from rfl, eq_ratCast]
    exact SubfieldClass.ratCast_mem K c
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin ℚ (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS ⟨x, hx, rfl⟩
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, GlobalTheory.Poinc.GCTrait.spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

theorem exists_uCTrait_of_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime], ∃ U : X.M.Z.Opens, (U : Set X.M.Z).Nonempty ∧ ∀ y : Sp (OO p) ⟶ X.M.Z, Set.range (gPt p ≫ y) ⊆ U → ∃ ct : UCTrait X p (y (cPt p)), ct.y = y := by
  intro E _ _ _ H Dw _ l Xo cf C X p _
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb : Topology.IsEmbedding (pullback.fst C.z (spMap C.b)) := Scheme.Hom.isEmbedding _
  let S : Set C.Z := pullback.fst C.z (spMap C.b) '' (Set.range C.iF)ᶜ
  have hS : pullback.fst C.z (spMap C.b) ⁻¹' closure S = (Set.range C.iF)ᶜ := by
    rw [← hemb.isInducing.closure_eq_preimage_closure_image]
    exact C.iF.isOpenEmbedding.isOpen_range.isClosed_compl.closure_eq
  let V : C.Z.Opens := ⟨(closure S)ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨X.π ⁻¹ᵁ V, ?_, ?_⟩
  · let w : Sp X.Ω₁ := IsLocalRing.closedPoint X.Ω₁
    refine ⟨X.M.pt w, ?_⟩
    have e : X.π (X.M.pt w) =
        pullback.fst C.z (spMap C.b) (C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w)) := by
      rw [← Scheme.Hom.comp_apply, X.comp]
      simp only [UCompact.i, Scheme.Hom.comp_apply]
    show X.π (X.M.pt w) ∈ (closure S)ᶜ
    rw [e]
    intro hc
    have h' : C.iF ((spMap (ratHull X.S.R).val.toRingHom ≫ X.u) w) ∈ (Set.range C.iF)ᶜ := hS ▸ hc
    exact h' ⟨_, rfl⟩
  · intro y hr
    obtain ⟨x', hx'⟩ := exists_lift_genericFibre C.b C.isFractionRing C.z (gPt p ≫ y ≫ X.π)
    have hr' : Set.range x' ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      by_contra hn
      have h1 : pullback.fst C.z (spMap C.b) (x' w) ∈ closure S := subset_closure ⟨_, hn, rfl⟩
      have h2 : (gPt p ≫ y) w ∈ X.π ⁻¹ᵁ V := hr ⟨w, rfl⟩
      have h3 : pullback.fst C.z (spMap C.b) (x' w) = X.π ((gPt p ≫ y) w) := by
        rw [← Scheme.Hom.comp_apply, hx']
        simp only [Scheme.Hom.comp_apply]
      exact h2 (h3 ▸ h1)
    let y₁ : Sp (PadicAlgCl p) ⟶ Xo.XF cf := IsOpenImmersion.lift C.iF x' hr'
    have hy₁ : y₁ ≫ C.i = gPt p ≫ y ≫ X.π := by
      show y₁ ≫ C.iF ≫ pullback.fst _ _ = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hx']
    haveI := cf.fin
    haveI := Xo.smooth
    haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
    haveI : LocallyOfFiniteType (spMap (algebraMap ℚ cf.F)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
    obtain ⟨K, hK, x, hx⟩ := exists_finite_point_rat (pullback.snd _ _ ≫ spMap (algebraMap ℚ cf.F)) p y₁
    obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
    haveI := hdvr
    haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
    let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
    let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
    have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) :=
      ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
    obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ :=
      GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf _ hbase hdvr (spMap es ≫ x)
    haveI : IsDiscreteValuationRing T.V := T.cdvr.1
    obtain ⟨ι, hι, hint⟩ := GlobalTheory.Poinc.GCTrait.exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
    have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
        (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
      refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
      show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
      rw [AlgEquiv.commutes]
      rfl
    have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es =
        algebraMap K (PadicAlgCl p) := by
      ext k
      rw [h2]
      show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
      rw [AlgEquiv.apply_symm_apply]
    have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
      rw [GlobalTheory.Poinc.GCTrait.spMap_comp'', GlobalTheory.Poinc.GCTrait.spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
    refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
    calc gPt p ≫ y ≫ X.π = y₁ ≫ C.i := hy₁.symm
      _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ C.i := by rw [hx]
      _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ C.i := by rw [key]
      _ = spMap ι ≫ T.y ≫ C.i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.UPoinc.UCTraitEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastBis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem USetup.range_π_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (η : Xo.XF c) (A : Set C.Z), (∀ w, X₁.uΩ w = η) → closure {C.i η} = A → Set.range X₁.π = A := by
  intro E _ _ _ H Dw _ l Xo c C X₁ η A hη hA
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = C.i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hA, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actG_form_eq_sim : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (L.actG g v) (L.actG g w) = (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) v w := by
  intro p _ D G L g v w
  set y : (AfP p ⊗[ℚ] G.C)ˣ := (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 with hy
  set c : AfP p := (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) with hc
  have hmem : (y : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := mem_uGroup.1 g.2
  have hsy : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop * (y : AfP p ⊗[ℚ] G.C) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
    have h1 : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
        ((y⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
      rw [← hmem, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [h1, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hact : ∀ u : AfP p ⊗[ℚ] VQ D, L.actG g u = actOn L.rep (AfP p) (y : AfP p ⊗[ℚ] G.C) u := fun u => rfl
  rw [hact, hact, GlobalTheory.LKGeo.adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, hsy, AlgHom.commutes,
    Module.algebraMap_end_apply, LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.LKGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (L.actG g v) (L.actG g w) = (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) v w := by
  first | (exact @GlobalTheory.LKGeo.actG_form_eq_sim) | (exact GlobalTheory.LKGeo.actG_form_eq_sim) | (intros; apply GlobalTheory.LKGeo.actG_form_eq_sim  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrysForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual GlobalTheory.Published.GrothendieckMessing

namespace GlobalTheory.HTDefLift

theorem exists_crysForm : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ φ₀ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ₀ ∧ (∀ φ, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → φ = φ₀) ∧ (∀ (c : D.O) x y, φ₀ (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x) y = φ₀ x (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (D.star c).unop y)) ∧ ∃ φ' : HdR o₀.A →ₗ[C₀] HdR o₀.A →ₗ[C₀] C₀, GlobalTheory.AbDual.IsCorrForm (dp0 C₀) (𝟙 _) o₀.A o₀.A o₀.P φ' ∧ ∀ x x' y y', (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr x x' → (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr y y' → φ' x' y' = π (φ₀ x y) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm CS o₀.isLB o₀.rig₁ o₀.rig₂
  refine ⟨φ₀, hφ₀, fun φ hφ ↦ hφ.unique CS o₀.isLB hφ₀, fun c x y ↦ ?_, ?_⟩
  · haveI := o₀.act.hom c
    haveI := o₀.act.hom (D.star c).unop
    have := hφ₀.adjoint CS o₀.isLB o₀.isLB hφ₀ (o₀.act.act c) (o₀.act.act (D.star c).unop) (LBIso.symm (o₀.rosati c)) x y
    exact this.symm
  · have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
      (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₀.isLB _) o₀.isLB).1
        (by rw [GlobalTheory.CechPic.cls_pull o₀.isLB, Over.id_left, GlobalTheory.CechPic.pull_id])
    obtain ⟨φ', hφ', e'⟩ := hφ₀.pull o₀.isLB (crysRedMor κ rfl o₀.A) (crysRedMor κ rfl o₀.A)
      (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) o₀.isLB iso
    exact ⟨φ', hφ', e'⟩

end GlobalTheory.HTDefLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.TraitPull

theorem exists_pull_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  intro E _ _ _ H Dw l Xo c T W _ _ _ hW hWd h hi hl
  obtain ⟨tW, ⟨m⟩⟩ := GlobalTheory.Models.Inhab.exists_pull (spMap h) T.t
  obtain ⟨PW, e, he⟩ := GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T.V T.cdvr T.t T.P W hW hWd h hi hl tW ⟨m⟩
  refine ⟨tW, m, PW, e, fun y => ?_⟩
  obtain ⟨u, n, hn, hc⟩ := T.mono (e y)
  have hn0 : T.be (e y) (e y) = 2 * (n 0 : ℤ) := hn 0
  obtain ⟨v, hv⟩ := he y _ hc
  refine ⟨by rw [hn0]; positivity, _, hv, ?_⟩
  have ht : (T.be (e y) (e y)).toNat = 2 * n 0 := by rw [hn0]; omega
  rw [ht]
  have hu : IsUnit ((v : W) * h u) := v.isUnit.mul (u.isUnit.map h)
  have e1 : ((v : W) * h (u * ∏ i, ![T.ϖ] i ^ n i)) ^ 2 = ((v : W) * h u) ^ 2 * h T.ϖ ^ (2 * n 0) := by
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
    ring
  rw [e1]
  exact associated_unit_mul_left _ _ (hu.pow 2)

end GlobalTheory.UPoinc.TraitPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_uniformisation_pulled_back_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  first | exact @GlobalTheory.UPoinc.TraitPull.exists_pull_unif | exact GlobalTheory.UPoinc.TraitPull.exists_pull_unif | (intros; apply GlobalTheory.UPoinc.TraitPull.exists_pull_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChartNotAb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem subsingleton_of_closed_mem_abLocus {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    (P : PELUnif (maximalIdeal R) t) (hc : (closedPoint R : Sp R) ∈ abLocus t.G) : Subsingleton P.D.toPre.X := by
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : maximalIdeal R ^ (0 + 1) ≤ (closedPoint R).asIdeal := by
    rw [zero_add, pow_one]; exact le_rfl
  obtain ⟨q, hq⟩ : closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hq' : thick R (maximalIdeal R) 0 q ∈ abLocus t.G := by
    rw [← hq] at hc; exact hc
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom

end GlobalTheory.ChartNotAb


open GlobalTheory.ChartNotAb in
theorem GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  intro E _ _ _ H Dw l Xo c φ k _ m e C hT hm hc
  obtain ⟨-, -, -, -, -, ⟨N, s, ε, τ₀, -, hε, -, -⟩, -⟩ := hT
  have hs := subsingleton_of_closed_mem_abLocus C.P hc
  let i : Fin C.m := ⟨0, hm⟩
  apply ε.ne_zero (Sum.inl i)
  apply Subtype.ext
  rw [Submodule.coe_zero, hε i]
  ext x y
  rw [Subsingleton.elim x 0]
  simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointNotMemAbelianLocusTautologicalBoundarStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  first | exact @GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | exact GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut | (intros; apply GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegral
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DenAway

open IsDedekindDomain

theorem isIntAf_algebraMap_inv_prime (p : ℕ) [Fact p.Prime] : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹) := by
  intro v
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
    refine le_antisymm (v.1.valuation_le_one _) (not_lt.1 fun h => v.2 ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at h
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Fact.out).irreducible
    exact (hm.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (p : ℚ)⁻¹) = v.1.valuation ℚ (p : ℚ)⁻¹ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
  rw [h2, map_inv₀]
  simp only [eq_intCast, Int.cast_natCast] at h1
  rw [h1, inv_one]

theorem exists_coprime_nat_adele : ∀ (p : ℕ) [Fact p.Prime] (a : AfP p),
    ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ IsIntAf ((j : AfP p) * a) := by
  intro p _ a
  obtain ⟨n, hn, hna⟩ := exists_nat_adele a
  obtain ⟨e, j, hj, hnj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h => hj (h ▸ dvd_zero p)
  refine ⟨j, hj0, ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hj).symm, ?_⟩
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e1 : (j : AfP p) * a = algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ e) * ((n : AfP p) * a) := by
    rw [hnj, Nat.cast_mul, Nat.cast_pow, ← _root_.mul_assoc, ← _root_.mul_assoc]
    congr 1
    rw [← map_natCast (algebraMap ℚ (AfP p)) p, ← map_pow, ← map_mul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hp), map_one, _root_.one_mul]
  rw [e1]
  intro v
  rw [map_mul, map_pow]
  exact mul_mem (pow_mem (isIntAf_algebraMap_inv_prime p v) e) (hna v)

end GlobalTheory.DenAway
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegralStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral : ∀ (p : ℕ) [Fact p.Prime] (a : AfP p), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ IsIntAf ((j : AfP p) * a) := by
  first | (exact @GlobalTheory.DenAway.exists_coprime_nat_adele) | (exact GlobalTheory.DenAway.exists_coprime_nat_adele) | (intros; apply GlobalTheory.DenAway.exists_coprime_nat_adele  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuli
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem ker_eq_bot_of_charZero {o K : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field K]
    [CharZero K] (φ : o →+* K) : RingHom.ker φ = ⊥ := by
  by_contra h
  haveI : (RingHom.ker φ).IsMaximal := (RingHom.ker_isPrime φ).isMaximal h
  letI := Ideal.Quotient.field (RingHom.ker φ)
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker φ) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : CharZero (o ⧸ RingHom.ker φ) := (RingHom.charZero_iff (RingHom.kerLift_injective φ)).2 inferInstance
  exact Int.not_isField (isField_of_isIntegral_of_isField (R := ℤ) (S := o ⧸ RingHom.ker φ)
    (fun _ _ h => Int.cast_injective (α := o ⧸ RingHom.ker φ) (by simpa using h)) (Field.toIsField _))

theorem UCompact.range_subset_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} (C : UCompact Xo c) {K : Type} [Field K] [CharZero K]
    (x : Sp K ⟶ Sp C.o) : Set.range x ⊆ Set.range (spMap C.b) := by
  haveI := C.ded
  haveI := C.ft
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  rintro _ ⟨w, rfl⟩
  refine ⟨(⊥ : PrimeSpectrum c.F), PrimeSpectrum.ext ?_⟩
  show Ideal.comap C.b ⊥ = Ideal.comap φ.hom w.asIdeal
  rw [Subsingleton.elim w (⊥ : PrimeSpectrum K)]
  exact ((RingHom.injective_iff_ker_eq_bot _).1 C.inj).trans (ker_eq_bot_of_charZero (K := K) φ.hom).symm

theorem exists_open_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  intro E _ _ _ H Dw l Xo c C
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨U, hU, hUe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := hUe ▸ ⟨x, rfl⟩
    exact this
  · intro p _ y hy
    rintro _ ⟨w, rfl⟩
    have h1 : (gPt p ≫ y) w ∈ Set.range (pullback.fst C.z (spMap C.b) :) := by
      rw [Scheme.Pullback.range_fst]
      exact C.range_subset_generic ((gPt p ≫ y) ≫ C.z) ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := h1
    have h2 : t ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' U := by
      show _ ∈ U
      rw [ht]
      exact hy ⟨w, rfl⟩
    rw [hUe] at h2
    obtain ⟨x, rfl⟩ := h2
    exact ⟨x, ht⟩

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_compactification_generic_subset_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∃ W : C.Z.Opens, Set.range C.i ⊆ W ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), Set.range (gPt p ≫ y) ⊆ W → Set.range (gPt p ≫ y) ⊆ Set.range C.i := by
  first | exact @GlobalTheory.UPoinc.exists_open_generic_subset_moduli | exact GlobalTheory.UPoinc.exists_open_generic_subset_moduli | (intros; apply GlobalTheory.UPoinc.exists_open_generic_subset_moduli <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdAroots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdAroots
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem deg_aeval_eq_prod_aroots :
    ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ),
      algebraMap ℚ Ω (deg (Polynomial.aeval f R).asHom : ℚ) =
        ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map
          (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous
      K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change (deg (∑ i, m i • End.addEquiv (Polynomial.aeval f (u i))) : ℚ) =
      (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = ((n : End A) - f) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    rw [e]
    exact Int.cast_natCast _

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdArootsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_aeval_end_eq_prod_aroots : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ), algebraMap ℚ Ω (deg (A := A) (B := A) (Polynomial.aeval f R).asHom : ℚ) = ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    change (deg (Polynomial.aeval f (F * G)).asHom : ℚ) =
      (deg (Polynomial.aeval f F).asHom : ℚ) * (deg (Polynomial.aeval f G).asHom : ℚ)
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n
      (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change _ = (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)
    simp only [map_sum, map_zsmul, End.addEquiv_apply]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = (n : End A) - f := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    change ((charpoly f).map (Int.castRingHom ℚ)).eval (n : ℚ) =
      (deg (Polynomial.aeval f (Polynomial.C n - Polynomial.X)).asHom : ℚ)
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n, e, map_natCast]
end
end
