module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurve
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PrincDegZero

theorem log_card_eq (κ : Type) [Field κ] [Finite κ] (V : Type) [AddCommGroup V] [Module κ V] :
    Real.log (Nat.card V) = Module.finrank κ V * Real.log (Nat.card κ) := by
  by_cases h : Module.Finite κ V
  · have : Finite V := Module.finite_of_finite κ
    rw [Module.natCard_eq_pow_finrank (K := κ)]
    push_cast
    rw [Real.log_pow]
  · rw [Module.finrank_of_not_finite h]
    have : Infinite V := by
      by_contra h'
      have := not_infinite_iff_finite.1 h'
      exact h (Module.Finite.of_finite)
    simp [Nat.card_eq_zero_of_infinite]

theorem log_card_residueField {κ : Type} [Field κ] [Finite κ] {Y : Scheme.{0}} [IsIntegral Y] [Algebra κ Γ(Y, ⊤)]
    [LocallyOfFiniteType (strHom κ (X := Y))] (hd : topologicalKrullDim Y = (0 + 1 : ℕ)) {z : Y}
    (hz : Order.coheight z = 1) :
    Real.log (Nat.card (Y.residueField z)) =
      (interNumRed κ (⟨closure {z}, isClosed_closure⟩ : Closeds Y) (Fin.elim0 : Fin 0 → LB Y) : ℝ) *
        Real.log (Nat.card κ) := by
  have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Y) hd hz
  obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range j = closure {j (genericPoint W)} := by
    rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
  letI := algebraΓAlong κ j
  have hW : topologicalKrullDim W = (0 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
  rw [InterModel.interNumRed_eq_interNumOn _ j _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun i => i.elim0), interNum_of_isEmpty]
  have hu (w : W) : w = genericPoint W := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds W) ≤ 0
      from hW.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ W, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec W)
  have hZ : ({genericPoint W} : Set W) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint W} : Set W) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (W.fromSpecResidueField (genericPoint W)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (W.fromSpecResidueField (genericPoint W))
  have : IsAffine W := .of_isIso (inv (W.fromSpecResidueField (genericPoint W)))
  have : IsIso (W.fromSpecResidueField (genericPoint W)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (j.residueFieldMap (genericPoint W)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := W.residue_surjective _ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective _ a
    exact ⟨Y.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((W.fromSpecResidueField (genericPoint W)).appTop ≫
      (Scheme.ΓSpecIso (W.residueField (genericPoint W))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(W, ⊤) ≃ Y.residueField (j (genericPoint W)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, log_card_eq κ]
  push_cast
  ring

end GlobalTheory.PrincDegZero

namespace GlobalTheory.PrincDegZero

theorem finsum_ord_mul_log_card_eq_zero : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  intro k _ Y _ _ q hA hd l _ _ f hf
  have : Module.Finite ℤ k := hA.finite
  have : AlgebraicGeometry.IsNoetherian Y := hA.isNoetherian
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hpr, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hA.isProjOver
  have hp : IsProjOver (strHom (ZMod l) (X := Y)) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)) = q ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) (X := Y)) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, H, hH⟩
  have : IsProper (strHom (ZMod l) (X := Y)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hd' : topologicalKrullDim Y = (0 + 1 : ℕ) := hd
  let r : (LB.triv Y).ι → Y.functionFieldˣ := fun _ => Units.mk0 f hf
  have hr : IsRatSec (LB.triv Y) r := fun _ _ h => by simp [r]
  have hM := LB.isLB_triv Y
  have key := GlobalTheory.ratSec_cycle_formula (ZMod l) Y hp 0 hd.le (LB.triv Y) hM Fin.elim0 (fun i => i.elim0) r hr
  rw [interNum_eq_zero_of_cls_eq_zero (ZMod l) _ (isLB_cons hM fun i => i.elim0) 0 (cls_triv _)] at key
  have hm (z : Y) : (divOfRatSec hM hr).mult z = Scheme.ord f z :=
    ((presents_divOfRatSec hM hr).isEqn PUnit.unit z trivial).mult_eq
  have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hM hr).mult w *
      interNumRed (ZMod l) (⟨closure {w}, isClosed_closure⟩ : Closeds _) (Fin.elim0 : Fin 0 → LB Y) :=
    (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
  have em := (AddMonoidHom.mulRight (Real.log (Nat.card (ZMod l)))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
  rw [← key] at em
  simp only [map_zero] at em
  refine (finsum_congr fun z => ?_).trans em.symm
  change (Scheme.ord f z : ℝ) * _ = (((divOfRatSec hM hr).mult z * _ : ℤ) : ℝ) * _
  rw [hm]
  by_cases hz : Scheme.ord f z = 0
  · simp [hz]
  have hc : Order.coheight z = 1 := by
    by_contra h
    exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  rw [Int.cast_mul, mul_assoc, log_card_residueField (κ := ZMod l) hd' hc]

end GlobalTheory.PrincDegZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalDivisor_degree_zero_finiteField_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  first | exact @GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero | exact GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero | (intros; apply GlobalTheory.PrincDegZero.finsum_ord_mul_log_card_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveFinsumOrdLogEqLocalLengths
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveFinsumOrdLogEqLocalLengths
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.AffineCurveSum

theorem length_quot_eq {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (p : Submonoid B)
    [IsLocalization p S] (b : B) :
    Module.length S (S ⧸ Ideal.span {algebraMap B S b}) =
      Module.length (Localization p) (LocalizedModule p (B ⧸ Ideal.span {b})) := by
  let e := IsLocalization.algEquiv p (Localization p) S
  let : Algebra (Localization p) S := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower B (Localization p) S := .of_algebraMap_eq fun x => (e.commutes x).symm
  have h : Submodule.localized' S p (Algebra.linearMap B S) (Ideal.span {b}) =
      Ideal.span {algebraMap B S b} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  rw [← h, ← Module.length_eq_of_surjective (S := Localization p) (R := S) e.surjective]
  exact (((IsLocalizedModule.iso p (Submodule.toLocalizedQuotient' S p (Algebra.linearMap B S)
    (Ideal.span {b}))).extendScalarsOfIsLocalization p (Localization p)).length_eq).symm

theorem finsum_ord_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), b ≠ 0 → ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ m : MaximalSpectrum Γ(Y, ⊤), ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl (Γ(Y, ⊤) ⧸ Ideal.span {b}))).toNat : ℝ) * Real.log (Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal)) := by
  intro k _ Y _ _ _ q hq b hb
  have hU := isAffineOpen_top Y
  have hd : ringKrullDim Γ(Y, ⊤) = 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    have := (Scheme.homeoOfIso Y.isoSpec).isHomeomorph.topologicalKrullDim_eq
    exact this.symm.trans (hq.dim_eq.trans (by simp))
  have hc (z : Y) : (Order.coheight z : WithBot ℕ∞) =
      (hU.primeIdealOf ⟨z, trivial⟩).asIdeal.height := by
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨z, trivial⟩ : (⊤ : Y.Opens))
    have := hU.isLocalization_stalk ⟨z, trivial⟩
    exact (ringKrullDim_stalk_eq_coheight z).symm.trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height _ _)
  have hK : Ring.KrullDimLE 1 Γ(Y, ⊤) := Ring.krullDimLE_iff.2 (by simp [hd])
  have hmax (P : PrimeSpectrum Γ(Y, ⊤)) : P.asIdeal.height = 1 ↔ P.asIdeal.IsMaximal := by
    constructor
    · intro h
      refine Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hK _ (fun h0 => ?_) P.isPrime
      rw [h0, Ideal.height_bot] at h
      exact zero_ne_one h
    · intro h
      have h1 : P.asIdeal.height ≤ 1 := by
        have := (Ideal.height_le_ringKrullDim_of_ne_top h.ne_top).trans_eq hd
        exact_mod_cast this
      refine le_antisymm h1 (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
      have h2 : P.asIdeal = ⊥ := by
        simpa [IsDomain.minimalPrimes_eq_singleton_bot] using Ideal.height_eq_zero_iff.1 h0
      have h3 : IsField Γ(Y, ⊤) := Ring.isField_iff_maximal_bot.2 (h2 ▸ h)
      rw [ringKrullDim_eq_zero_of_isField h3] at hd
      exact zero_ne_one hd
  let i : MaximalSpectrum Γ(Y, ⊤) → Y := fun m => hU.fromSpec m.toPrimeSpectrum
  have hi : Function.Injective i :=
    hU.fromSpec.isOpenEmbedding.injective.comp (MaximalSpectrum.toPrimeSpectrum_injective)
  have hp (m) : hU.primeIdealOf ⟨i m, trivial⟩ = m.toPrimeSpectrum :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq' _ (Set.range i) Set.univ ?_, finsum_mem_range hi]
  · refine finsum_congr fun m => ?_
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨i m, trivial⟩ : (⊤ : Y.Opens))
    have hl : IsLocalization.AtPrime (Y.presheaf.stalk (i m)) m.asIdeal := by
      have := hU.isLocalization_stalk ⟨i m, trivial⟩
      convert this
      exact congrArg PrimeSpectrum.asIdeal (hp m).symm
    have h1 : Order.coheight (i m) = 1 := by
      have := hc (i m)
      rw [hp, (hmax _).2 m.isMaximal] at this
      exact_mod_cast this
    have hb' : algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective _ m.asIdeal.primeCompl_le_nonZeroDivisors)).2 hb
    have h2 := ord_algebraMap h1 hb'
    rw [length_quot_eq m.asIdeal.primeCompl] at h2
    have h3 : algebraMap Γ(Y, ⊤) Y.functionField b =
        algebraMap _ Y.functionField (algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b) :=
      (algebraMap_germ (Opens.mem_top (i m)) b).symm
    have h4 : Nat.card (Y.residueField (i m)) = Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal) :=
      Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m.asIdeal
        (Y.presheaf.stalk (i m))).symm.toEquiv
    rw [h3, h2, h4, Int.cast_natCast]
  · intro z hz
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have h1 : Order.coheight z = 1 := by
      by_contra h
      exact hz (by simp [Scheme.ord_eq_zero_of_coheight_neq_one h])
    have h2 := hc z
    rw [h1] at h2
    exact ⟨⟨_, (hmax (hU.primeIdealOf ⟨z, trivial⟩)).1 (by exact_mod_cast h2.symm)⟩,
      hU.fromSpec_primeIdealOf ⟨z, trivial⟩⟩

end GlobalTheory.AffineCurveSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveFinsumOrdLogEqLocalLengthsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineArithmeticCurve_finsum_ord_log_eq_localLengths : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), b ≠ 0 → ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ m : MaximalSpectrum Γ(Y, ⊤), ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl (Γ(Y, ⊤) ⧸ Ideal.span {b}))).toNat : ℝ) * Real.log (Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal)) := by
  first | exact @GlobalTheory.AffineCurveSum.finsum_ord_eq | exact GlobalTheory.AffineCurveSum.finsum_ord_eq | (intros; apply GlobalTheory.AffineCurveSum.finsum_ord_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveSumComplexPointsLogEqRingHo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveSumComplexPointsLogEqRingHo
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AffCurveSum

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsAffine Y] {q : Y ⟶ Sp k}

def evTop (y : Σ σ : k →+* ℂ, CxPts q σ) : Γ(Y, ⊤) →+* ℂ := evHom (y := y.2) mem_ptsIn_top

theorem evTop_apply (y : Σ σ : k →+* ℂ, CxPts q σ) (b : Γ(Y, ⊤)) :
    evTop y b = ev q y.1 ⊤ b y.2 := (ev_eq mem_ptsIn_top b).symm

theorem evTop_bijective : Function.Bijective (evTop (q := q)) := by
  constructor
  · rintro ⟨σ, y⟩ ⟨σ', y'⟩ h
    have hσ : σ = σ' := RingHom.ext fun a => by
      have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ (algX q ⊤ a)) h
      simp only [evTop_apply, ev_algX mem_ptsIn_top] at this
      exact this
    subst hσ
    have hy : y = y' := Subtype.ext (Points.ext_of_valR (isAffineOpen_top Y)
      (mem_ptsIn_top : y ∈ ptsIn q σ ⊤) (mem_ptsIn_top : y' ∈ ptsIn q σ ⊤) fun f => by
        have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ f) h
        simp only [evTop_apply] at this
        exact this)
    rw [hy]
  · intro τ
    refine ⟨⟨τ.comp (algX q ⊤), ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ
      (fun _ => rfl)⟩, ?_⟩
    ext f
    rw [evTop_apply]
    exact ev_ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ (fun _ => rfl) f

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsAffine Y] (q : Y ⟶ Sp k),
    IsArithVar q 0 → ∀ b : Γ(Y, ⊤), ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        ∑ᶠ τ : Γ(Y, ⊤) →+* ℂ, Real.log ‖τ b‖ := by
  intro k _ Y _ _ q hq b
  have := hq.finite_emb
  have (σ : k →+* ℂ) := ArchDimZero.finite_cxPts hq σ
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  let e := Equiv.ofBijective _ (evTop_bijective (q := q))
  have : Finite (Γ(Y, ⊤) →+* ℂ) := .of_equiv _ e
  let := Fintype.ofFinite (Γ(Y, ⊤) →+* ℂ)
  have hv (σ : k →+* ℂ) (y : CxPts q σ) :
      ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y = evTop ⟨σ, y⟩ b := by
    exact (ratVal_fnOf mem_ptsIn_top _ b).trans (evTop_apply ⟨σ, y⟩ b).symm
  simp only [hv, finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_sigma (fun x : (Σ σ : k →+* ℂ, CxPts q σ) => Real.log ‖evTop x b‖)]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.AffCurveSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveSumComplexPointsLogEqRingHoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineArithmeticCurve_sum_complexPoints_log_eq_ringHoms : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ = ∑ᶠ τ : Γ(Y, ⊤) →+* ℂ, Real.log ‖τ b‖ := by
  first | exact @GlobalTheory.AffCurveSum.main | exact GlobalTheory.AffCurveSum.main | (intros; apply GlobalTheory.AffCurveSum.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardEqFinsumLengthLocalizedMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardEqFinsumLengthLocalizedMaximal
namespace GlobalTheory.CardLength

variable {R : Type} [CommRing R]

noncomputable def lenAt (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q] : ℕ∞ :=
  Module.length (Localization.AtPrime w) (LocalizedModule w.primeCompl Q)

theorem lenAt_exact (w : Ideal R) [w.IsPrime] {N M P : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    lenAt w M = lenAt w N + lenAt w P :=
  Module.length_eq_add_of_exact (LocalizedModule.map w.primeCompl f)
    (LocalizedModule.map w.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

theorem lenAt_congr (w : Ideal R) [w.IsPrime] {M N : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] N) : lenAt w M = lenAt w N :=
  le_antisymm
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap)
      (LocalizedModule.map_injective _ _ e.injective))
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap)
      (LocalizedModule.map_injective _ _ e.symm.injective))

theorem lenAt_subsingleton (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : lenAt w Q = 0 :=
  Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl Q))

theorem lenAt_quot_ne (w m : Ideal R) [hw : w.IsMaximal] [hm : m.IsMaximal] (h : w ≠ m) :
    lenAt w (R ⧸ m) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (R ⧸ m))).2 ?_)
  have hnle : ¬ m ≤ w := fun hle => h (hm.eq_of_le hw.ne_top hle).symm
  obtain ⟨s, hsm, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  intro x
  refine ⟨s, hsw, ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact m.mul_mem_right _ hsm

theorem lenAt_quot_self (m : Ideal R) [hm : m.IsMaximal] : lenAt m (R ⧸ m) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (R ⧸ m))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ m.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

theorem card_eq_prod_lenAt : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : MaximalSpectrum R →₀ ℕ,
      (∀ w : MaximalSpectrum R, lenAt w.asIdeal Q = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.asIdeal) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn
  by_cases hQ : Subsingleton Q
  · refine ⟨0, fun w => ?_, ?_⟩
    · rw [lenAt_subsingleton]; simp
    · rw [Finsupp.prod_zero_index]; exact Nat.card_of_subsingleton 0
  · rw [not_subsingleton_iff_nontrivial] at hQ
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R (Q ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      have hnt : Nontrivial (Q ⧸ Q1) := IsSimpleModule.nontrivial R _
      have hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1) :=
        Submodule.card_eq_card_quotient_mul_card Q1
      have hfq : Finite (Q ⧸ Q1) := Finite.of_surjective _ Q1.mkQ_surjective
      have h1 : 1 < Nat.card (Q ⧸ Q1) := Finite.one_lt_card
      have h2 : 0 < Nat.card Q1 := Nat.card_pos
      have hlt : Nat.card Q1 < n := by
        rw [← hn, hcard]; nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt Q1 rfl
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.isMaximal
        rw [lenAt_exact w.asIdeal Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective
          (LinearMap.exact_subtype_mkQ Q1), hk1 w, lenAt_congr w.asIdeal e, Finsupp.add_apply,
          Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : MaximalSpectrum R) = w
        · subst hw
          rw [if_pos rfl, lenAt_quot_self]; simp
        · rw [if_neg hw, lenAt_quot_ne w.asIdeal m0
            (fun h => hw (MaximalSpectrum.ext h.symm))]; simp
      · have hz : ∀ w : MaximalSpectrum R, Nat.card (R ⧸ w.asIdeal) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : MaximalSpectrum R) (a c : ℕ), Nat.card (R ⧸ w.asIdeal) ^ (a + c) =
            Nat.card (R ⧸ w.asIdeal) ^ a * Nat.card (R ⧸ w.asIdeal) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) (hz _),
          pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]

theorem log_card_eq_finsum_length : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N]
    [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B,
      ((Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  intro B _ N _ _ _
  classical
  obtain ⟨k, hk, hc⟩ := card_eq_prod_lenAt (R := B) _ N rfl
  have hlen : ∀ m : MaximalSpectrum B, (Module.length (Localization.AtPrime m.asIdeal)
      (LocalizedModule m.asIdeal.primeCompl N)).toNat = k m := fun m => by
    have h := hk m
    unfold lenAt at h
    rw [h]; rfl
  simp_rw [hlen]
  rw [finsum_eq_sum_of_support_subset (s := k.support) _ ?_]
  · have h0 : (k.prod fun w j => Nat.card (B ⧸ w.asIdeal) ^ j) ≠ 0 := by
      rw [← hc]; exact Nat.card_pos.ne'
    rw [Finsupp.prod, Finset.prod_ne_zero_iff] at h0
    rw [hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro m hm
      exact_mod_cast h0 m hm
  · intro m hm
    rw [Function.mem_support] at hm
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0; apply hm; simp [h0]

end GlobalTheory.CardLength
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardEqFinsumLengthLocalizedMaximalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_card_eq_finsum_length_localized_maximal : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N] [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B, ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  first | exact @GlobalTheory.CardLength.log_card_eq_finsum_length | exact GlobalTheory.CardLength.log_card_eq_finsum_length | (intros; apply GlobalTheory.CardLength.log_card_eq_finsum_length <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotSpanEqFinsumLogNormEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotSpanEqFinsumLogNormEmbeddings
open scoped nonZeroDivisors

namespace GlobalTheory

namespace IndexNormEmb

theorem card_quot_span_eq (B : Type) [CommRing B] [IsDomain B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (b : B) (hb : b ≠ 0) : Nat.card (B ⧸ Ideal.span {b}) = (Algebra.norm ℤ b).natAbs := by
  classical
  rw [Algebra.norm_apply]
  let bs := Module.Free.chooseBasis ℤ B
  have := Submodule.natAbs_det_equiv ((Ideal.span {b}).restrictScalars ℤ)
    (bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _))
  rw [show Nat.card (B ⧸ Ideal.span {b}) = Nat.card (B ⧸ (Ideal.span {b}).restrictScalars ℤ) from rfl,
    ← this]
  congr
  refine bs.ext fun i => ?_
  simp
  show ((bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _) (bs i) : Ideal.span {b}) : B) = b * bs i
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Ideal.basisSpanSingleton_apply]

theorem injective_of_ringHom (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (τ : B →+* ℂ) : Function.Injective τ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have h : (RingHom.ker τ).comap (algebraMap ℤ B) = ⊥ := by
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have := Ideal.eq_bot_of_comap_eq_bot h
  have hx' : x ∈ RingHom.ker τ := hx
  rw [this] at hx'
  simpa using hx'

noncomputable def embEquiv (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] :
    (FractionRing B →ₐ[ℚ] ℂ) ≃ (B →+* ℂ) where
  toFun σ := (σ : FractionRing B →+* ℂ).comp (algebraMap B (FractionRing B))
  invFun τ := (IsFractionRing.lift (K := FractionRing B) (injective_of_ringHom B τ)).toRatAlgHom
  left_inv σ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext B⁰
    ext x
    simp
  right_inv τ := by
    ext x
    simp

theorem log_card_quot_span_eq_finsum_log_norm : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B),
    b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧
      Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  intro B _ _ _ _ b hb
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B ℤ⁰) (FractionRing B) :=
    Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors ℤ B (FractionRing B)
  haveI : IsScalarTower ℤ ℚ (FractionRing B) :=
    ⟨fun n q x => by rw [zsmul_eq_mul, zsmul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_mul, map_intCast, mul_assoc]⟩
  haveI : @IsScalarTower ℤ ℚ (FractionRing B) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : FiniteDimensional ℚ (FractionRing B) := Module.Finite.of_isLocalization ℤ B ℤ⁰
  have hcard := card_quot_span_eq B b hb
  have hN0 : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.mpr hN0), ?_⟩
  have hN : algebraMap ℤ ℂ (Algebra.norm ℤ b) =
      ∏ σ : FractionRing B →ₐ[ℚ] ℂ, σ (algebraMap B (FractionRing B) b) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ ℂ,
      ← Algebra.norm_localization ℤ (Sₘ := FractionRing B) ℤ⁰, Algebra.norm_eq_prod_embeddings]
  have hx : algebraMap B (FractionRing B) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr hb
  rw [← finsum_comp_equiv (embEquiv B), finsum_eq_sum_of_fintype]
  change _ = ∑ σ : FractionRing B →ₐ[ℚ] ℂ, Real.log ‖σ (algebraMap B (FractionRing B) b)‖
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hx)),
    ← norm_prod, ← hN, hcard, Nat.cast_natAbs, eq_intCast, Complex.norm_intCast, Int.cast_abs]

end IndexNormEmb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotSpanEqFinsumLogNormEmbeddingsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B), b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧ Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  first | exact @GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | exact GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | (intros; apply GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunction
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveProd

theorem product_formula_curve : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  intro k _ Y _ _ q hq f hf
  obtain ⟨hAff, hFin⟩ := GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int k Y q hq
  have := hAff
  have := hFin
  have : Module.Finite ℤ k := hq.finite
  have hgen : genericPoint Y ∈ (⊤ : Y.Opens) := trivial
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : CharZero Γ(Y, ⊤) := (flat_int_iff_charZero (q ≫ spMap (Int.castRingHom k))).1 hq.flat
  have : IsFractionRing Γ(Y, ⊤) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)

  have finHom : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], Finite (B →+* ℂ) := by
    intro B _ _
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
    have hint : ∀ x : B, IsIntegral ℤ x := fun x => Algebra.IsIntegral.isIntegral x
    choose p hpm hp using hint
    let T : Set (s → ℂ) :=
      Set.pi Set.univ fun x => {z : ℂ | ((p x).map (Int.castRingHom ℂ)).IsRoot z}
    have hT : T.Finite :=
      Set.Finite.pi fun x => Polynomial.finite_setOfPred_isRoot ((hpm x).map _).ne_zero
    have hmem : ∀ φ : B →+* ℂ, (fun x : s => φ x) ∈ T := by
      intro φ x _
      show Polynomial.eval (φ (x : B)) ((p x).map (Int.castRingHom ℂ)) = 0
      rw [Polynomial.eval_map]
      rw [← show φ.comp (algebraMap ℤ B) = Int.castRingHom ℂ from RingHom.ext_int _ _,
        ← Polynomial.hom_eval₂, hp x, map_zero]
    let F : (B →+* ℂ) → T := fun φ => ⟨fun x => φ x, hmem φ⟩
    have hF : Function.Injective F := by
      intro φ ψ h
      have h' : Set.EqOn φ.toAddMonoidHom.toIntLinearMap ψ.toAddMonoidHom.toIntLinearMap (s : Set B) := by
        intro x hx
        have := congrArg (fun t : T => t.1 ⟨x, hx⟩) h
        simpa [F] using this
      have hl := LinearMap.ext_on hs h'
      ext x
      exact LinearMap.congr_fun hl x
    have : Finite T := hT.to_subtype
    exact Finite.of_injective F hF

  have finZero : ∀ c : Γ(Y, ⊤), Finite (Γ(Y, ⊤) ⧸ Ideal.span {c}) →
      {z : Y | z ∉ Y.basicOpen c}.Finite := by
    intro c _
    have hS : (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {c})))).Finite :=
      Set.finite_range _
    refine (hS.preimage fun _ _ _ _ h => Y.toSpecΓ.isOpenEmbedding.injective h).subset ?_
    intro z hz
    have h1 : Y.toSpecΓ z ∉ PrimeSpectrum.basicOpen c := by
      intro h
      apply hz
      rw [← Scheme.toSpecΓ_preimage_basicOpen]
      exact h
    show Y.toSpecΓ z ∈ Set.range _
    apply (Set.ext_iff.1 (range_comap_of_surjective _ (Ideal.Quotient.mk (Ideal.span {c}))
      Ideal.Quotient.mk_surjective) _).2
    have h2 : c ∈ (Y.toSpecΓ z).asIdeal := by
      by_contra h
      exact h1 h
    rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff.2 h2

  have hgb : ∀ c : Γ(Y, ⊤), c ≠ 0 → genericPoint Y ∈ Y.basicOpen c := by
    intro c hc
    by_contra h
    apply hc
    rw [← basicOpen_eq_bot_iff (X := Y) (U := ⊤) c, ← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
    rintro ⟨x, hx⟩
    exact h (gen_mem hx)

  have hsupp : ∀ c : Γ(Y, ⊤), c ≠ 0 → (Function.support fun z =>
      (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
        Real.log (Nat.card (Y.residueField z))).Finite := by
    intro c hc
    refine (finZero c (GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc).1).subset ?_
    intro z hz hzc
    apply hz
    have hu : UnitAt z (algebraMap Γ(Y, ⊤) Y.functionField c) :=
      (unitAt_fnOf_iff (U := ⊤) trivial hgen c).2 hzc
    simp only
    rw [hu.ord_eq_zero]
    simp

  have key : ∀ c : Γ(Y, ⊤), c ≠ 0 →
      ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField c) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) =
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField c) y‖ := by
    intro c hc
    obtain ⟨hfq, hlog⟩ := GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings Γ(Y, ⊤) c hc
    have := hfq
    rw [GlobalTheory.T.affineArithmeticCurve_finsum_ord_log_eq_localLengths k Y q hq c hc, ← GlobalTheory.T.log_card_eq_finsum_length_localized_maximal Γ(Y, ⊤) (Γ(Y, ⊤) ⧸ Ideal.span {c}), hlog,
      GlobalTheory.T.affineArithmeticCurve_sum_complexPoints_log_eq_ringHoms k Y q hq c]

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective Γ(Y, ⊤) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hf
  have hinj := IsFractionRing.injective Γ(Y, ⊤) Y.functionField
  have ha'0 : algebraMap Γ(Y, ⊤) Y.functionField a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  have hb'0 : algebraMap Γ(Y, ⊤) Y.functionField b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hord : ∀ z, Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z =
        Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z -
          Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z := by
    intro z
    have h := Scheme.ord_mul (x := z) (div_ne_zero ha'0 hb'0) hb'0
    rw [div_mul_cancel₀ _ hb'0] at h
    omega

  have hpt : ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖ -
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    intro σ y
    have hg : under y = genericPoint Y := GlobalTheory.TwistTop.under_eq_genericPoint hq y
    have hua : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen a).2 (hgb a ha0)
    have hub : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [hg]
      exact (unitAt_fnOf_iff (U := ⊤) hgen hgen b).2 (hgb b hb0)
    have huq : UnitAt (under y) (algebraMap Γ(Y, ⊤) Y.functionField a /
        algebraMap Γ(Y, ⊤) Y.functionField b) := by
      rw [div_eq_mul_inv]
      exact hua.mul hub.inv
    have hm : ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y =
        ratVal (algebraMap Γ(Y, ⊤) Y.functionField a / algebraMap Γ(Y, ⊤) Y.functionField b) y *
          ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y := by
      rw [← ratVal_mul huq.regAt hub.regAt, div_mul_cancel₀ _ hb'0]
    rw [hm, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero huq))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hub))]
    ring
  have hL : ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) =
      (∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField a) z : ℝ) *
          Real.log (Nat.card (Y.residueField z))) -
        ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) *
          Real.log (Nat.card (Y.residueField z)) := by
    rw [← finsum_sub_distrib (hsupp a ha0) (hsupp b hb0)]
    refine finsum_congr fun z => ?_
    rw [hord z]
    push_cast
    ring
  have hR : ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a /
      algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
      (∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField a) y‖) -
        ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
          Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ := by
    have : Finite (k →+* ℂ) := finHom k
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    refine finsum_congr fun σ => ?_
    have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
    rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun y => hpt σ y
  rw [hL, hR, key a ha0, key b hb0]

end GlobalTheory.CurveProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaArithmeticCurveRationalFunctionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFormula_arithmeticCurve_rationalFunction : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ f : Y.functionField, f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, Real.log ‖ratVal f y‖ := by
  first | exact @GlobalTheory.CurveProd.product_formula_curve | exact GlobalTheory.CurveProd.product_formula_curve | (intros; apply GlobalTheory.CurveProd.product_formula_curve <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveIndep

variable {Y : Scheme.{0}} [IsIntegral Y] {L : LB Y}

theorem exists_ratio (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') : ∃ f : Y.functionFieldˣ, ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f := by
  obtain ⟨i₀, h₀⟩ := exists_chart hL (genericPoint Y)
  refine ⟨(r i₀)⁻¹ * r' i₀, fun i hi => Units.ext ?_⟩
  have e := hr i i₀ ⟨hi, h₀⟩
  have e' := hr' i i₀ ⟨hi, h₀⟩
  have h0 : (r i₀ : Y.functionField) ≠ 0 := (r i₀).ne_zero
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [e', e]
  field_simp

theorem div_eq_add_principal (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ} (hr : IsRatSec L r)
    (hr' : IsRatSec L r') (f : Y.functionFieldˣ) (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) :
    divOfRatSec hL hr' = divOfRatSec hL hr + CartierDiv.principal f :=
  (presents_divOfRatSec hL hr').unique ⟨hL, hr', fun i x hx => by
    rw [hf i (gen_mem hx)]
    exact ((presents_divOfRatSec hL hr).add_principal f).isEqn i x hx⟩

theorem mult_eq_add_ord [IsLocallyNoetherian Y] (hL : L.IsLB) {r r' : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hr' : IsRatSec L r') (f : Y.functionFieldˣ)
    (hf : ∀ i, genericPoint Y ∈ L.U i → r' i = r i * f) (z : Y) :
    (divOfRatSec hL hr').mult z = (divOfRatSec hL hr).mult z + Scheme.ord (f : Y.functionField) z := by
  rw [div_eq_add_principal hL hr hr' f hf, CartierDiv.mult_add,
    (CartierDiv.isEqn_principal f z).mult_eq]

end GlobalTheory.CurveIndep

namespace GlobalTheory.CurveIndep


open Classical in
theorem mixArch_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    (L : Fin 0 → HermLB q) (N : HermLB q) {r : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r) :
    mixArch L N hr = (HermLB.triv q).archInt N 0 hr := by
  have h (n : Fin 0 → ℤ) : (comb L n).archInt N 0 hr = (HermLB.triv q).archInt N 0 hr := by
    have e : comb L n = HermLB.triv q := by simp [comb]
    rw [e]
  have e (S : Finset (Fin 0)) : S.card = 0 := by simp [Subsingleton.elim S ∅]
  simp [mixArch, FibreProj.pol, h, e]

theorem archInt_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  intro k _ Y _ _ q hA hd N L r hr r' hr'
  obtain ⟨f, hf⟩ := exists_ratio N.isLB hr hr'
  have := hA.isNoetherian
  set c : Y → ℝ := fun z => Real.log (Nat.card (Y.residueField z)) with hc
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * c z).Finite :=
    (CartierDiv.finite_support_mult D).subset fun z hz h0 => hz (by simp [h0])
  have hord (z : Y) : Scheme.ord (f : Y.functionField) z = (CartierDiv.principal f).mult z :=
    ((CartierDiv.isEqn_principal f z).mult_eq).symm
  have hsum : ∑ᶠ z, ((N.div hr').mult z : ℝ) * c z =
      ∑ᶠ z, ((N.div hr).mult z : ℝ) * c z + ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z := by
    simp_rw [hord]
    rw [← finsum_add_distrib (hfin _) (hfin _)]
    refine finsum_congr fun z => ?_
    rw [HermLB.div, HermLB.div, mult_eq_add_ord N.isLB hr hr' f hf z, hord]
    push_cast
    ring
  unfold recVal
  rw [hsum, mixArch_zero, mixArch_zero]
  rcases GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hA (0 + 1) hd with ⟨l, hl, ⟨alg⟩, hemp⟩ | ⟨e, he, hq⟩
  · have h0 : ∑ᶠ z, (Scheme.ord (f : Y.functionField) z : ℝ) * c z = 0 :=
      @GlobalTheory.T.principalDivisor_degree_zero_finiteField_curve k _ Y _ _ q hA hd l hl alg (f : Y.functionField) f.ne_zero
    rw [h0, archInt_eq_zero hemp, archInt_eq_zero hemp]
    ring
  · obtain rfl : e = 0 := by omega
    have := hq.finite_emb
    rw [GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r hr,
      GlobalTheory.ArchDimZero.main k Y q hq N (HermLB.triv q) r' hr',
      GlobalTheory.T.productFormula_arithmeticCurve_rationalFunction k Y q hq (f : Y.functionField) f.ne_zero]
    have hlog (σ : k →+* ℂ) (y : CxPts q σ) : logNorm (N.φ σ) r' y =
        Real.log ‖ratVal (f : Y.functionField) y‖ + logNorm (N.φ σ) r y := by
      have hy := GlobalTheory.TwistTop.under_eq_genericPoint hq y
      have hreg (g : Y.functionField) : RegAt (under y) g := by
        rw [hy]; exact regAt_genericPoint g
      have hunit (g : Y.functionFieldˣ) : UnitAt (under y) (g : Y.functionField) := by
        rw [hy]; exact unitAt_genericPoint g.ne_zero
      have hi : genericPoint Y ∈ N.B.U (pick (N.φ σ).isLB y) :=
        gen_mem (mem_ptsIn.1 (mem_pick (N.φ σ).isLB y))
      simp only [logNorm]
      rw [hf _ hi, Units.val_mul, ratVal_mul (hreg _) (hreg _), norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit _)))
          (norm_ne_zero_iff.2 (ratVal_ne_zero (hunit f)))]
      ring
    have hσ (σ : k →+* ℂ) : ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r' y =
        ∑ᶠ y : CxPts q σ, Real.log ‖ratVal (f : Y.functionField) y‖ + ∑ᶠ y : CxPts q σ, logNorm (N.φ σ) r y := by
      have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
      simp_rw [hlog σ]
      exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
    simp_rw [hσ]
    rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    ring

end GlobalTheory.CurveIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_curve_degree_independent_of_section : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (0 + 1 : ℕ) → ∀ (N : HermLB q) (L : Fin 0 → HermLB q) (r : N.B.ι → Y.functionFieldˣ) (hr : IsRatSec N.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr = recVal (fun z => Real.log (Nat.card (Y.residueField z))) L N hr' := by
  first | exact @GlobalTheory.CurveIndep.main | exact GlobalTheory.CurveIndep.main | (intros; apply GlobalTheory.CurveIndep.main <;> assumption)
end
