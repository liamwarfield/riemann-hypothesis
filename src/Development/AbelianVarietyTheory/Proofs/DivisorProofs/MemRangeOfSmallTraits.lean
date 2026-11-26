module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleComplexExistenceJetsKeyValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateTermsJetsBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValuesDetOmegaDeltaUnitAffineOpens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCExtComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteIsAlgClosedComplexRatVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RatNorm

open Cardinal IsLocalRing

theorem mk_le_of_dense {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

end GlobalTheory.RatNorm

namespace GlobalTheory.MBLow

open Cardinal IsLocalRing GlobalTheory.RatNorm ReciprocityTheory.ChartRestriction.G.DVR

end GlobalTheory.MBLow
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.KeySmall

theorem norm_toF_unit {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] (hC : CExt V I C) (u : Vˣ) : ‖toF V C u‖ = 1 := by
  have h1 : ‖toF V C u‖ ≤ 1 := hC.1 u
  have h2 : ‖toF V C ↑u⁻¹‖ ≤ 1 := hC.1 ↑u⁻¹
  have h3 : toF V C u * toF V C ↑u⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have h4 : ‖toF V C u‖ * ‖toF V C ↑u⁻¹‖ = 1 := by rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg (toF V C u), norm_nonneg (toF V C ↑u⁻¹)]

theorem c_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := GlobalTheory.T.genericThetaExpansion_scalar_ne_zero

theorem level_labels : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := GlobalTheory.T.levelStructure_baseChange_labels_torsion

theorem jc_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := GlobalTheory.T.torusExtDualNumberTermValue_smul

theorem fst_indep : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := GlobalTheory.T.section_value_eq_at_first_order_of_tangents

theorem deform_of_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := GlobalTheory.T.powerSeriesDeformation_of_boundedLatticeSeries

end GlobalTheory.UMin.KeySmall

namespace GlobalTheory.UMin.KeySmall


set_option maxHeartbeats 4000000 in
theorem norm_key_eq_one : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → Nonempty (C ≃+* ℂ) →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) →
      ‖c‖ ^ 8 * ‖algebraMap (FractionRing V) C (κ (FractionRing V) x : FractionRing V)‖ = 1 := by
  intro κ hR4
  obtain ⟨hHom, hFun, hTh1, hFamU⟩ := id hR4
  intro V _ _ _ _ hcomp D x G _ _ hSA U w₀ hNW y hy hyv C _ _ _ _ _ _ hCE hiso N ν hInt th ϑ c hOn hExp hFV
  obtain ⟨e⟩ := hiso

  set K := FractionRing V

  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.transfer_of_rule4' κ hR4 x.P.g 3 Nat.prime_three ⟨1, rfl⟩
  set j := max j₀ 1 with hj
  set m := 3 ^ j with hm
  have hmOdd : Odd m := Odd.pow ⟨1, rfl⟩
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by norm_num)
  have hm2 : 2 ≤ m ^ 2 := by
    have : 3 ≤ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    nlinarith

  obtain ⟨vB, r, bX, σ, y', gm₀, gm, hy', hAd, hT⟩ := GlobalTheory.T.exists_adaptedLieBasis_torusExtensionModel V hcomp D x.P G hSA U C hCE N ν hInt
  have hvec := fun j => GlobalTheory.T.existsUnique_genericFibreDualNumberPoint_of_model V hcomp D x.P G hSA U C (y' j)
  choose yA hyA _ using fun j => (hvec j).1
  choose v' hv'o _ using fun j => (hvec j).2.1
  have hyAs : ∀ j, yA j ≫ (snd (TFK (R := V) C) x.P.A).left =
      spMap (dualMap (algebraMap (FractionRing V) C)) ≫ (v' j).left := fun j => (hvec j).2.2 (v' j) (yA j) (hv'o j) (hyA j)
  obtain ⟨-, -, -, hgp, -⟩ := GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D x.P G U.toUnifPre
  obtain ⟨hv', u, hu⟩ := GlobalTheory.T.thetaKeyRule_lieBasisChange_unit_factor κ hHom V (FractionRing V) (algebraMap V (FractionRing V)) x G _ hgp y y' v' hy hy' hyv hv'o
  set x' : KeyIn (FractionRing V) := ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ with hx'

  obtain ⟨xC, hgC, io, hPB, hW, hJ⟩ := GlobalTheory.T.exists_keyDatumBaseChange_thetaJets (FractionRing V) C (algebraMap (FractionRing V) C) x'
  have hκC : (κ C xC : C) = algebraMap (FractionRing V) C (κ (FractionRing V) x') := hFun _ _ _ x' xC hPB
  obtain ⟨ζ, ⟨lev⟩⟩ := GlobalTheory.T.exists_symplecticLevel_algClosed_charZero C xC.P (m ^ 2) (by omega)
  obtain ⟨hprim, hadd, hinj, hsurj, hweil⟩ :=
    level_labels (FractionRing V) C (algebraMap (FractionRing V) C) x'.P xC.P io hW x.P.g (m ^ 2) hgC ζ lev hm2
  set pt : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → (TFK (R := V) C ⟶ x.P.A) := fun a => io.symm (levelPoint lev hgC a) with hpt
  obtain ⟨p, Q, hQL, hpq⟩ := GlobalTheory.T.torsionSymplecticLabels_of_levelStructure V hcomp D x.P G hSA U C hCE N ν hInt x.P.g (m ^ 2) (by omega) ζ pt hprim
    hadd hinj hsurj hweil

  choose Θ tt ss ff hfam using fun a => GlobalTheory.T.symmetricThetaTranslates_expand_seriesFamilies V hcomp D x.P G hSA U C hCE N ν hInt w₀ x.rig hNW th ϑ c hExp hFV
    m hmOdd (p a) (Q a) (pt a) (hpq a).1 (hpq a).2
  have hc : c ≠ 0 := c_ne_zero V hcomp D x G hSA U w₀ hNW C hCE N ν th ϑ c hOn hExp hFV
  set s' : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fam D.toPre C (m ^ 2) := fun a => c⁻¹ • ss a with hs'
  have hs'V : ∀ a, ν.FamV (s' a) (ff a) := fun a => by
    have := GlobalTheory.WeilValues.famV_smul ν (hfam a).2.2.2.2 c⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

  have hch : ∃ i₀, ⊤ ≤ (jFK (R := V) C ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ := by
    have h : (jFK (R := V) C ≫ eSec x.P.A) (default : PrimeSpectrum C) ∈ (⨆ i, x.P.L.U i) := by
      rw [x.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    refine ⟨i, fun z _ => ?_⟩
    obtain rfl : z = (default : PrimeSpectrum C) := Subsingleton.elim _ _
    exact hi
  obtain ⟨i₀, hi₀⟩ := hch
  choose cj hcj using fun j => GlobalTheory.T.tangentVector_section_value_eq_expansion_sum V hcomp D x.P G hSA U C hCE N ν hInt w₀ x.rig hNW (y' j) (gm₀ j) (gm j)
    (yA j) (hy'.1 j) (hT j).1 (hT j).2.2 (hyA j) (m ^ 2) i₀ hi₀
  set j₁ : Fin x.P.g := ⟨0, x.g_pos⟩
  set Sf : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → C :=
    fun a j => ∑' α, (jc ν (ss a) (gm j) α).fst / ν.rg ^ (m ^ 2) with hSf
  set Ss : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → C :=
    fun a j => ∑' α, (jc ν (ss a) (gm j) α).snd / ν.rg ^ (m ^ 2) with hSs
  have hind : ∀ a j, Sf a j = Sf a j₁ := fun a j =>
    fst_indep (FractionRing V) C x.P x.rig (m ^ 2) (tt a) i₀ hi₀ (v' j) (v' j₁) (hv'.1 j) (hv'.1 j₁) (yA j) (yA j₁)
      (hyA j).1 (hyAs j) (hyA j₁).1 (hyAs j₁) _ _ _ _ (hcj j (tt a) (ss a) (hfam a).2.2.1).2.2
      (hcj j₁ (tt a) (ss a) (hfam a).2.2.1).2.2
  have hTJ : ThJetT x'.P x'.rig m (spMap (algebraMap (FractionRing V) C)) th pt yA (fun a => Sf a j₁) Ss := by
    refine ⟨Θ, tt, i₀, cj, fun a => ⟨(hfam a).1, (hfam a).2.1⟩, hi₀, fun a j => ?_⟩
    have h := (hcj j (tt a) (ss a) (hfam a).2.2.1).2.2
    have e := hind a j
    simp only [hSf] at e
    rw [e] at h
    exact h
  have hJC := hJ m th _ pt yA (fun a => Sf a j₁) Ss hOn (fun j => ⟨(hyA j).1, hyAs j⟩) hTJ
  have hio : (fun a => io (pt a)) = levelPoint lev hgC := funext fun a => io.apply_symm_apply _
  rw [hio] at hJC
  obtain ⟨th'', hth'', hsc, hJsc⟩ := GlobalTheory.T.thetaKeyRule_scale_section_pow_eight κ hHom C xC c⁻¹ (inv_ne_zero hc)
  have hJ'' := hJsc x.P.g hgC m _ (levelPoint lev hgC) _ _ hJC
  set x'' : KeyIn C := ⟨xC.P, xC.g_pos, xC.rig, xC.rig_gen, th'', hth'', xC.v, xC.basis⟩ with hx''

  have hadm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  obtain ⟨q, hq⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase V _ hadm D C hCE N ν hInt
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨hrg, hdisc⟩ := GlobalTheory.T.degenerationValues_norms_eq_uniformizer_zpow V ϖ hϖ D C hCE N ν hInt
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have ht1 : ‖toF V C ϖ‖ < 1 := hCE.2 ϖ hϖm
  have ht0 : toF V C ϖ ≠ 0 := by
    intro h
    have hinj : Function.Injective (toF V C) :=
      (algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))
    exact hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨β, π, hπ0, hπ1, hfinβ, hexp⟩ := GlobalTheory.T.exists_integralForm_parameter_of_discreteNorms C N q (toF V C ϖ) hq ht0 ht1 hdisc m hm1
  choose bd hbd using fun a j => GlobalTheory.T.thetaTranslateTerms_jets_bounded V D C hCE N ν hInt q hq m hmOdd (Q a) (s' a) (ff a) (hs'V a)
    (hfam a).2.2.2.1 (gm₀ j) (gm j) (hT j).2.1 (hT j).2.2
  haveI : NeZero (m ^ 2) := ⟨by omega⟩
  set B : ℝ := ∑ a, ∑ j, |bd a j| with hB
  have hbB : ∀ a j, bd a j ≤ B := fun a j =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun j => |bd a j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun a => ∑ j, |bd a j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)))
  obtain ⟨k₀, hBK, hk₀⟩ := GlobalTheory.T.exists_abelianKeyValue_norm_one κ hR4 V D.toPre C hCE N ν hInt vB hAd.1
  have hAF := GlobalTheory.T.archimedeanExistence_of_complex_isomorphic_field κ hFun (GlobalTheory.T.keyRule_complex_existence_jets_key_value κ hR4)
  obtain ⟨ε, hε, hAε⟩ := hAF V D.toPre D.psi_even D.tau_bimult C e N ν x.P.g r m (m ^ 2) x.g_pos hmOdd dvd_rfl β ζ Q hQL
    s' (fun a => ⟨ff a, hs'V a, (hfam a).2.2.2.1⟩) vB bX σ gm hAd k₀ hBK
  set nn : N.X → ℕ := fun α => (β.be α α / (2 * m ^ 2)).toNat with hnn
  set aa : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → N.X → C :=
    fun a α => (jc ν (s' a) (gm j₁) α).fst / ν.rg ^ (m ^ 2) with haa
  set bb : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → N.X → C :=
    fun a j α => (jc ν (s' a) (gm j) α).snd / ν.rg ^ (m ^ 2) with hbb
  have hSa : ∀ a, c⁻¹ * Sf a j₁ = ∑' α, aa a α := fun a => by
    rw [hSf, ← tsum_mul_left]
    congr 1
    funext α
    simp [haa, hs', jc_smul, div_eq_mul_inv, _root_.mul_assoc]
  have hSb : ∀ a j, c⁻¹ * Ss a j = ∑' α, bb a j α := fun a j => by
    rw [hSs, ← tsum_mul_left]
    congr 1
    funext α
    simp [hbb, hs', jc_smul, div_eq_mul_inv, _root_.mul_assoc]
  have hJ3 : ThJet x'' hgC m (levelPoint lev hgC) (fun i => ∑' α, aa i α) (fun i j => ∑' α, bb i j α) := by
    have e1 : (fun i => ∑' α, aa i α) = fun i => c⁻¹ * Sf i j₁ := funext fun i => (hSa i).symm
    have e2 : (fun i j => ∑' α, bb i j α) = fun i j => c⁻¹ * Ss i j := funext fun i => funext fun j => (hSb i j).symm
    rw [e1, e2]
    exact hJ''
  have hba : ∀ i α, ‖aa i α‖ ≤ B * ‖π‖ ^ nn α := fun i α => by
    have h := ((hbd i j₁) α).1
    rw [hexp α] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hbB i j₁) (pow_nonneg (norm_nonneg _) _))
  have hbb' : ∀ i j α, ‖bb i j α‖ ≤ B * ‖π‖ ^ nn α := fun i j α => by
    have h := ((hbd i j) α).2
    rw [hexp α] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hbB i j) (pow_nonneg (norm_nonneg _) _))
  have hDef : Deform κ (e : C →+* ℂ) x'' hgC m ζ lev k₀ := by
    refine deform_of_series κ C (e : C →+* ℂ) x'' x.P.g hgC m ζ lev k₀ N.X nn π B aa bb hπ0 hπ1 hfinβ hba hbb' hJ3
      ⟨ε, hε, fun u hu hu' => ?_⟩
    obtain ⟨hsm, x₀, hg₀, lev₀, ϑ₀, hϑ₀, hJ₀, hk⟩ := hAε u hu hu'
    refine ⟨⟨fun i => (hsm i j₁).1, fun i j => (hsm i j).2⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have e3 : ϑ₀ = fun i => ∑' α, (e : C →+* ℂ) (aa i α) * u ^ nn α := funext fun i => hϑ₀ i j₁
    rw [e3] at hJ₀
    exact hJ₀
  have hk := hj₀ j (le_max_left _ _) C (e : C →+* ℂ) x'' hgC ζ lev k₀ hDef
  have h1 : (κ C xC : C) = toF V C u * algebraMap (FractionRing V) C (κ (FractionRing V) x) := by
    rw [hκC, hu, map_mul]
    rfl
  have h2 : c⁻¹ ^ 8 * k₀ = toF V C u * algebraMap (FractionRing V) C (κ (FractionRing V) x) := by
    rw [← hk]
    exact hsc.trans h1
  have h3 := congrArg norm h2
  rw [norm_mul, norm_mul, norm_pow, norm_inv, hk₀, norm_toF_unit hCE u, _root_.mul_one, _root_.one_mul] at h3
  rw [← h3, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hc))]

end GlobalTheory.UMin.KeySmall

namespace GlobalTheory.UMin.KeySmall


open Cardinal IsLocalRing GlobalTheory.RatNorm in
set_option maxHeartbeats 800000 in
theorem exists_cExt_complex : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], #V ≤ 𝔠 →
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C)
      (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  intro V _ _ _ _ hcV
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let K := FractionRing V
  have hϖm : ϖ ∈ maximalIdeal V := hϖ.not_isUnit
  obtain ⟨w, hw, hw1, hwa⟩ := GlobalTheory.exists_absoluteValue_of_isDiscreteValuationRing V K hϖ.ne_zero hϖm
    (r := 1 / 2) (by norm_num) (by norm_num)

  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w (algebraMap V K ϖ))⁻¹, by
        rw [norm_inv]
        change 1 < (w (algebraMap V K ϖ))⁻¹
        rw [hwa]
        norm_num⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => hw x.ofAbs y.ofAbs
  let K₁ := UniformSpace.Completion (WithAbs w)
  letI : NontriviallyNormedField K₁ := completionNontriviallyNormedField (WithAbs w)
  haveI : IsUltrametricDist K₁ := IsUltrametricDist.of_normedAlgebra (WithAbs w)
  let K₂ := AlgebraicClosure K₁
  letI : NontriviallyNormedField K₂ := spectralNorm.nontriviallyNormedField K₁ K₂
  letI : NormedAlgebra K₁ K₂ := spectralNorm.normedAlgebra K₁ K₂
  haveI : IsUltrametricDist K₂ := IsUltrametricDist.of_normedAlgebra K₁
  let C := UniformSpace.Completion K₂
  letI : NontriviallyNormedField C := completionNontriviallyNormedField K₂
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra K₂
  haveI : IsAlgClosed C := isAlgClosed_of_denseRange (K := K₂) UniformSpace.Completion.denseRange_coe
  let i : K →+* C := (algebraMap K₂ C).comp ((algebraMap K₁ K₂).comp
    ((algebraMap (WithAbs w) K₁).comp (WithAbs.equiv w).symm.toRingHom))
  have hi : ∀ x : K, ‖i x‖ = w x := by
    intro x
    have h₁ : ∀ y : K₂, ‖algebraMap K₂ C y‖ = ‖y‖ := fun y => UniformSpace.Completion.norm_coe y
    have h₂ : ∀ y : K₁, ‖algebraMap K₁ K₂ y‖ = ‖y‖ := fun y => spectralNorm_extends y
    have h₃ : ∀ y : WithAbs w, ‖algebraMap (WithAbs w) K₁ y‖ = ‖y‖ :=
      fun y => UniformSpace.Completion.norm_coe y
    simp only [i, RingHom.comp_apply, h₁, h₂, h₃]
    rfl
  letI : Algebra K C := i.toAlgebra
  have hiV : Function.Injective (i.comp (algebraMap V K)) :=
    i.injective.comp (IsFractionRing.injective V K)
  haveI : CharZero C := charZero_of_injective_ringHom hiV

  have hc0 : #(WithAbs w) ≤ 𝔠 := by
    rw [Cardinal.mk_congr (WithAbs.equiv w).toEquiv, Cardinal.mk_fractionRing]; exact hcV
  have hc1 : #K₁ ≤ 𝔠 := mk_le_of_dense _ UniformSpace.Completion.denseRange_coe hc0
  have hc2 : #K₂ ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K₁ K₂).trans (max_le hc1 aleph0_le_continuum)
  have hc3 : #C ≤ 𝔠 := mk_le_of_dense _ UniformSpace.Completion.denseRange_coe hc2
  have hC : #C = 𝔠 := le_antisymm hc3 (continuum_le_cardinal_of_nontriviallyNormedField C)
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨fun a => ?_, fun a ha => ?_⟩, ?_⟩
  · change ‖i _‖ ≤ 1
    rw [hi]; exact (hw1 _).2 ⟨a, rfl⟩
  · change ‖i _‖ < 1
    rw [hi]
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    obtain ⟨s, rfl⟩ := ha
    rw [map_mul, map_mul, hwa]
    have := (hw1 (algebraMap V K s)).2 ⟨s, rfl⟩
    linarith
  · exact IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := C) (L := ℂ)
      (by rw [hC]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.1 (by rw [hC, Cardinal.mk_complex]))


open Cardinal GlobalTheory.KeyEven in
theorem key_unit_unif (κ : Rule) (hR : Rule4 κ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hcpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (hcV : #V ≤ 𝔠)
    (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre)
    (hN : GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig) (y : Fin x.P.g → (epsR V ⟶ G)) (hy : IsLieBasis y)
    (hvec : ∀ i, GlobalTheory.IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i))
    (σ : U.LG.L.Sec) (hNz : NzFib σ)
    (hMaps : GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull x.th U.gen.hom.left)
      (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V)))) :
    ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u := by
  obtain ⟨C, i1, i2, i3, i4, i5, i6, hC, hCC⟩ := exists_cExt_complex V hcV
  obtain ⟨N, ν, hInt⟩ := GlobalTheory.T.exists_degenerationData_values_ultrametric V hcpl D C hC
  obtain ⟨σ₁, f, th, ϑ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.integralSection_expands_integrally_genericFibre V hcpl D x.P G hG U w₀ hN.1 x.th σ hMaps C
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  obtain ⟨hv₁, -, -, -, hv₅, -⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨f', hf', -⟩ := hv₁ ϑ
  obtain ⟨c, rfl⟩ := hv₅ ϑ f' hf'
  have hc : ‖c‖ = 1 := GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries V hcpl D x.P G hG U σ σ₁ f hNz h1 h2 C hC N ν hInt ϑ c h5 hf'
  have e := norm_key_eq_one κ hR V hcpl D x G hG U w₀ hN y hy hvec C hC hCC N ν hInt th ϑ c h3 h4 hf'
  rw [hc, one_pow, _root_.one_mul] at e
  exact GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr V C hC _ e

theorem dualMapR_eq_of_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h1 : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := _root_.GlobalTheory.KeyEven.dualMapR_eq_of_map (R := R) (R' := R') f F h1 h2


open Cardinal GlobalTheory.KeyEven in
theorem key_unit_trait (κ : Rule) (hR : Rule4 κ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (hF : #V ≤ 𝔠)
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing V))
    (y : Fin x.P.g → (epsR V ⟶ G)) (hSA : IsSemiAbelian G) (hUn : HasUnif G L.L) (hLie : IsLieBasis y) (hNz : NzFib σ)
    (hKey : KeyOn (algebraMap V (FractionRing V)) x G L σ y) :
    ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u := by
  obtain ⟨D, A, U, e, he⟩ := hUn
  obtain ⟨φ, hφe, ψ, F, hPB, hψ, hRig, hTh, hF1, hF2, hv⟩ := hKey
  obtain ⟨θ, hθm, hθφ⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hPB

  obtain ⟨e', he', heR⟩ := GlobalTheory.T.exists_rescaled_iso_preserving_rigidification G U.LG L e he
  obtain ⟨σ', hσ', hnz⟩ := GlobalTheory.T.exists_section_transport_along_generating_iso e' he' U.LG.isLB L.isLB σ
  obtain ⟨w₀, hw₀, hPW⟩ := GlobalTheory.T.exists_iso_cancel_pulled_bundles_germs θ.hom.left φ (pullback.fst G.hom (jK V)) hθφ x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB ψ e' hψ he'
  let U' : Unif (IsLocalRing.maximalIdeal V) D x.P G :=
    { toUnifPre := { U.toUnifPre with gen := θ, gen_hom := hθm, ext := ⟨w₀, hw₀⟩ }, expand := U.expand }
  have hinv : U'.gen.inv.left ≫ pullback.fst G.hom (jK V) = φ := by
    show θ.inv.left ≫ pullback.fst G.hom (jK V) = φ
    rw [← hθφ, ← Category.assoc, ← Over.comp_left, θ.inv_hom_id, Over.id_left, Category.id_comp]
  have hFd := dualMapR_eq_of_map _ F hF1 hF2
  haveI : IsMonHom θ.hom := hθm
  refine key_unit_unif κ hR V hA hF D x G hSA U' w₀ ⟨hw₀, x.rig_gen, ?_⟩ y hLie (fun i => ?_) σ' ?_ ?_
  · exact GlobalTheory.T.iso_preserves_rigidification_at_origin V G x.P.A θ.hom φ hθφ hφe x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB x.rig L.rig U.LG.rig ψ e' w₀ hPW hRig heR
  · show (x.v i).left ≫ (U'.gen.inv.left ≫ pullback.fst G.hom (jK V)) = _
    rw [hinv, hv i, hFd]
  · intro s
    obtain ⟨z, hz, hz'⟩ := hNz s
    exact ⟨z, hz, hnz hz'⟩
  · exact GlobalTheory.T.secMaps_secPull_of_pointwise_germs θ.hom.left φ _ hθφ x.P.L L.L U.LG.L L.isLB ψ e' w₀ hPW x.th σ σ' hTh hσ'

end GlobalTheory.UMin.KeySmall
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven GlobalTheory.MBLow
open scoped CategoryTheory.Obj Cardinal
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.KeySmall


open Cardinal in
theorem mk_adicCompletion_le {D : Type} [CommRing D] (I : Ideal D) (h : #D ≤ 𝔠) : #(AdicCompletion I D) ≤ 𝔠 := by
  have hs : ∀ a : AdicCompletion I D, ∃ s : ℕ → D, ∀ n, a.val n = Submodule.Quotient.mk (s n) := fun a => by
    choose s hs using fun n => Submodule.Quotient.mk_surjective _ (a.val n)
    exact ⟨s, fun n => (hs n).symm⟩
  choose s hs using hs
  have hinj : Function.Injective s := fun a b hab => AdicCompletion.ext fun n => by rw [hs, hs, hab]
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right h).trans_eq Cardinal.continuum_power_aleph0


open Cardinal in
theorem dvd_of_forall_small : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R],
    #R ≤ 𝔠 → ∀ a b : R, b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → #V ≤ 𝔠 →
      ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  intro R _ _ _ _ _ hR a b hb h
  classical
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  let K := FractionRing R
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
  suffices hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by
    obtain ⟨r, hr⟩ := (h2 (algebraMap R K a / algebraMap R K b)).2 hmem
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hbK]
  intro p _ hp
  obtain ⟨-, hD, -⟩ := h1 p hp
  let D := primeLocalSubalgebra K p
  haveI : IsDiscreteValuationRing D := hD
  let W := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let iW : D →+* W := algebraMap D W
  let φ : R →+* W := iW.comp (algebraMap R D)
  have hRD : Function.Injective (algebraMap R D) := fun x y hxy =>
    IsFractionRing.injective R K (congrArg Subtype.val hxy)
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr D).comp hRD
  haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, inferInstance⟩
  have hcD : #D ≤ 𝔠 := by
    refine (Cardinal.mk_le_of_injective (f := fun d : D => (d : K)) Subtype.val_injective).trans ?_
    rw [Cardinal.mk_fractionRing]; exact hR
  obtain ⟨t, ht⟩ := h W hW (mk_adicCompletion_le _ hcD) φ hφ
  have hdvd : algebraMap R D b ∣ algebraMap R D a := by
    rcases ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩
    · exact hd
    have ha' : φ a ≠ 0 := (map_ne_zero_iff _ hφ).mpr ha
    have e : φ a * (iW c * t) = φ a * 1 := by
      rw [_root_.mul_one]
      calc φ a * (iW c * t) = iW (algebraMap R D a * c) * t := by
            rw [map_mul, _root_.mul_assoc]; rfl
        _ = φ a := by rw [← hc]; exact ht.symm
    have hu : IsUnit (iW c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit iW c hu
    exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  obtain ⟨c, hc⟩ := hdvd
  have hcK : algebraMap R K a = algebraMap R K b * (c : K) := congrArg Subtype.val hc
  rw [hcK, mul_div_cancel_left₀ _ hbK]
  exact c.2

theorem dvd_of_map_dvd {V W : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing W] [IsDomain W] (g : V →+* W)
    [IsLocalHom g] (hg : Function.Injective g) {a b : V} (h : g b ∣ g a) : b ∣ a := by
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  obtain ⟨t, ht⟩ := h
  rcases ValuationRing.dvd_total b a with hd | ⟨c, hc⟩
  · exact hd
  have ha' : g a ≠ 0 := (map_ne_zero_iff _ hg).mpr ha
  have e : g a * (g c * t) = g a * 1 := by
    rw [_root_.mul_one, ← _root_.mul_assoc, ← map_mul, ← hc]
    exact ht.symm
  have hu : IsUnit (g c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
  obtain ⟨u, rfl⟩ := isUnit_of_map_unit g c hu
  exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩


open Cardinal in
theorem mem_range_of_small_traits {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    (hA : #A ≤ 𝔠) (f : A) (hf : f ≠ 0) (b : Localization.Away f)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → #V ≤ 𝔠 →
      ∀ (t : A →+* V), Function.Injective t → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (g : V →+* W),
        Function.Injective g ∧ IsLocalHom g ∧ ∀ h : Localization.Away f →+* FractionRing W,
        h.comp (algebraMap A _) = (algebraMap W (FractionRing W)).comp (g.comp t) →
        ∃ w : W, h b = algebraMap W (FractionRing W) w) :
    ∃ c : A, algebraMap A (Localization.Away f) c = b := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) b
  obtain ⟨n, hn⟩ := s.2
  have hdiv : f ^ n ∣ a := by
    refine dvd_of_forall_small A hA a (f ^ n) (pow_ne_zero n hf) ?_
    intro V _ _ _ hc hV t ht
    obtain ⟨W, _, _, g, hg, hgl, HW⟩ := H V hc hV t ht
    obtain ⟨hd, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hc
    refine dvd_of_map_dvd g hg ?_
    have htf : (g.comp t) f ≠ 0 := (map_ne_zero_iff (g.comp t) (fun a b e => ht (hg e))).2 hf
    have hinjV := IsFractionRing.injective W (FractionRing W)
    have hu : IsUnit (((algebraMap W (FractionRing W)).comp (g.comp t)) f) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjV).2 htf)
    have hcomp := IsLocalization.Away.lift_comp (S := Localization.Away f) f hu
    obtain ⟨w, hw⟩ := HW _ hcomp
    have e := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hs
    rw [map_mul, hw, ← RingHom.comp_apply, hcomp, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      RingHom.comp_apply (algebraMap W (FractionRing W)), ← map_mul] at e
    have e' := hinjV e
    refine ⟨w, ?_⟩
    change (g.comp t) a = (g.comp t) (f ^ n) * w
    rw [← e', ← hn, mul_comm]
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  have hsu : IsUnit (algebraMap A (Localization.Away f) (s : A)) := IsLocalization.map_units _ s
  have hn' : (s : A) = f ^ n := hn.symm
  rw [hc, map_mul] at hs
  refine (hsu.mul_left_inj).1 ?_
  rw [hs, hn', mul_comm]

theorem polAt_of_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (g : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hc, hL⟩ := h
  have g₁ := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ P.A.left,
      ψ ≫ α = pullback.fst t.G.hom x ∧ ψ ≫ P.A.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, hc.1.lift_fst _ _ w, hc.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) P.A (𝟙 _) ψ :=
    hc.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (P.L.pull ψ) :=
    (GlobalTheory.LN.GenericPoint.lbIso_pull hL ψ h₁.symm).symm
  have hq := amplePt (Sp K) K (𝟙 _) P.A ((Over.pullback x).obj t.G) ψ g₂ P.L
    (t.PP.L.pull (pullback.fst t.G.hom x)) P.isLB hM e P.ample P.ktriv
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 P.isAb.proper, hq.1, hq.2⟩

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pullT {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : SAB H S' :=
  (fun {t' : SAB H S'} (_ : SABMap t' t f) => t')
    (sabPull Out.CubePf.cubePull f t).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

theorem pullT_map {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ m : SABMap (pullT f t) t f, m.φ = pullback.fst t.G.hom f :=
  (sabPull Out.CubePf.cubePull f t).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

theorem pullT_iso {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) {L : LB t.G.left} (hL : L.IsLB) (h : LBIso t.PP.L L)
    {L' : LB ((Over.pullback f).obj t.G).left} (hL' : L'.IsLB) (h' : LBIso (L.pull (pullback.fst t.G.hom f)) L') :
    LBIso (X := ((Over.pullback f).obj t.G).left) (pullT f t).PP.L L' := by
  obtain ⟨m, hm⟩ := pullT_map f t
  have e : LBIso (X := ((Over.pullback f).obj t.G).left) (pullT f t).PP.L (t.PP.L.pull (pullback.fst t.G.hom f)) := by
    rw [← hm]
    exact GlobalTheory.ModelSum.lbIso_of_map m
  have e' : LBIso (t.PP.L.pull (pullback.fst t.G.hom f)) (L.pull (pullback.fst t.G.hom f)) :=
    (CechPic.cls_eq_iff (pull_isLB t.PP.isLB _) (pull_isLB hL _)).1 (by
      rw [CechPic.cls_pull t.PP.isLB, CechPic.cls_pull hL, (CechPic.cls_eq_iff t.PP.isLB hL).2 h])
  have i₀ : LB.IsLB (X := ((Over.pullback f).obj t.G).left) (pullT f t).PP.L := (pullT f t).PP.isLB
  have i₁ := pull_isLB t.PP.isLB (pullback.fst t.G.hom f)
  have i₂ := pull_isLB hL (pullback.fst t.G.hom f)
  have e'' := LBIso.trans i₁ i₂ hL' e' h'
  exact LBIso.trans i₀ i₁ hL' e e''


open Cardinal in
theorem key_unit_split (κ : Rule) (hR : Rule4 κ) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (hW : #W ≤ 𝔠) (t : SAB H (Sp W))
    (hS : ∃ E' : SplitExt (Sp (IsLocalRing.ResidueField W)),
      E'.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t.G))
    (L : RigLB t.G) (hL : LBIso t.PP.L L.L) (σ : L.L.Sec) (x : KeyIn (FractionRing W)) (y : Fin x.P.g → (epsR W ⟶ t.G))
    (hy : IsLieBasis y) (hσ : NzFib σ) (hk : KeyOn (algebraMap W (FractionRing W)) x t.G L σ y) :
    ∃ u : Wˣ, (κ (FractionRing W) x : FractionRing W) = algebraMap W (FractionRing W) u := by
  have hk0 := hk
  obtain ⟨φ, -, ψ, -, hpb, hψ, -⟩ := hk
  have e₁ : LBIso x.P.L (L.L.pull φ) := ⟨ψ, hψ⟩
  have e₂ : LBIso x.P.L (t.PP.L.pull φ) :=
    (CechPic.cls_eq_iff x.P.isLB (pull_isLB t.PP.isLB _)).1 (by
      rw [(CechPic.cls_eq_iff x.P.isLB (pull_isLB L.isLB φ)).2 e₁, CechPic.cls_pull t.PP.isLB, CechPic.cls_pull L.isLB,
        (CechPic.cls_eq_iff t.PP.isLB L.isLB).2 hL])
  have hp : GlobalTheory.LN.PolAt t (jK W) := polAt_of_fibre t x.P.g _ ⟨x.P, φ, rfl, hpb, e₂⟩
  have hW' : GlobalTheory.LN.CDvr W := (GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hc, inferInstance⟩
  obtain ⟨U, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW' t hp hS
  exact key_unit_trait κ hR W hc hW t.G L σ x y t.semi ⟨U.D, U.A, U.U, by rw [U.bundle]; exact hL⟩ hy hσ hk0


open Cardinal in
theorem key_unit_normal (κ : Rule) (hR : Rule4 κ) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CharZero A] (hA : #A ≤ 𝔠) (t : SAB H (Sp A)) (L : RigLB t.G) (hL : LBIso t.PP.L L.L)
    (σ : L.L.Sec) (x : KeyIn (FractionRing A)) (y : Fin x.P.g → (epsR A ⟶ t.G))
    (hsm : SmoothOfRelativeDimension x.P.g t.G.hom) (hopen : IsOpen (abLocus t.G)) (hsym : L.IsSymmetric)
    (hpol : PolOnAb t.G L.L) (hy : IsLieBasis y) (hσ : NzFib σ)
    (hkey : KeyOn (algebraMap A (FractionRing A)) x t.G L σ y) :
    ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u := by
  have hkey0 := hkey
  obtain ⟨φ, -, -, -, hpb, -⟩ := hkey
  haveI : IsProper x.P.A.hom := x.P.isAb.proper
  have hab := GlobalTheory.range_subset_abLocus_of_isProper t.semi hpb.1
  obtain ⟨f, hf0, hfab⟩ := LocPf.exists_away_subset (abLocus t.G) hopen hab
  have hle : Submonoid.powers f ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away f) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) (Localization.Away f) inferInstance
  haveI : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away f) (Submonoid.powers f) hle
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) := IsLocalization.injective _ hle
  haveI : CharZero (Localization.Away f) := charZero_of_injective_algebraMap hinj
  obtain ⟨xB, hgB, hkB⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (Localization.Away f) (algebraMap A _) t.G L σ x.P.g y x.g_pos t.semi hsm hopen
    hsym hpol hy hσ hfab
  obtain ⟨u, hu⟩ := hR.2.2.2 (Localization.Away f) xB
  have hfu : IsUnit ((algebraMap A (FractionRing A)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hf0)
  have hc := IsLocalization.Away.lift_comp (S := Localization.Away f) f hfu
  have hpbx : KeyPB x xB (IsLocalization.Away.lift (S := Localization.Away f) f hfu) :=
    GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing A) (algebraMap A _) _ t.G L σ x.P.g y xB x hgB rfl hkB
      (by rw [hc]; exact hkey0)
  have hval := hu _ _ x hpbx
  have trait : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → #V ≤ 𝔠 →
      ∀ (a : A →+* V), Function.Injective a → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (g : V →+* W),
        Function.Injective g ∧ IsLocalHom g ∧ ∀ h : Localization.Away f →+* FractionRing W,
        h.comp (algebraMap A _) = (algebraMap W (FractionRing W)).comp (g.comp a) →
        ∃ w : Wˣ, h u = algebraMap W (FractionRing W) w := by
    intro V _ _ _ hV hcV a ha
    obtain ⟨hd, hcomp, h0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
    haveI := hd
    haveI := h0
    obtain ⟨W, _, _, _, _, g, hcW, hgi, hginj, hgl, Ex, hEx⟩ :=
      GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V hcomp (pullT (spMap a) t).G (pullT (spMap a) t).semi
    refine ⟨W, inferInstance, inferInstance, g, hginj, hgl, fun h hh => ?_⟩
    have hW : #W ≤ 𝔠 := by
      letI := g.toAlgebra
      haveI : Algebra.IsIntegral V W := ⟨hgi⟩
      haveI : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.2 hginj
      exact (Algebra.IsAlgebraic.cardinalMk_le_max V W).trans (max_le hcV aleph0_le_continuum)
    have hrange : Set.range (spMap ((algebraMap W (FractionRing W)).comp (g.comp a))) ⊆ abLocus t.G := by
      rw [← hh]
      rintro _ ⟨p, rfl⟩
      exact hfab ⟨spMap h p, rfl⟩
    obtain ⟨xV, hgV, hkV⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (FractionRing W) ((algebraMap W _).comp (g.comp a)) t.G L σ x.P.g y x.g_pos
      t.semi hsm hopen hsym hpol hy hσ hrange
    have hpbV : KeyPB xV xB h :=
      GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing W) (algebraMap A _) h t.G L σ x.P.g y xB xV hgB hgV hkB
        (by rw [hh]; exact hkV)
    have hvalV := hu _ h xV hpbV
    haveI : IsCommMonObj ((Over.pullback (spMap a)).obj t.G) := (pullT (spMap a) t).comm
    obtain ⟨L₁, σ₁, y₁, hiso₁, hy₁, hσ₁, hk₁⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis A V (FractionRing W) a ((algebraMap W _).comp g) t.G L σ xV
      (fun i => y (i.cast hgV)) t.semi (LocPf.isLieBasis_cast hgV y hy) hσ hkV
    have e₁ := pullT_iso (spMap a) t L.isLB hL L₁.isLB hiso₁
    haveI : IsCommMonObj ((Over.pullback (spMap g)).obj ((Over.pullback (spMap a)).obj t.G)) :=
      (pullT (spMap g) (pullT (spMap a) t)).comm
    obtain ⟨L₂, σ₂, y₂, hiso₂, hy₂, hσ₂, hk₂⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis V W (FractionRing W) g (algebraMap W _)
      ((Over.pullback (spMap a)).obj t.G) L₁ σ₁ xV y₁ (pullT (spMap a) t).semi hy₁ hσ₁ hk₁
    have e₂ := pullT_iso (spMap g) (pullT (spMap a) t) L₁.isLB e₁ L₂.isLB hiso₂
    obtain ⟨w, hw⟩ := key_unit_split κ hR W hcW hW (pullT (spMap g) (pullT (spMap a) t)) ⟨Ex, hEx⟩ L₂ e₂ σ₂ xV y₂ hy₂
      hσ₂ hk₂
    exact ⟨w, hvalV.symm.trans hw⟩
  obtain ⟨c, hcu⟩ := mem_range_of_small_traits hA f hf0 (u : Localization.Away f) (fun V _ _ _ hV hcV a ha => by
    obtain ⟨W, _, _, g, h1, h2, h3⟩ := trait V hV hcV a ha
    refine ⟨W, inferInstance, inferInstance, g, h1, h2, fun h hh => ?_⟩
    obtain ⟨w, hw⟩ := h3 h hh
    exact ⟨w, hw⟩)
  obtain ⟨c', hcu'⟩ := mem_range_of_small_traits hA f hf0 ((u⁻¹ : (Localization.Away f)ˣ) : Localization.Away f)
    (fun V _ _ _ hV hcV a ha => by
      obtain ⟨W, _, _, g, h1, h2, h3⟩ := trait V hV hcV a ha
      refine ⟨W, inferInstance, inferInstance, g, h1, h2, fun h hh => ?_⟩
      obtain ⟨w, hw⟩ := h3 h hh
      refine ⟨((w⁻¹ : Wˣ) : W), ?_⟩
      rw [map_units_inv, map_units_inv, hw])
  have hcc : c * c' = 1 := hinj (by rw [map_mul, hcu, hcu', Units.mul_inv, map_one])
  refine ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, ?_⟩
  rw [hval, Units.val_mk, ← hcu, ← RingHom.comp_apply, hc]

end Triples

theorem lbPow_U' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j : (lbPow M n).ι) : (lbPow M n).U j = M.U (j PUnit.unit) := by
  ext x
  simp only [lbPow, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h i => h⟩

theorem germ_lbPow_g' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j j' : (lbPow M n).ι) (x : S)
    (h : x ∈ (lbPow M n).U j ⊓ (lbPow M n).U j') (h' : x ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :
    S.presheaf.germ _ x h ((lbPow M n).g j j' : Γ(S, (lbPow M n).U j ⊓ (lbPow M n).U j')) =
      S.presheaf.germ _ x h' (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(S, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) ^ n := by
  simp only [lbPow, LB.LinComb, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  congr 1
  simp [res, pullU]
  erw [map_pow]
  congr 1
  erw [Units.coe_map, Units.coe_map]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _


open Cardinal in
theorem key_sab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (S : Scheme.{0}) [IsIntegral S]
    (t : SAB H S) (g : ℕ) (δ : LB S) (σ : (CechPic.tens t.PP.L (δ.pull t.G.hom)).Sec) (hg : 1 ≤ g)
    (hN : Geo.Tor.IsNormalScheme S) (hn : IsLocallyNoetherian S) (h0 : CharZero Γ(S, ⊤))
    (hsmall : ∀ (A : Type) [CommRing A] (ξ : Sp A ⟶ S), IsOpenImmersion ξ → #A ≤ 𝔠)
    (hsm : SmoothOfRelativeDimension g t.G.hom) (hne : (abLocus t.G).Nonempty) (hop : IsOpen (abLocus t.G))
    (hδ : δ.IsLB) (hpol : PolOnAb t.G t.PP.L) (hnz : NzFib σ) :
    LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge t.G g) 4) := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : Rule4 κ := ⟨hH, hF, hT, hU⟩
  obtain ⟨f, hloc, hcomp⟩ := GlobalTheory.T.keyValues_detOmega_delta_unit_affineOpens κ hH hF S t.G g t.PP δ σ hg hN hn h0 t.semi hsm hne hop t.sym hδ hpol hnz
    (fun A _ _ _ _ _ ξ hξ _ L' σ' x y hiso hsm' hop' hsym' hpol' hy hσ' hk =>
      key_unit_normal κ h4 A (hsmall A ξ hξ) (pullT ξ t) L'
        (pullT_iso ξ t t.PP.isLB (PolBaseChange.lbIso_refl t.PP.isLB) L'.isLB hiso) σ' x y hsm' hop' hsym' hpol' hy hσ' hk)
  refine GlobalTheory.GlueRat.lbIso_of_rat S (lbPow δ 8) (lbPow (SiegelTor.hodge t.G g) 4) (fun p => f (p.1 PUnit.unit) (p.2 PUnit.unit)) ?_ ?_
  · rintro ⟨c, i⟩ x hx
    rw [lbPow_U', lbPow_U'] at hx
    obtain ⟨V, hV, hxV, u, hu⟩ := hloc _ _ x hx
    exact ⟨V, by rw [lbPow_U', lbPow_U']; exact hV, hxV, u, hu⟩
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h1 h2
    have h1' : genericPoint S ∈ (VB.det (LieVB.omega t.G) g).U (c PUnit.unit) ⊓ (VB.det (LieVB.omega t.G) g).U (c' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h1; exact h1
    have h2' : genericPoint S ∈ δ.U (i PUnit.unit) ⊓ δ.U (i' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h2; exact h2
    dsimp only
    rw [germ_lbPow_g' δ 8 i i' _ h2 h2', germ_lbPow_g' _ 4 c c' _ h1 h1']
    exact hcomp _ _ _ _ h1' h2'

theorem cls_eq_zero_of_chart {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (i₀ : L.ι) (h : L.U i₀ = ⊤) :
    CechPic.cls L hL = 0 := by
  have le : ∀ j, L.U j ≤ L.U j ⊓ L.U i₀ := fun j => le_inf le_rfl (h ▸ le_top)
  have hm : ∀ y : Z, y ∈ L.U i₀ := fun y => h ▸ TopologicalSpace.Opens.mem_top y
  exact (CechPic.cls_eq_zero_iff hL).2 ⟨⟨fun j => res (le j) (L.g j i₀)⟩, fun i j => unit_ext fun y hy => by
      rw [map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.1, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.2]
      exact (gm_cocycle hL (𝟙 Z) y hy.1 hy.2 (hm y)).symm⟩

theorem cls_O1_zero (o : Type) [CommRing o] : CechPic.cls _ (ProjSpace.O1_isLB o 0) = 0 := by
  refine cls_eq_zero_of_chart _ (0 : Fin 1) (top_le_iff.1 fun x _ => ?_)
  obtain ⟨i, hi⟩ := Semi.LB.mem_of_cover (ProjSpace.O1_isLB o 0) x
  obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  exact hi

theorem cls_det_zero {X : Scheme.{0}} (F : X.Modules) (h : (VB.det F 0).IsLB) : CechPic.cls _ h = 0 := by
  refine (CechPic.cls_eq_zero_iff h).2 ⟨⟨fun _ => 1⟩, fun c c' => ?_⟩
  have e : (VB.det F 0).g c c' = 1 := Units.ext (by
    refine (VB.IsFrame.val_detUnit c.isFrame c'.isFrame inf_le_left inf_le_right).trans ?_
    rw [Module.Basis.det_apply, Matrix.det_isEmpty]
    rfl)
  simp [e]


open Cardinal in
theorem mk_le_of_lft {k A : Type} [Field k] [CommRing A] (hk : #k ≤ 𝔠) (s : Sp A ⟶ Sp k) [LocallyOfFiniteType s] :
    #A ≤ 𝔠 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 ‹_›
  letI := φ.hom.toAlgebra
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (show Algebra.FiniteType k A from hft)
  refine (Cardinal.mk_le_of_surjective hp).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le hk ((Cardinal.lt_aleph0_of_finite _).le.trans aleph0_le_continuum)) aleph0_le_continuum

theorem nzFib_of_geom {S : Scheme.{0}} {G : Over S} {L : LB G.left} (σ : L.Sec)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (y : Sp K ⟶ G.left) (j : L.ι), y ≫ G.hom = x ∧
      Set.range y ⊆ L.U j ∧ valF y _ (σ.f j) ≠ 0) : NzFib σ := by
  intro s
  let K := AlgebraicClosure (S.residueField s)
  obtain ⟨y, j, hy, hj, hv⟩ := h K (spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s)
  let q : Sp K := IsLocalRing.closedPoint K
  refine ⟨y q, ?_, TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩⟩
  · rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  · have hle : ⊤ ≤ y ⁻¹ᵁ L.U j := fun z _ => hj ⟨z, rfl⟩
    rw [valF, dite_eq_left hle] at hv
    have hu : IsUnit ((y.appLE (L.U j) ⊤ hle).hom (σ.f j)) :=
      (isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _).1 (isUnit_iff_ne_zero.2 hv)
    have hb := (Sp K).basicOpen_of_isUnit hu
    rw [Scheme.basicOpen_appLE] at hb
    have : q ∈ (⊤ ⊓ y ⁻¹ᵁ G.left.basicOpen (σ.f j) : (Sp K).Opens) := by rw [hb]; trivial
    exact this.2

end GlobalTheory.UMin.KeySmall
