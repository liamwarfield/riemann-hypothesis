module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatRowTest
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyStagesParametersParameterSizeConditionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_stages_parameterSizeConditions : EvG fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) → ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  first | exact @GlobalTheory.Mem.R3.LedSize.evG_exists_sizeRows | exact GlobalTheory.Mem.R3.LedSize.evG_exists_sizeRows | (intros; apply GlobalTheory.Mem.R3.LedSize.evG_exists_sizeRows <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestAtRealisationOfHilbertModels
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHilbertModelsOfChoiceClaims
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHilbertModelsOfChoiceClaims
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

namespace GlobalTheory.RowTestFromClaims

open GlobalTheory.RowTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_gE (R : RealDat D A Ks) (hE : R.models_HE) (hg : R.models_gE) (y : R.HE.H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  have hmem : R.HE.e y ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ _
  have hfix := ((mem_goodPart _ _ _ _ _ _).1 hmem).2
  apply hE.1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [map_smul, hg]
  ext v
  rw [← hfix v]
  simp only [RealDat.e0, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.sum_apply, MultilinearMap.smul_apply, postOn_apply]
  rfl

theorem rat_of_formula {K : Type} [Field K] (σ : K →+* ℂ) {z : K} {c c₀ κ p w : ℂ} (hz : σ z ≠ 0) (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (hκ : κ ≠ 0) (h : σ z * c * p = κ * w) (hw : w ∈ Set.range σ) (hr : c / c₀ ∈ Set.range σ) : ∃ y, σ y = c₀ * κ⁻¹ * p := by
  obtain ⟨w', rfl⟩ := hw
  obtain ⟨r', hr'⟩ := hr
  refine ⟨w' / (z * r'), ?_⟩
  rw [map_div₀, map_mul, hr']
  have hp : p = κ * σ w' / (σ z * c) := by
    rw [eq_div_iff (mul_ne_zero hz hc), ← h]
    ring
  rw [hp]
  field_simp


set_option maxHeartbeats 1000000 in
theorem exists_good (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (t : T0)
    (x : A.fam.amb.FR t) :
    ∃ x' : A.fam.amb.FR t, x' ∈ (A.fam.R t).goodF A.fam.X ∧ R.Th t (R.jX t x') = R.Th t (R.jX t x) := by
  obtain ⟨hth, -⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hP R F hC
  have hga : goodAt A.fam.X (⊥ : Subgroup G) 1 = idemOf A.X := Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _
  have hmem : (A.fam.R t).S.gaOp (A.fam.R t).r (idemOf A.X) x ∈ (A.fam.R t).goodF A.fam.X := by
    unfold BlockDat.goodF
    rw [hga]
    exact LinearMap.mem_range_self _ x
  refine ⟨_, hmem, ?_⟩
  conv_rhs => rw [← sum_gE R hC.models.HE hC.models.gE (R.Th t (R.jX t x))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hth t g x]

private theorem exists_linearMap_eq_psiK {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) :
    ∃ f : Fin ch.n → (R.HE.H →ₗ[ℂ] ℂ), ∀ a u, f a u = psiK ch a u :=
  ⟨fun a =>
    { toFun := psiK ch a
      map_add' := fun u u' => by
        simp only [psiK, map_add (f := _)]
        exact GlobalTheory.FunObj.fPsiPhi_add ch.W ch.M (hlin a u) (hlin a u')
      map_smul' := fun b u => by
        have h1 := GlobalTheory.FunObj.fPsiPhi_smul ch.W ch.M ch.ρ ch.ξ 1 b (ch.col a) (ch.Phi a) (ch.form u)
        rw [one_smul, one_mul] at h1
        simp only [psiK, map_smul, RingHom.id_apply, smul_eq_mul]
        exact h1 }, fun _ _ => rfl⟩

private theorem rowTestModel_of_scaled_values_rational {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u)
    (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0) {k : ℂ} (hk : k ≠ 0)
    (hval : ∀ t x a, ∃ z : D.what₂.LL, D.what₂.embLL z = k * psiK ch a (R.Th t (R.jX t x))) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  obtain ⟨f, hf⟩ := exists_linearMap_eq_psiK ch hlin
  refine ⟨ch.n, fun a => k • f a, ?_, ?_⟩
  · intro e he
    apply hinj
    intro a
    have h1 := he a
    rw [LinearMap.smul_apply, hf, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hk
  · intro t x a
    obtain ⟨z, hz⟩ := hval t x a
    refine ⟨z, hz.trans ?_⟩
    exact (((LinearMap.smul_apply k (f a) _).trans (congrArg (k • ·) (hf a _))).trans (smul_eq_mul k _)).symm

set_option maxHeartbeats 1600000 in
private theorem exists_embLL_mul_psiK_eq_vK_of_formulaAt (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze) (t : T0) (x : A.fam.amb.FR t) (a : Fin ch.n) :
    ∃ x' : A.fam.amb.FR t, D.what₂.embLL (ze t) * cTot ch t * psiK ch a (R.Th t (R.jX t x)) = κ * vK ch t x' a := by
  obtain ⟨x', hx', hxx⟩ := exists_good hP R F hC t x
  refine ⟨x', ?_⟩
  rw [← hxx]
  exact hF.2 t x' hx' a


set_option maxHeartbeats 1600000 in
theorem rowTest_of_choice (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0)
    (hc : ∀ i j t, ch.c i j t ≠ 0) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze)
    (hv : ∀ t x a, vK ch t x a ∈ Set.range D.what₂.embLL) (hr : ∀ i j t, sqRatio ch i j t ∈ Set.range D.what₂.embLL) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  have hcT : ∀ t, cTot ch t ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hc i j t
  have hz0 : ∀ t, D.what₂.embLL (ze t) ≠ 0 := by
    intro t
    obtain ⟨n, hn, hze⟩ := hF.1 t
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hn.ne'] at hze
    exact zero_ne_one hze
  by_cases hκ : κ = 0
  · subst hκ
    refine rowTestModel_of_scaled_values_rational ch hlin hinj one_ne_zero fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hp : psiK ch a (R.Th t (R.jX t x)) = 0 :=
      (mul_eq_zero.1 (hfo.trans (zero_mul _))).resolve_left (mul_ne_zero (hz0 t) (hcT t))
    exact ⟨0, (map_zero D.what₂.embLL).trans (hp.symm.trans (one_mul _).symm)⟩
  · refine rowTestModel_of_scaled_values_rational ch hlin hinj (mul_ne_zero (hcT A.μ0) (inv_ne_zero hκ)) fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hrat : cTot ch t / cTot ch A.μ0 ∈ Set.range D.what₂.embLL := by
      have he : cTot ch t / cTot ch A.μ0 = ∏ i, ∏ j, sqRatio ch i j t := by
        simp only [cTot, sqRatio, Finset.prod_div_distrib]
      rw [he]
      exact RingHom.mem_fieldRange.1 (Subfield.prod_mem _ fun i _ =>
        Subfield.prod_mem _ fun j _ => RingHom.mem_fieldRange.2 (hr i j t))
    exact rat_of_formula D.what₂.embLL (hz0 t) (hcT t) (hcT _) hκ hfo (hv t x' a) hrat


set_option maxHeartbeats 1000000 in
theorem rowTestModel_of_claims : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.RowClaim.HidaSetting large₂ R F → (∃ ch : GlobalTheory.RowTest.Choice R, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  intro hP hL hI hC _ hF hR hRa
  obtain ⟨CF0, h⟩ := Big.and (Big.and (Big.and (Big.and (Big.and hL hI) hC) hF) hR) hRa
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ hε hxl G _ _ Pl0 T0 A Ks _ _ _ R F hSet => ?_⟩
  rintro ⟨ch, hch, hsc, hfld⟩
  obtain ⟨⟨⟨⟨⟨hlin, hinj⟩, hcst⟩, hfor⟩, hrat⟩, hra⟩ := hx D large₂ hε hxl G Pl0 T0 A Ks R F hSet ch hch hsc
  obtain ⟨κ, ze, hFo⟩ := hfor hfld
  exact rowTest_of_choice hP hSet.core ch hlin hinj (fun i j t => (hcst i j t).2) hFo (hrat hfld) (hra hfld)

end GlobalTheory.RowTestFromClaims
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHilbertModelsOfChoiceClaimsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_hilbertModels_of_choiceClaims : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.RowClaim.HidaSetting large₂ R F → (∃ ch : GlobalTheory.RowTest.Choice R, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  first | exact @GlobalTheory.RowTestFromClaims.rowTestModel_of_claims | exact GlobalTheory.RowTestFromClaims.rowTestModel_of_claims | (intros; apply GlobalTheory.RowTestFromClaims.rowTestModel_of_claims <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestComplexSideOfHilbertModels
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestComplexSideOfHilbertModels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models

theorem rowTest_toCx3 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F h
  obtain ⟨n, ψ, hinj, hrat⟩ := (GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.test_tw_iff (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0) R.emb0 (ι := T0)
    (X := fun t => A3.A.fam.amb.FR t) fun t x => R.Th t (R.jX t x)).2 h
  exact ⟨n, ψ, hinj, fun t i x => hrat t x i⟩

end GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestComplexSideOfHilbertModelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_complexSide_of_hilbert_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  first | exact @GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 | exact GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 | (intros; apply GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestAtRealisationOfHilbertModels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

theorem GlobalTheory.RowTest.rowTest_realisation : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.RowClaim.HidaSetting large₂ R.toRealDat F.lv2 → (∃ ch : GlobalTheory.RowTest.Choice R.toRealDat, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro hC hL hI hCo hS hF hSR hR
  obtain ⟨CF0, hCF0⟩ := GlobalTheory.T.rowTest_hilbertModels_of_choiceClaims hC hL hI hCo hS hF hSR hR
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hCF0 ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hSet hch => ?_⟩
  exact GlobalTheory.T.rowTest_complexSide_of_hilbert_models D G Pl0 I0 T0 A3 Ks R F (hx₀ D large₂ hε hx G Pl0 T0 _ Ks R.toRealDat F.lv2 hSet hch)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestAtRealisationOfHilbertModelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_at_realisation_of_hilbertModels : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.RowClaim.HidaSetting large₂ R.toRealDat F.lv2 → (∃ ch : GlobalTheory.RowTest.Choice R.toRealDat, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  first | exact @GlobalTheory.RowTest.rowTest_realisation | exact GlobalTheory.RowTest.rowTest_realisation | (intros; apply GlobalTheory.RowTest.rowTest_realisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

noncomputable section

theorem GlobalTheory.RowEx.dat_choice_exists : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  classical
  intro hE
  obtain ⟨CF0, hE⟩ := hE
  refine ⟨CF0, fun CF hCF => ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ?_⟩⟩⟩⟩⟩
  obtain ⟨x₀, hx⟩ := hE eps CF hCF
  refine ⟨x₀, fun K _ _ _ hK hxK => ?_⟩
  have hF := hx K.s hK hxK
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if h : Ξ.Finite then Classical.choose (hF P f Ξ h) else ∅, by simp, ?_, ?_⟩
  · intro P f _ _ Ξ z hz
    by_cases h : Ξ.Finite
    · dsimp only at hz
      rw [dite_eq_left h] at hz
      exact (Classical.choose_spec (hF P f Ξ h)).1 z hz
    · dsimp only at hz
      rw [dite_eq_right h] at hz
      simp at hz
  · intro B f T _ hH _ _ w Z hX Wt z L hL hS
    obtain ⟨hq, hC, hfin, hmem⟩ := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z hX Wt z
    have hS2 := hH.2
    dsimp only at hS2
    rw [dite_eq_left hfin] at hS2
    rw [hL]
    exact (Classical.choose_spec (hF B.toPre f (T.set f) hfin)).2 (w.st Z) f rfl HEq.rfl L hL _ _ _ _ _ _ _ hS hC hq
      (fun t => ⟨_, hmem t, HEq.rfl⟩) (fun y hy => hS2 y hy)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData : GlobalTheory.RowEx.ExField → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLg fun K B f T => ∀ (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (L : SizeData₂ (w.st Z).toD7), L.sc = K.s → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 → ∃ ch : GlobalTheory.RowTest.Choice z.R.toRealDat, ch.Is ∧ ch.AtScale CF L.sc.b ∧ ch.FieldOK := by
  exact @GlobalTheory.RowEx.dat_choice_exists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn

theorem rowTest_setting_dat : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L →
    GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  refine Ev.mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK B f T w Z hX Wt z hOv hG hEx L hsz
  obtain ⟨hHost, hF, -, -, -, -, -, hstdX⟩ := hK (w.st Z) hOv
  have hC := z.pins.char
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hC hEx).1
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  exact
    { size := hsz
      eser := hG.eSerTie Z.V Z.S Z.G
      host := hHost
      hF := hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := z.pins.keep.guard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := z.pins.keep.std
      stdX := hstdX
      betaX := z.pins.keep.beta.2 }

end GlobalTheory.PrimIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hidaSetting_of_sizeRows : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f → z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L → GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  first | exact @GlobalTheory.PrimIn.rowTest_setting_dat | exact GlobalTheory.PrimIn.rowTest_setting_dat | (intros; apply GlobalTheory.PrimIn.rowTest_setting_dat <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.RowAt

theorem ev_scale {p : ℝ → ℝ → Prop} (h : ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, p eps x₀) :
    Ev fun K => ∃ x₀ : ℝ, x₀ ≤ K.s.x ∧ p K.s.eps x₀ :=
  ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    let ⟨x₀, hx⟩ := h eps h0
    ⟨x₀, fun _ _ _ _ hs hx' => ⟨x₀, hx', hs ▸ hx⟩⟩⟩⟩⟩⟩


set_option maxHeartbeats 2000000 in
theorem atDat_rowTest : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK →
    RatioK → GlobalTheory.RowEx.ExField → StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt →
      GlobalTheory.RealGeo.InGeo z.geo → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  intro hG hC h1 h2 h3 h4 h5 h6 h7 hEF
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.rowTest_at_realisation_of_hilbertModels hC h1 h2 h3 h4 h5 h6 h7
  obtain ⟨CF2, H2⟩ := GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData hEF
  have hCh := H2 (max CF1 CF2) (le_max_right _ _)
  have e1 := ((evG_of_ev (ev_scale fun eps _ => H1 eps (max CF1 CF2) (le_max_left _ _))).inter GlobalTheory.T.eventually_stages_parameterSizeConditions).inter
    (evG_of_ev GlobalTheory.T.hidaSetting_of_sizeRows)
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg hCh)
  refine s1.trans (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨⟨⟨x₀, hx, hH⟩, hLed⟩, hSet⟩ B f T hO - - hch w - Z hX Wt z g1 - hEx -
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hG (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz⟩ := hLed (w.st Z') hO hη hA
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  exact (GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer B w.C Z Z' w.px w.I hX T Wt s z).2 (by
    have hEx' := DatCopy.copy_exAt Z' s hEx
    generalize DatCopy.copy Z' s z = y at hEx' ⊢
    have hS := hSet B f T w Z' hX Wt y hO g1' hEx' L hsz
    exact hH (w.st Z').toD7 L (by rw [hsc]) (by rw [hsc]; exact hx) _ _ _ _ _ _ y.R y.F hS (hch w Z' hX Wt y L hsc hS))

end GlobalTheory.Mem.R3.Rw.RowAt

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
open GlobalTheory.RowClaim

namespace GlobalTheory.Twist

theorem atDat_rowTest_of_exField : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → GlobalTheory.RowEx.ExField → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun hG hC h1 h2 h3 h4 h5 h6 h7 hE => GlobalTheory.Mem.R3.Rw.RowAt.atDat_rowTest hG hC h1 h2 h3 h4 h5 h6 h7 hE

end GlobalTheory.Twist
