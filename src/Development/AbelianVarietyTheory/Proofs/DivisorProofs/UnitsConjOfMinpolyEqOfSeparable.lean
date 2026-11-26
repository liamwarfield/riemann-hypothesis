module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem conj_rel_alg' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β e e' : G.Cˣ) (a' : G.C) (r r' : ℚˣ) :
    algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) =
      algebraMap ℚ G.C ((r : ℚ) / r') * (((e * e'⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (r' : ℚ) *
        ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))) *
        ((β : G.C) * sh G ((e * e'⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  have hsh : sh G ((e * e'⁻¹ : G.Cˣ) : G.C) = sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C) := by
    simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : sh G (e' : G.C) * sh G ((e'⁻¹ : G.Cˣ) : G.C) = 1 := by
    simp only [sh]
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hrr : (r' : ℚ) * ((r : ℚ) / r') = r := by field_simp
  have key2 : ((e : G.C) * ((e'⁻¹ : G.Cˣ) : G.C)) * ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) *
      ((β : G.C) * (sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C)) * ((β⁻¹ : G.Cˣ) : G.C)) =
      (e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    simp only [mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul_cancel_left, ← mul_assoc (sh G (e' : G.C)), h1, one_mul]
  rw [hsh, Units.val_mul]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, hrr]
  rw [key2]

theorem commute_of_commute_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (y₀ : G.C)
    (hsep : (minpoly G.F y₀).Separable) (hdeg : (minpoly G.F y₀).natDegree = G.n) (a b : G.C)
    (ha : Commute a y₀) (hb : Commute b y₀) : Commute a b := by
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hamem : a ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact ha.eq.symm
  have hbmem : b ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hb.eq.symm
  rw [hc] at hamem
  have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({y₀} : Set G.C) hamem
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 b hbmem).symm

theorem units_conj_of_minpoly_eq_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ)
    (hab : minpoly G.F (a : G.C) = minpoly G.F (b : G.C)) (hsep : (minpoly G.F (b : G.C)).Separable)
    (hdeg : (minpoly G.F (b : G.C)).natDegree = G.n) : ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  haveI : Infinite G.F := Infinite.of_injective (Nat.cast : ℕ → G.F) Nat.cast_injective
  obtain ⟨g, hg⟩ := GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq G.F G.C G.n G.rankC (b : G.C) (a : G.C) hsep hdeg hab
  refine ⟨g, ?_⟩
  rw [hg, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.LKCx.ClsReg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiDetValues


set_option maxHeartbeats 1000000 in
theorem res_mem {D : D7} (S : Subfield ℂ) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq c χ)
    (hS : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ S)
    (P : Pl D.host.E) (ψ : (kP P)ˣ →* ℂˣ) (hψ : IsRes χ P ψ⁻¹) (u : (kP P)ˣ) : ((ψ u : ℂˣ) : ℂ) ∈ S := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  have h4 := hψ a (Units.mk0 _ ha0) u rfl ha.symm
  have h5 := hc.2 P e he (Units.mk0 _ ha0) (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) rfl
  have h6 := hS (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) (by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, hinf,
      zero_mul, add_zero])
  rw [h5, ← h4, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h6
  exact inv_mem_iff.1 h6


set_option maxHeartbeats 1000000 in
theorem chiC_mem_coeff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL t i g
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T t.alg t.laws.pins.2.2.1
  have hσ : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.good_σ₀
  have hA := (t.chiR i D.what₂.embLL hσ).2.2.2.1
  have h : ((chiC R i g : ℂˣ) : ℂ) ∈ (res T D.what₂.embLL).fieldRange := by
    unfold chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy, -⟩ := hA x hx
    exact ⟨y, hy.symm⟩
  exact h

end GlobalTheory.ChiDetValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffFieldStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_character_det_values_mem_coeff_field : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ChiDetValues.chiC_mem_coeff | exact GlobalTheory.ChiDetValues.chiC_mem_coeff | (intros; apply GlobalTheory.ChiDetValues.chiC_mem_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Matrix

namespace GlobalTheory.AdelicSvN.Weyl

variable {F : Type} [Field F] [NumberField F]

theorem trace_eq_mixedTrace (m : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) m = mixedTrace F m := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, mixedTrace_apply]
  simp only [Algebra.trace_complex_apply, Algebra.trace_self_apply]

theorem isStd_infinite {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (z : InfiniteAdeleRing F) :
    ψ (infiniteAdeleInl z) = (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have hat : At (evI F) (infiniteAdeleInl z : AF F) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [hψ.2.2 _ hat, h2, trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) : ψ a = (adelicChar F a : ℂ) := by
  have hfin : ∀ y : FiniteAdeleRing (𝓞 F) F,
      ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ) := by
    intro y
    refine (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).induction_on
      (p := fun y => ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ)) y
      (isClosed_eq (hψ.1.comp continuous_finiteAdeleInr)
        (continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp continuous_finiteAdeleInr))) fun k => ?_
    have hs := infiniteAdeleInl_add_finiteAdeleInr (algebraMap F (AF F) k)
    rw [adeleRing_algebraMap_fst, adeleRing_algebraMap_snd] at hs
    have e : (finiteAdeleInr (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) : AF F) =
        algebraMap F (AF F) k + infiniteAdeleInl (-algebraMap F (InfiniteAdeleRing F) k) := by
      rw [← hs, map_neg]; abel
    rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.1, adelicChar_algebraMap, one_mul, one_mul,
      isStd_infinite hψ]
  rw [← infiniteAdeleInl_add_finiteAdeleInr a, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul,
    isStd_infinite hψ, hfin]

variable {κ : Type} [Fintype κ]

theorem pureA_eq (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f g = schwartzBruhatTensorPi f g := by
  funext x
  simp only [pureA, schwartzBruhatTensorPi]
  rfl

omit [Fintype κ] in
theorem mem_SB_iff (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ↔ g ∈ finiteSchwartzBruhatPi F :=
  (mem_finiteSchwartzBruhatPi F).symm

theorem schA_eq : schA F κ = schwartzBruhatPi (K := F) (ι := κ) := by
  unfold schA schwartzBruhatPi
  congr 1

def fourierLin : schA F κ →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun φ := adelicFourierPi F φ.1
  map_add' φ φ' := adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ.2))
    (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ'.2))
  map_smul' c φ := adelicFourierPi_smul c φ.1

theorem act_weyl [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    act (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) w = (w.2, -w.1) := by
  have h0 : (0 : Matrix κ κ F).map (algebraMap F (AF F)) = 0 := Matrix.map_zero _ (map_zero _)
  have h1 : (1 : Matrix κ κ F).map (algebraMap F (AF F)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (-1 : Matrix κ κ F).map (algebraMap F (AF F)) = -1 := by rw [Matrix.map_neg _ (map_neg _), h1]
  simp only [act, Matrix.fromBlocks_map, h0, h1, h2, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]

theorem integral_add_right_pi (f : (κ → AF F) → ℂ) (a : κ → AF F) :
    ∫ x, f (x + a) ∂(adeleMeasurePi F) = ∫ x, f x ∂(adeleMeasurePi F) := by
  let _ : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  have : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have : MeasurableAdd (κ → AdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  exact integral_add_right_eq_self f a

theorem fourier_schr {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    adelicFourierPi F (schr ψ w φ) = schr ψ (w.2, -w.1) (adelicFourierPi F φ) := by
  funext y
  simp only [adelicFourierPi, schr, ← isStd_eq hψ]
  rw [← integral_const_mul, ← integral_add_right_pi _ (-w.1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  have e : ((x + -w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (x + -w.1) ⬝ᵥ y =
      (y ⬝ᵥ -w.1 + ⅟(2 : AF F) * (w.2 ⬝ᵥ -w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [add_dotProduct, dotProduct_add, neg_dotProduct, dotProduct_neg, dotProduct_comm y w.1,
      dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  have e' := congrArg ψ e
  rw [AddChar.map_add_eq_mul ψ _ ((x + -w.1) ⬝ᵥ y), AddChar.map_add_eq_mul ψ _ (x ⬝ᵥ (y + w.2))] at e'
  simp only [neg_add_cancel_right]
  change _ * _ * ψ ((x + -w.1) ⬝ᵥ y) = _ * (_ * ψ (x ⬝ᵥ (y + w.2)))
  linear_combination φ x * e'

theorem realised_weyl : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  intro F _ _ ψ hψ κ _ _
  have hk : ∀ φ ∈ schA F κ, adelicFourierPi F φ ∈ schA F κ := fun φ hφ => by
    rw [schA_eq] at hφ ⊢
    exact adelicFourierPi_mem_schwartzBruhatPi hφ
  have hinv : ∀ φ ∈ schA F κ, adelicFourierPi F (adelicFourierPi F φ) = fun x => φ (-x) := fun φ hφ => by
    rw [schA_eq] at hφ
    exact adelicFourierPi_adelicFourierPi hφ
  refine ⟨adelicFourierPi F, hk, fun φ hφ => ⟨_, hk _ (hk _ (hk _ hφ)), ?_⟩, fun l hl => ?_, fun w φ _ => ?_⟩
  · rw [hinv _ (hk _ (hk _ hφ)), hinv _ hφ]
    simp only [neg_neg]
  · obtain ⟨T, hT⟩ := LinearMap.exists_extend (fourierLin (F := F) (κ := κ))
    have hT' : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ := fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩
    refine ⟨l ∘ₗ T, fun g hg => ?_, fun φ hφ => by rw [LinearMap.comp_apply, hT' φ hφ]⟩
    obtain ⟨U, hU⟩ := hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))
    refine ⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩
    rw [LinearMap.comp_apply, hT' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU,
      pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]
  · rw [act_weyl, fourier_schr hψ]

end GlobalTheory.AdelicSvN.Weyl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourierStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRealisedOnAdelicSchwartz_weyl_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  first | exact @GlobalTheory.AdelicSvN.Weyl.realised_weyl | exact GlobalTheory.AdelicSvN.Weyl.realised_weyl | (intros; apply GlobalTheory.AdelicSvN.Weyl.realised_weyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FrameDom

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexOrder

variable {n : ℕ} {Hm x₀ : Mt n} {q : ℕ}

theorem conjTranspose_map_conj (y : Mt n) : (y.map (starRingEnd ℂ))ᴴ = yᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem map_conj_conj (y : Mt n) : (y.map (starRingEnd ℂ)).map (starRingEnd ℂ) = y := by
  ext i j
  simp

theorem det_map_conj_ne {y : Mt n} (h : y.det ≠ 0) : (y.map (starRingEnd ℂ)).det ≠ 0 := by
  have e : y.map (starRingEnd ℂ) = (yᴴ)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e, det_transpose, det_conjTranspose]
  intro h0
  exact h (star_eq_zero.mp h0)

theorem neg_gram_mul (Hm x b : Mt n) : -((x * b)ᴴ * Hm * (x * b)) = bᴴ * (-(xᴴ * Hm * x)) * b := by
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem neg_gram_orth (h : OrthFr Hm q x₀) : -(x₀ᴴ * Hm * x₀) = diagonal (sv q) := by
  rw [h.2, ← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sgn_cast_eq q n, ← Matrix.diagonal_neg, neg_neg]

theorem sv_mul_self (a : Fin n) : sv q a * sv q a = 1 := by
  simp only [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.sv]
  split_ifs <;> norm_num

theorem det_diag_sv_ne : (diagonal (sv q) : Mt n).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => left_ne_zero_of_mul_eq_one (sv_mul_self a)

theorem det_ne_of_orth (h : OrthFr Hm q x₀) : x₀.det ≠ 0 ∧ Hm.det ≠ 0 := by
  have h1 : (x₀ᴴ * Hm * x₀).det ≠ 0 := by
    have e : x₀ᴴ * Hm * x₀ = -(diagonal (sv q)) := by rw [← neg_gram_orth h, neg_neg]
    rw [e, det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) det_diag_sv_ne
  rw [det_mul, det_mul] at h1
  exact ⟨right_ne_zero_of_mul h1, right_ne_zero_of_mul (left_ne_zero_of_mul h1)⟩

theorem neg_gram_isHermitian (h : OrthFr Hm q x₀) (x : Mt n) : (-(xᴴ * Hm * x)).IsHermitian := by
  obtain ⟨hx0, -⟩ := det_ne_of_orth h
  have hD : (x₀ᴴ * Hm * x₀)ᴴ = x₀ᴴ * Hm * x₀ := by
    rw [h.2, Matrix.diagonal_conjTranspose]
    congr 1
    ext a
    simp
  have hD' : x₀ᴴ * Hmᴴ * x₀ = x₀ᴴ * Hm * x₀ := by
    rw [← hD]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det x₀).mpr hx0.isUnit
  have hus : IsUnit x₀ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [det_conjTranspose]
    have hs : star x₀.det ≠ 0 := fun h0 => hx0 (star_eq_zero.mp h0)
    exact hs.isUnit
  have hH : Hmᴴ = Hm := hus.mul_left_cancel (hu.mul_right_cancel hD')
  exact (Matrix.isHermitian_conjTranspose_mul_mul x (hH : Hm.IsHermitian)).neg

theorem mul_upT_mem {x b : Mt n} (hx : x ∈ frDom Hm q) (hb : UpT b) : x * b ∈ frDom Hm q := by
  obtain ⟨hdet, hmin⟩ := hx
  refine ⟨by rw [det_mul]; exact mul_ne_zero hdet hb.1, fun i => ?_⟩
  have hbT : b.BlockTriangular id := fun a c hca => hb.2 a c hca
  have hN : (b.map (starRingEnd ℂ)).BlockTriangular id := fun a c hca => by
    simp [hb.2 a c hca]
  have hdiag : ∀ k, b k k ≠ 0 := by
    have := hb.1
    rw [Matrix.det_of_upperTriangular hbT] at this
    exact fun k => Finset.prod_ne_zero_iff.mp this k (Finset.mem_univ k)
  have e : -((x * b)ᴴ * Hm * (x * b)) =
      (b.map (starRingEnd ℂ))ᵀ * (-(xᴴ * Hm * x)) * (b.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
    rw [neg_gram_mul, ← conjTranspose_map_conj (b.map (starRingEnd ℂ)), map_conj_conj]
  rw [e, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj hN i]
  refine ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.pos_conj_mul ?_ (hmin i)
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  simpa using hdiag _

theorem unitary_mul_mem (hH : Hm.det ≠ 0) {u x : Mt n} (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) (hx : x ∈ frDom Hm q) :
    u * x ∈ frDom Hm q := by
  have hu' : uᴴ * Hm * u = Hm := hu
  have hg : (u * x)ᴴ * Hm * (u * x) = xᴴ * Hm * x := by
    have : (u * x)ᴴ * Hm * (u * x) = xᴴ * (uᴴ * Hm * u) * x := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hu']
  have hu0 : u.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hu'
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact hH this.symm
  refine ⟨by rw [det_mul]; exact mul_ne_zero hu0 hx.1, fun i => ?_⟩
  rw [hg]
  exact hx.2 i

theorem neg_gram_conj (h : OrthFr Hm q x₀) (y : Mt n) :
    -((x₀ * y.map (starRingEnd ℂ))ᴴ * Hm * (x₀ * y.map (starRingEnd ℂ))) = Gy q y := by
  rw [neg_gram_mul Hm x₀ (y.map (starRingEnd ℂ)), neg_gram_orth h, conjTranspose_map_conj]
  rfl

theorem mem_of_ok (h : OrthFr Hm q x₀) {y : Mt n} (hy : Ok q y) : x₀ * y.map (starRingEnd ℂ) ∈ frDom Hm q := by
  refine ⟨?_, fun i => ?_⟩
  · rw [det_mul]
    exact mul_ne_zero (det_ne_of_orth h).1 (det_map_conj_ne (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.det_ne_of_ok hy))
  · rw [neg_gram_conj h]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.lead_pos hy i (Nat.le_of_lt_succ i.isLt)

theorem ok_of_gy {y : Mt n} (h : Gy q y = diagonal (sv q)) : Ok q y := by
  show (diagonal (sv q) * Gy q y).PosDef
  rw [h, diagonal_mul_diagonal]
  have e : (fun a : Fin n => sv q a * sv q a) = fun _ => (1 : ℂ) := funext sv_mul_self
  rw [e, diagonal_one]
  exact Matrix.PosDef.one

theorem ok_one : Ok q (1 : Mt n) := by
  refine ok_of_gy ?_
  show (1 : Mt n)ᵀ * diagonal (sv q) * (1 : Mt n).map (starRingEnd ℂ) = diagonal (sv q)
  rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem base_mem (h : OrthFr Hm q x₀) : x₀ ∈ frDom Hm q := by
  have := mem_of_ok h (ok_one (q := q) (n := n))
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem isOpen_frDom (Hm : Mt n) (q : ℕ) : IsOpen (frDom Hm q) := by
  have e : frDom Hm q = {x : Mt n | x.det ≠ 0} ∩
      ⋂ i : Fin (n + 1), {x : Mt n | 0 < psgn q i * (lminor (-(xᴴ * Hm * x)) i).re} := by
    ext x
    simp only [frDom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsOpen.inter (isOpen_ne_fun continuous_id.matrix_det continuous_const) ?_
  refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  exact ((((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id).neg).matrix_submatrix _ _).matrix_det

theorem isPreconnected_frDom (h : OrthFr Hm q x₀) : IsPreconnected (frDom Hm q) := by
  have hOk : IsPreconnected {y : Mt n | Ok q y} := by
    have e : {y : Mt n | Ok q y} =
        (fun y : Unit → Mt n => y ()) '' {y : Unit → Mt n | ∀ i, Ok q (y i)} := by
      ext y
      constructor
      · intro hy
        exact ⟨fun _ => y, fun _ => hy, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz ()
    rw [e]
    exact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_ok (p0 := q) (r := n) (ι := Unit)).image _
      (continuous_apply _).continuousOn
  have hUp : IsPreconnected {b : Mt n | UpT b} := by
    have e : {b : Mt n | UpT b} =
        (fun b : Unit → Mt n => b ()) '' {b : Unit → Mt n |
          ∀ i, (b i).det ≠ 0 ∧ ∀ a c : Fin n, c < a → b i a c = 0} := by
      ext b
      constructor
      · intro hb
        exact ⟨fun _ => b, fun _ => hb, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz ()
    rw [e]
    exact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_upper (r := n) (ι := Unit)).image _
      (continuous_apply _).continuousOn
  have hT : IsPreconnected ((fun y : Mt n => x₀ * y.map (starRingEnd ℂ)) '' {y : Mt n | Ok q y}) :=
    hOk.image _ (continuous_const.matrix_mul
      (continuous_id.matrix_map Complex.continuous_conj)).continuousOn
  have hTsub : (fun y : Mt n => x₀ * y.map (starRingEnd ℂ)) '' {y : Mt n | Ok q y} ⊆ frDom Hm q := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_of_ok h hy
  refine isPreconnected_of_forall x₀ fun x hx => ?_
  have hxB : IsPreconnected ((fun b : Mt n => x * b) '' {b : Mt n | UpT b}) :=
    hUp.image _ (continuous_const.matrix_mul continuous_id).continuousOn
  have hxBsub : (fun b : Mt n => x * b) '' {b : Mt n | UpT b} ⊆ frDom Hm q := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_upT_mem hx hb

  obtain ⟨b, hbdet, hbT, hbeq⟩ := GlobalTheory.UnitFrames.exists_upper_conj_eq_signature q (-(xᴴ * Hm * x))
    (neg_gram_isHermitian h x) hx.2
  set c : Mt n := b.map (starRingEnd ℂ) with hc
  have hcU : UpT c := by
    refine ⟨det_map_conj_ne hbdet, fun a d hda => ?_⟩
    simp [hc, hbT hda]
  have hgc : -((x * c)ᴴ * Hm * (x * c)) = diagonal (sv q) := by
    rw [neg_gram_mul, hc, conjTranspose_map_conj, hbeq, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.sgn_cast_eq]
  have hx0 := (det_ne_of_orth h).1
  set y : Mt n := (x₀⁻¹ * (x * c)).map (starRingEnd ℂ) with hy
  have hxy : x₀ * y.map (starRingEnd ℂ) = x * c := by
    rw [hy, map_conj_conj, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv x₀ hx0.isUnit, Matrix.one_mul]
  have hyOk : Ok q y := by
    refine ok_of_gy ?_
    rw [← neg_gram_conj h y, hxy, hgc]
  refine ⟨_ ∪ _, Set.union_subset hTsub hxBsub, Or.inl ⟨1, ok_one, ?_⟩,
    Or.inr ⟨1, ⟨by simp, fun a c hca => by simp [Matrix.one_apply_ne (ne_of_lt hca).symm]⟩, Matrix.mul_one x⟩,
    hT.union (x * c) ⟨y, hyOk, hxy⟩ ⟨c, hcU, rfl⟩ hxB⟩
  show x₀ * (1 : Mt n).map (starRingEnd ℂ) = x₀
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]

end GlobalTheory.HolDict.FrameDom


open GlobalTheory.HolDict.FrameDom in
theorem GlobalTheory.HolDict.frDoms_open_preconnected_stable : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → IsOpen (frDoms Hm q) ∧ IsPreconnected (frDoms Hm q) ∧ (∀ u ∈ UG Hm, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) → ∀ x ∈ frDoms Hm q, (fun τ => (u τ * Matrix.of (x τ) * b τ : Mt n)) ∈ frDoms Hm q) ∧ (fun τ => (x₀ τ : Mt n)) ∈ frDoms Hm q := by
  intro n ι _ _ Hm q x₀ h
  have e : frDoms Hm q = Set.univ.pi fun τ => frDom (Hm τ) (q τ) := by
    ext x
    exact ⟨fun hx τ _ => hx τ, fun hx τ => hx τ (Set.mem_univ τ)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e]
    exact isOpen_set_pi Set.finite_univ fun τ _ => isOpen_frDom (Hm τ) (q τ)
  · rw [e]
    exact isPreconnected_univ_pi fun τ => isPreconnected_frDom (h τ)
  · intro u hu b hb x hx τ
    exact mul_upT_mem (unitary_mul_mem (det_ne_of_orth (h τ)).2 (hu τ) (hx τ)) (hb τ)
  · intro τ
    exact base_mem (h τ)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStableStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negativeFrameDomainProduct_open_preconnected_stable : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → IsOpen (frDoms Hm q) ∧ IsPreconnected (frDoms Hm q) ∧ (∀ u ∈ UG Hm, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) → ∀ x ∈ frDoms Hm q, (fun τ => (u τ * Matrix.of (x τ) * b τ : Mt n)) ∈ frDoms Hm q) ∧ (fun τ => (x₀ τ : Mt n)) ∈ frDoms Hm q := by
  first | exact @GlobalTheory.HolDict.frDoms_open_preconnected_stable | exact GlobalTheory.HolDict.frDoms_open_preconnected_stable | (intros; apply GlobalTheory.HolDict.frDoms_open_preconnected_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
noncomputable section

namespace GlobalTheory.ChrWUnif

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

theorem valued_unifAt (v : Pl F) : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have hu : valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    e.lt_one_iff_lt_one.1 (hu ▸ uniformizer_lt_one)
  have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
  have hle1 : valuation (Fv F v) ((π : F) : Fv F v) ≤ valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) := by
    rw [hu, le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) := hπv ▸ (e _ _).1 hle1
  rw [← WithZero.exp_log h0] at hlt hge ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hge
  congr 1
  omega

theorem chrW_unifAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E)
    (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UnrAt χ (splitPrime t)) : chrW χ t (unifAt v) = val χ (splitPrime t) := by
  refine h.locChar_eq_val ?_
  show Valued.v (complMap (splitPrime_under t) ((unifAt v : (Fv F v)ˣ) : Fv F v)) = WithZero.exp (-1 : ℤ)
  rw [GlobalTheory.LFun.SplitTie.valued_complMap t (splitPrime_under t), valued_unifAt]

end GlobalTheory.ChrWUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizerStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_at_uniformizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), UnrAt χ (splitPrime t) → chrW χ t (unifAt v) = val χ (splitPrime t) := by
  first | exact @GlobalTheory.ChrWUnif.chrW_unifAt | exact GlobalTheory.ChrWUnif.chrW_unifAt | (intros; apply GlobalTheory.ChrWUnif.chrW_unifAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitary
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FdDom

open ReciprocityTheory.ChartRestriction.G.FD

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [IsCMField E] in
theorem gram_neg_transpose (τ : E →+* ℂ) (H : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ (-Hᵀ) x = (-(xᴴ * H.map τ * x))ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem lminor_transpose (A : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) : lminor Aᵀ i = lminor A i := by
  unfold lminor
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]

theorem map_mem_UH (τ : E →+* ℂ) (H g : Matrix (Fin r) (Fin r) E)
    (hg : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) (g.mulVec x) (g.mulVec y) = ReciprocityTheory.ChartRestriction.G.FD.herm (-Hᵀ) x y) :
    g.map τ ∈ Formalism.QuantumDeterminants.UH (H.map τ) := by
  change (g.map τ)ᴴ * H.map τ * g.map τ = H.map τ
  ext b a
  have h := congrArg τ (hg (Pi.single a 1) (Pi.single b 1))
  have hc : ∀ z : E, τ (ReciprocityTheory.ChartRestriction.G.FD.cc z) = starRingEnd ℂ (τ z) := fun z =>
    IsCMField.complexEmbedding_complexConj E τ z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul, hc, Matrix.neg_apply,
    Matrix.transpose_apply, map_neg, Pi.single_apply, apply_ite τ, apply_ite (starRingEnd ℂ), map_one, map_zero,
    ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, RCLike.star_def]
  have h2 : (∑ x, ∑ y, if x = a then if y = b then -τ (H y x) else 0 else 0) = -τ (H b a) := by
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
    simp
  rw [← neg_inj, ← h2, ← h]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := by
  intro s t h
  apply D.eTau.injective
  apply Subtype.ext
  apply (D.host.gal).symm.injective
  exact AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)

theorem dom_iff_frDoms : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ k, ∃ e : D.what₂.Tau ≃ (X k).Ψ, (∀ ρ, (e ρ).1 = tauE D ρ) ∧ (∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r, x ∈ (X k).dom ↔ (fun ρ a b => x (e ρ) (Fin.cast hr a) (Fin.cast hr b)) ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ))) ∧ ∀ γ ∈ (X k).Γ, ∀ ρ, Matrix.reindex (finCongr hr.symm) (finCongr hr.symm) ((γ : Matrix (Fin r) (Fin r) D.host.E).map (tauE D ρ)) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  intro D θ V S M w r hr Comp X la dict mu c Kf _ hG k
  subst hr
  have hΨ := hG.base.1 k
  have hp := hG.base.2.1 k
  have hGm : (X k).Gm = -V.gramᵀ := (hG.model k).1
  let f : D.what₂.Tau → (X k).Ψ := fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t h => tauE_injective D (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := (hΨ τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext hρ.symm⟩
  refine ⟨Equiv.ofBijective f hf, fun _ => rfl, fun x => ?_, fun γ hγ ρ => ?_⟩
  · change (∀ τ : (X k).Ψ, _) ↔ ∀ ρ, _
    rw [← (Equiv.ofBijective f hf).forall_congr_right]
    refine forall_congr' fun ρ => ?_
    simp only [dmin, hGm, gram_neg_transpose, lminor_transpose, hp ρ]
    rfl
  · have h := ((X k).Γ_stab γ hγ).1
    rw [hGm] at h
    exact map_mem_UH (tauE D ρ) V.gram _ h

end GlobalTheory.HolDict.FdDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDomainFramesEqGramFramesUnitaryStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagDomain_frames_eq_gramFrames_unitary : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ k, ∃ e : D.what₂.Tau ≃ (X k).Ψ, (∀ ρ, (e ρ).1 = tauE D ρ) ∧ (∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r, x ∈ (X k).dom ↔ (fun ρ a b => x (e ρ) (Fin.cast hr a) (Fin.cast hr b)) ∈ frDoms (gramAt D V) (fun ρ => nNeg (M.ε ρ))) ∧ ∀ γ ∈ (X k).Γ, ∀ ρ, Matrix.reindex (finCongr hr.symm) (finCongr hr.symm) ((γ : Matrix (Fin r) (Fin r) D.host.E).map (tauE D ρ)) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  first | exact @GlobalTheory.HolDict.FdDom.dom_iff_frDoms | exact GlobalTheory.HolDict.FdDom.dom_iff_frDoms | (intros; apply GlobalTheory.HolDict.FdDom.dom_iff_frDoms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeLatticeGermSystem
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AwayOrb.Cpt
open scoped RestrictedProduct
variable {p : ℕ} [Fact p.Prime]

theorem eventually_int_of_isCompact (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ w in Filter.cofinite, ∀ x ∈ K, AfP.eval w x ∈ w.1.adicCompletionIntegers ℚ := by
  let U : Finset (AwayP p) → Set (AfP p) := fun F =>
    {f : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] |
      ∀ i, i ∉ F → f.1 i ∈ (i.1.adicCompletionIntegers ℚ : Set (i.1.adicCompletion ℚ))}
  have hU : ∀ F, IsOpen (U F) := fun F =>
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun i => i ∉ F)
  have hcov : K ⊆ ⋃ F, U F := by
    intro x _
    have hx := x.2
    rw [Filter.eventually_cofinite] at hx
    refine Set.mem_iUnion.2 ⟨hx.toFinset, fun i hi => ?_⟩
    by_contra h
    exact hi (hx.mem_toFinset.2 h)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  let S : Finset (AwayP p) := t.biUnion id
  rw [Filter.eventually_cofinite]
  refine S.finite_toSet.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨x, hxK, hxw⟩ := hw
  obtain ⟨F, hF, hxF⟩ := Set.mem_iUnion₂.1 (ht hxK)
  by_contra hwS
  exact hxw (hxF w fun hwF => hwS (Finset.mem_biUnion.2 ⟨F, hF, hwF⟩))

theorem repr_map_eval (G : HTGroup p) (w : AwayP p) (x : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr
        (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) x) i =
      AfP.eval w ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul r c =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]

theorem continuous_coord (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_coord_inv (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_sim (G : HTGroup p) :
    Continuous fun x : G.GAf => (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)

theorem continuous_sim_inv (G : HTGroup p) :
    Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)

theorem eventually_mem_intPts (G : HTGroup p) (Ω : Set G.GAf) (hΩ : IsCompact Ω) :
    ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i) ∈
        w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord_inv G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h3 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim G))
  have h4 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim_inv G))
  filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4 h hh
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e := repr_map_eval G w (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i
    have := hw1 i h hh
    rw [← e] at this
    exact this
  · have e := repr_map_eval G w ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C) i
    have := hw2 i h hh
    rw [← e] at this
    exact this
  · exact hw3 _ (Set.mem_image_of_mem _ hh)
  · exact hw4 _ (Set.mem_image_of_mem _ hh)

end GlobalTheory.AwayOrb.Cpt

theorem GlobalTheory.AwayOrb.eventually_compL_mem_intPts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf),
    IsCompact Ω → ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w :=
  fun _ _ G Ω hΩ => GlobalTheory.AwayOrb.Cpt.eventually_mem_intPts G Ω hΩ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentation
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRep


set_option maxHeartbeats 1000000 in
theorem exists_cusp_rep : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  intro D G _ T κ i lev _ hL hW
  have hnat := fun f (hf : f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) => ((mem_cusp _ _ _ _ _ _).1 hf).1.1
  exact ⟨{ toFun := fun g => (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev g).restrict (hW g)
           map_one' := LinearMap.ext fun F => Subtype.ext
             (actL_one _ _ _ hL.total hL.func hL.one (hnat _ F.2))
           map_mul' := fun g g' => LinearMap.ext fun F => Subtype.ext
             (actL_mul _ _ _ hL.total hL.func hL.mul g g' (hnat _ F.2)) },
    fun _ _ => rfl⟩

end GlobalTheory.LevelRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentationStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_action_cusp_form_representation : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.LevelRep.exists_cusp_rep | exact GlobalTheory.LevelRep.exists_cusp_rep | (intros; apply GlobalTheory.LevelRep.exists_cusp_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem pos_iff_smul_toV (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) : c ≠ 0 →
    (0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ↔ 0 < (star (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ⬝ᵥ
      (herm G v β *ᵥ (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)))).re) := by
  intro hc
  set M : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) with hM
  set H := herm G v β
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β g
  have hs : (0 : ℚ) < (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := g.2.2
  set s : ℚ := (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have key : star (c • (M *ᵥ z)) ⬝ᵥ (H *ᵥ (c • (M *ᵥ z))) =
      ((Complex.normSq c * s : ℝ) : ℂ) * (star z ⬝ᵥ (H *ᵥ z)) := by
    have e1 : star (M *ᵥ z) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star z ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, e1, hsim, Matrix.smul_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp [mul_comm]
  rw [key, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq c * (s : ℝ) :=
    mul_pos (Complex.normSq_pos.2 hc) (by exact_mod_cast hs)
  exact (mul_pos_iff_of_pos_left hpos).symm

end GlobalTheory.LKCx
end
