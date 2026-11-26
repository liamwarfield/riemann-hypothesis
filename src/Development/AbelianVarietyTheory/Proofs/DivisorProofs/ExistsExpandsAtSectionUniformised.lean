module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem IntFam.exists_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G), IsSemiAbelian G → ∀ k : ℕ, 1 ≤ k → ∀ F : IntFam (maximalIdeal R) D.toPre k, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ F.f := by
  intro R _ _ _ hB D A G _ _ U hG k hk F
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have : IsNoetherianRing R := hR.1
  have := hG.geomConnected
  obtain ⟨s, ⟨r, hr, σ₀, f₀, -, hf₀, hE⟩, -⟩ := (U.expand k hk).2 F.F
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    rw [scal, map_one, map_one]
  have h₁ : ∀ α j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (F.f α).f j := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _
      (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (h1 ▸ F.ext α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₀ α)
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R _ hR D A G U.toUnifPre k r hr σ₀ f₀ F.f h₁ hE
  exact ⟨σ, GlobalTheory.expandsAt_cancel_of_ne_zero R _ D A G U.toUnifPre k r hr σ σ₀ F.f f₀ hσ h₁ hE⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_expandsAt_section_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G), IsSemiAbelian G → ∀ k : ℕ, 1 ≤ k → ∀ F : IntFam (maximalIdeal R) D.toPre k, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ F.f := by
  first | exact @GlobalTheory.Mum.IntFam.exists_expandsAt | exact GlobalTheory.Mum.IntFam.exists_expandsAt | (intros; apply GlobalTheory.Mum.IntFam.exists_expandsAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def IsEigTan {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (τ : E →+* ℂ)
    (w : Sp (DualNumber K) ⟶ Z.t.G.left) : Prop :=
  IsTanAtG Z.t x w ∧ ∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w


omit [NumberField E] [IsCMField E] in
def trCo {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U U' : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    (f' : Fin r → Γ(M, U')) (b a : Fin r) : Γ(X, U ⊓ U') :=
  (hf.basis inf_le_left).repr (Twist.resM M inf_le_right (f' a)) b

abbrev FrAssign {X W : Scheme.{0}} (M : X.Modules) (r : ℕ) (jB : W ⟶ X) : Type 1 :=
  ∀ (U : X.Opens) (f : Fin r → Γ(M, U)), VB.IsFrame f → ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W),
    ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)


end Free

end GlobalTheory.ArLieBase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.ChartGlue GlobalTheory.Points
open Topology Filter

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem cHess_zero (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

variable {A B : LB X} {c : AlgChart p σ D} {y : CxPts p σ}

theorem hess_tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf) (hy : y ∈ c.e.source)
    {a : A.ι} {b : B.ι} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (ψ.tens φ) (a, b) y = c.hess ψ a y + c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (hψ a) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    ((contDiffOn_chart (hφ b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
  simp only [one_mul, Complex.ofReal_one, one_smul] at e
  exact e

theorem hess_dual {φ : Weight p σ B} (hφ : φ.IsCInf) (hy : y ∈ c.e.source) {b : B.ι}
    (hb : y ∈ ptsIn p σ (B.U b)) : c.hess φ.dual b y = -c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U b))
  have hm := mem_over c.e hy hb
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ b) c) (-1) hm
  rw [cHess_zero, zero_add] at e
  simp only [zero_add, neg_one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul] at e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.dual.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y) =
    -ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((φ.φ b (c.e.symm v) : ℝ) : ℂ)) (c.e y)
  refine (congrArg (fun g => ReciprocityTheory.L2DbarEstimates.cHess D g (c.e y)) ?_).trans e
  funext v
  simp only [Function.comp_apply]
  exact Complex.ofReal_neg _

end GlobalTheory.FlatMass

namespace GlobalTheory.FlatMass

open GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end GlobalTheory.FlatMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Taut

theorem X_mem_nonZeroDivisors (W : Type) [CommRing W] {σ : Type} (k : σ) :
    (MvPolynomial.X k : MvPolynomial σ W) ∈ nonZeroDivisors (MvPolynomial σ W) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun p hp => ?_, fun p hp => ?_⟩
  · ext m
    have := congrArg (AddMonoidAlgebra.coeff · (m + Finsupp.single k 1)) hp
    rwa [mul_comm, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this
  · ext m
    have := congrArg (AddMonoidAlgebra.coeff · (m + Finsupp.single k 1)) hp
    rwa [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this

theorem monomial_chart : ∀ {o : Type} [CommRing o] {ζ : o} (g n : ℕ) (φ : InvFun ℤ), 1 ≤ n → ∀ C : Taut ζ g n φ,
    C.Q.IsMonomialTau C.t (fun k => (n : ℤ) • C.δ k) ∧ Module.finrank ℤ C.Q.X ≤ g ∧ IsCone id φ C.δ ∧
      (∀ z, z ≠ 0 → ∃ k, 0 < C.δ k z z) ∧ (∀ k, C.t k ≠ 0) := by
  intro o _ ζ g n φ _ C
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    obtain ⟨k, hk, hc⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator C.T (C.ψ.comp MvPolynomial.C) (fun k => C.ψ (MvPolynomial.X k))
      (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.Q C.e C.data a b
    let z : Fin C.N → ℤ := fun j => (n : ℤ) * (C.ε (.inr j) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)
    let w : C.Rˣ := ∏ j, (C.tor j).unit ^ z j
    refine ⟨k * Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹, ?_,
      GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
    rw [Units.val_mul, hk, Fintype.prod_sum_type]
    have hw : ((Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹ : (FractionRing C.R)ˣ) : FractionRing C.R) *
        ∏ j : Fin C.N, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inr j))) ^ z j = 1 := by
      rw [← Units.val_one, ← mul_inv_cancel (Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w)]
      simp [w, map_prod, Units.coe_prod, map_zpow]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ?_)
      exact (map_ne_zero_iff _ (IsFractionRing.injective C.R (FractionRing C.R))).2 (C.tor j).ne_zero
    have hl : ∏ i, algebraMap C.R (FractionRing C.R) (C.t i) ^ (((n : ℤ) • C.δ i) a b) =
        ∏ k : Fin C.m, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inl k))) ^
          ((n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)) := by
      rfl
    rw [hl, _root_.mul_assoc, mul_comm (∏ j : Fin C.N, _), hw, _root_.mul_one]
  · have h : Module.finrank ℤ C.Q.X = C.T.r := by
      rw [C.e.toIntLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    have := C.genus
    omega
  · exact C.cone.pull_equiv C.e.toIntLinearEquiv
  · intro z hz
    obtain ⟨k, hk⟩ := C.defin (C.e z) (by simpa using hz)
    exact ⟨k, hk⟩
  · intro k hk
    letI := C.ψ.toAlgebra
    haveI : Module.Flat (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R := C.compl.2.2.1
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C.R) (X_mem_nonZeroDivisors C.W (Sum.inl k : Fin C.m ⊕ Fin C.N))
    apply one_ne_zero (α := C.R)
    apply hreg
    show C.ψ (MvPolynomial.X (.inl k)) * 1 = C.ψ (MvPolynomial.X (.inl k)) * 0
    rw [show C.ψ (MvPolynomial.X (.inl k)) = 0 from hk]; simp

end GlobalTheory.TChart.Taut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValue
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.lift_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c)
    (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (φ ψ : G.A n →ₐ[R] D) :
    Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) =
      d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f (G.A n) D (toConv φ * toConv ψ).ofConv (t.y n) +
            (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f (G.A n) D φ (t.y n) + φ (d.h n)) -
          (fv d.f (G.A n) D ψ (t.y n) + ψ (d.h n))) := by
  set l : G.A n ⊗[R] G.A n →ₐ[R] D := Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) with hl
  have hc := (fv_isCoc_and_ev_eq R A d.f).1
  have e1 : l.comp Algebra.TensorProduct.includeLeft = φ := by
    simpa only [hl] using Algebra.TensorProduct.lift_comp_includeLeft φ ψ (fun _ _ ↦ Commute.all _ _)
  have e2 : l.comp Algebra.TensorProduct.includeRight = ψ := by
    simpa only [hl] using Algebra.TensorProduct.lift_comp_includeRight' φ ψ (fun _ _ ↦ Commute.all _ _)
  have e3 : l.comp (Bialgebra.comulAlgHom R (G.A n)) = (toConv φ * toConv ψ).ofConv := by
    apply AlgHom.ext
    intro a
    change l (Coalgebra.comul a) = (toConv φ * toConv ψ) a
    rw [AlgHom.convMul_apply, ofConv_toConv, ofConv_toConv, hl]
  have e4 : (toConv (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) *
      toConv Algebra.TensorProduct.includeRight).ofConv = Bialgebra.comulAlgHom R (G.A n) := by
    apply AlgHom.ext
    intro a
    simpa only [ofConv_toConv, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply,
      Bialgebra.comulAlgHom_apply]
      using AlgHom.convMul_apply
        (toConv (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n))
        (toConv Algebra.TensorProduct.includeRight) a
  have m := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
    (toConv Algebra.TensorProduct.includeRight)
  rw [e4] at m
  have a := d.add (G.A n ⊗[R] G.A n) D l (spOver Algebra.TensorProduct.includeLeft ≫ t.y n)
    (spOver Algebra.TensorProduct.includeRight ≫ t.y n)
  have c1 := hc _ _ _ Algebra.TensorProduct.includeLeft l (t.y n) (sm_whole _)
  have c2 := hc _ _ _ Algebra.TensorProduct.includeRight l (t.y n) (sm_whole _)
  have c3 := hc _ _ _ (Bialgebra.comulAlgHom R (G.A n)) l (t.y n) (sm_whole _)
  rw [← m, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e1, e2] at a
  rw [e1] at c1
  rw [e2] at c2
  rw [e3] at c3
  have h3 : l (Coalgebra.comul (d.h n)) = (toConv φ * toConv ψ).ofConv (d.h n) := by
    rw [← e3]; rfl
  have h1 : l (d.h n ⊗ₜ 1) = φ (d.h n) := by simp [hl]
  have h2 : l (1 ⊗ₜ d.h n) = ψ (d.h n) := by simp [hl]
  simp only [Dat.coc, cobOne_apply, map_sub, h1, h2, h3]
  rw [c1, c2, c3]
  linear_combination -a

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValueStatement
alias GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue :=
  GlobalTheory.PtExt.Dat.lift_coc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.ConjUnitary
open Matrix

theorem unitary_of_norm_preserving {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    V ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hn : ∀ v : EuclideanSpace ℂ (Fin N), ‖toEuclideanCLM (n := Fin N) (𝕜 := ℂ) V v‖ = ‖v‖ := by
    intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simpa using h v.ofLp
  have h1 := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 hn
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← ContinuousLinearMap.mul_def, ← map_mul,
    ← map_one (toEuclideanCLM (n := Fin N) (𝕜 := ℂ))] at h1
  rw [Matrix.mem_unitaryGroup_iff']
  exact (toEuclideanCLM (n := Fin N) (𝕜 := ℂ)).injective h1

theorem conj_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    (fun j => (starRingEnd ℂ) ((M *ᵥ fun k => (starRingEnd ℂ) (z k)) j)) =
      M.map (starRingEnd ℂ) *ᵥ z := by
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem conj_frame_unitary : ∀ (K : Type) [Field K] (N : ℕ) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.ChowHt.ConjCompat A → (∀ σ, (A σ).det ≠ 0) →
    ∀ σ : K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U := by
  intro K _ N A hC hdet σ
  set B := A ((starRingEnd ℂ).comp σ) with hBdef
  set A0 := A σ with hA0
  set C := A0.map (starRingEnd ℂ) with hCdef
  set V := B⁻¹ * C with hV
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 (hdet _)
  have hA0u : IsUnit A0.det := isUnit_iff_ne_zero.2 (hdet _)
  have hnorm : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have h := hC σ (A0 *ᵥ fun k => (starRingEnd ℂ) (z k))
    rw [← hBdef, ← hA0, conj_mulVec] at h
    unfold GlobalTheory.ChowHt.frameNorm at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA0u,
      Matrix.one_mulVec, ← hV] at h
    rw [Real.sqrt_inj (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)] at h
    rw [h]
    simp
  have hVu := unitary_of_norm_preserving V hnorm
  refine ⟨star V, Unitary.star_mem hVu, ?_⟩
  have hVs : V * star V = 1 := (Matrix.mem_unitaryGroup_iff).1 hVu
  have hBV : B * V = C := by
    rw [hV, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
  rw [← hBV, Matrix.mul_assoc, hVs, Matrix.mul_one]

end GlobalTheory.ConjUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_conjugate_embedding_eq_conj_mul_unitary : ∀ (K : Type) [Field K] (N : ℕ) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.ChowHt.ConjCompat A → (∀ σ, (A σ).det ≠ 0) →
    ∀ σ : K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U := by
  first | exact @GlobalTheory.ConjUnitary.conj_frame_unitary | exact GlobalTheory.ConjUnitary.conj_frame_unitary | (intros; apply GlobalTheory.ConjUnitary.conj_frame_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GrpPullPow

theorem isMonHom_of_mul_pts {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  · rw [MonObj.mul_eq_mul G, MonObj.mul_eq_mul H, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd]
    exact h (G ⊗ G) (fst G G) (snd G G)

theorem pr_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr hB hC hpr huniv
  have hw : ∀ a, (φB ≫ (pr a).left) ≫ C.hom = B'.hom ≫ t := fun a => by
    rw [Category.assoc, Over.w (pr a), hB.1.w]
  let pr' : Fin 8 → (B' ⟶ C') := fun a =>
    Over.homMk (hC.1.lift (φB ≫ (pr a).left) B'.hom (hw a)) (hC.1.lift_snd _ _ _)
  have h1 : ∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left := fun a => hC.1.lift_fst _ _ _
  have hpush : ∀ (T₁ : Over T') (x : T₁ ⟶ B') a,
      pushPt hC.1.w (x ≫ pr' a) = pushPt hB.1.w x ≫ pr a := by
    intro T₁ x a
    apply Over.OverMorphism.ext
    show (x.left ≫ (pr' a).left) ≫ χ = (x.left ≫ φB) ≫ (pr a).left
    rw [Category.assoc, h1, Category.assoc]
  refine ⟨pr', h1, fun a => ?_, fun T₁ y => ?_⟩
  · haveI := hpr a
    refine isMonHom_of_mul_pts _ fun T₁ x y => ?_
    apply Over.OverMorphism.ext
    apply hC.1.hom_ext
    · have e1 := hC.2 T₁ (x ≫ pr' a) (y ≫ pr' a) (pushPt hC.1.w (x ≫ pr' a))
        (pushPt hC.1.w (y ≫ pr' a)) rfl rfl
      have e2 := hB.2 T₁ x y (pushPt hB.1.w x) (pushPt hB.1.w y) rfl rfl
      rw [← e1, hpush, hpush, ← MonObj.mul_comp, Over.comp_left, Over.comp_left, Category.assoc, h1,
        ← Category.assoc, ← e2]
    · rw [Over.w, Over.w]
  · let T₀ : Over T := Over.mk (T₁.hom ≫ t)
    obtain ⟨x₀, hx₀, hu⟩ := huniv T₀ (fun a => pushPt hC.1.w (y a))
    have wx : x₀.left ≫ B.hom = T₁.hom ≫ t := Over.w x₀
    let X : T₁ ⟶ B' := Over.homMk (hB.1.lift x₀.left T₁.hom wx) (hB.1.lift_snd _ _ _)
    have hX : X.left ≫ φB = x₀.left := hB.1.lift_fst _ _ _
    refine ⟨X, fun a => ?_, fun x' hx' => ?_⟩
    · apply Over.OverMorphism.ext
      apply hC.1.hom_ext
      · show (X.left ≫ (pr' a).left) ≫ χ = (y a).left ≫ χ
        rw [Category.assoc, h1, ← Category.assoc, hX]
        exact congrArg (fun q => q.left) (hx₀ a)
      · rw [Over.w, Over.w]
    · have e : pushPt hB.1.w x' = x₀ := hu _ fun a => by
        rw [← hpush, hx' a]
      apply Over.OverMorphism.ext
      apply hB.1.hom_ext
      · rw [hX]; exact congrArg (fun q => q.left) e
      · rw [Over.w, Over.w]

end GlobalTheory.GrpPullPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPowerProjections_groupPullback : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  first | exact @GlobalTheory.GrpPullPow.pr_pull | exact GlobalTheory.GrpPullPow.pr_pull | (intros; apply GlobalTheory.GrpPullPow.pr_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHPos

theorem smoothOfRelativeDimension_of_holUnif {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (u : HolUnif A L g) : SmoothOfRelativeDimension g A.hom := by
  obtain ⟨D, hD⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ A hA
  obtain ⟨c, hc⟩ := GlobalTheory.AlgChart.exists_mem_source (p := A.hom) (σ := RingHom.id ℂ) (D := D)
    (GlobalTheory.HolUnifSec.pt u 0)
  have h1 : D ≤ g := GlobalTheory.HolUnifSec.dim_le u c hc
  have h2 : g ≤ D := by
    have hi : Function.Injective (fderiv ℂ (c.e ∘ GlobalTheory.HolUnifSec.pt u) 0).toLinearMap := by
      rw [ContinuousLinearMap.coe_coe]
      exact GlobalTheory.HolUnifSec.injective_fderiv u c hc
    have := LinearMap.finrank_le_finrank_of_injective hi
    simpa using this
  obtain rfl : D = g := le_antisymm h1 h2
  exact hD

end GlobalTheory.AHPos

theorem GlobalTheory.AHPos.exists_lb_of_posDef : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ u.IsAH Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hpos hint
  obtain ⟨A', _, hA', hsm, L', u', χ', hL', hΛ, hAH'⟩ :=
    GlobalTheory.T.riemann_theorem_nonprincipal_polarised_torus g u₀.Λ Hm u₀.discrete u₀.full hHm hpos hint
  obtain ⟨f, -, hf⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A A' g hA hA'
    (GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u₀) hsm L₀ L' u₀ u' LinearMap.id
    (fun x hx => (hΛ x).2 hx)
  obtain ⟨u₁, hex, hΛ₁, hfr⟩ := GlobalTheory.exists_holUnif_linComb A A' L₀ L' g g u₀ u' PUnit (fun _ => f)
    (fun _ => LinearMap.id) (fun _ => 1) (fun _ z => hf z)
  have hmem : ∀ l : u₁.Λ, (l : Fin g → ℂ) ∈ u'.Λ := fun l => (hΛ _).2 (hΛ₁ ▸ l.2)
  refine ⟨_, u₁, fun l => χ' ⟨l.1, hmem l⟩, LB.isLB_linComb hL' _ _, hex, hHm, hpos,
    fun l => hAH'.2.2.1 _, ?_⟩
  intro l j z hz
  rw [hex] at hz
  have hz' : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U (j PUnit.unit) := by
    rw [← LinearMap.id_apply (R := ℂ) z, hf z]
    exact (CubeValues.le_preimage_wchart (u₀.ex z).left L' (fun _ => f.left) j).1 hz PUnit.unit
  have e1 : u₁.fr j z = u'.fr (j PUnit.unit) z := by simpa using hfr j z
  have e2 : u₁.fr j (z + l) = u'.fr (j PUnit.unit) (z + l) := by simpa using hfr j (z + l)
  rw [e1, e2]
  exact hAH'.2.2.2 ⟨l.1, hmem l⟩ (j PUnit.unit) z hz'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitianStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbert_exists_lineBundle_posDef_hermitian : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ u.IsAH Hm χ := by
  first | exact @GlobalTheory.AHPos.exists_lb_of_posDef | exact GlobalTheory.AHPos.exists_lb_of_posDef | (intros; apply GlobalTheory.AHPos.exists_lb_of_posDef <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Mum

variable {X Y Z : Scheme.{0}} {L : LB X} {k k' : ℕ}

abbrev secGerm (u : Y ⟶ X) (y : Y) (s : H0 L k) (i : Fin 1 → L.ι) : Y.presheaf.stalk y :=
  gs u y (secChart L i) (s.f i)

theorem secRatioEq_iff_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} :
    SecRatioEq L u v s₁ s₂ t₁ t₂ ↔ ∀ (y : Y) (i i' : Fin 1 → L.ι), u y ∈ secChart L i → v y ∈ secChart L i' →
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i' := by
  have key : ∀ (y : Y) (i i' : Fin 1 → L.ι) (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s : H0 L k)
      (t : H0 L k'), gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
    intro y i i' hi hi' s t
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
    rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
    exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)
  refine ⟨fun h y i i' hi hi' => ?_, fun h i i' => fn_ext fun y hy => ?_⟩
  · rw [← key y i i' hi hi', ← key y i i' hi hi', h i i']
  · rw [key y i i' hy.1 hy.2, key y i i' hy.1 hy.2]
    exact h y i i' hy.1 hy.2

theorem exists_unit_secGerm (k : ℕ) (u : Y ⟶ X) (y : Y) {i j : Fin 1 → L.ι} (hi : u y ∈ secChart L i)
    (hj : u y ∈ secChart L j) :
    ∃ c : (Y.presheaf.stalk y)ˣ, ∀ s : H0 L k, secGerm u y s i = c.val * secGerm u y s j := by
  have hy : u y ∈ secChart L i ⊓ secChart L j := ⟨hi, hj⟩
  refine ⟨gm u y (secChart L i ⊓ secChart L j)
    ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g i j), fun s => ?_⟩
  have h := congrArg (gs u y (secChart L i ⊓ secChart L j)) (s.compat i j)
  refine (gs_res u y inf_le_left hy _).symm.trans (h.trans ((gs_mul u y _ hy _ _).trans ?_))
  exact congrArg₂ (· * ·) (gs_unit u y _ hy _) (gs_res u y inf_le_right hy _)

theorem secRatioEq_of_exists_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ y : Y, ∃ i i' : Fin 1 → L.ι, u y ∈ secChart L i ∧ v y ∈ secChart L i' ∧
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i') :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun y j j' hj hj' => ?_
  obtain ⟨i, i', hi, hi', e⟩ := h y
  obtain ⟨c, hc⟩ := exists_unit_secGerm k u y hj hi
  obtain ⟨c', hc'⟩ := exists_unit_secGerm k' v y hj' hi'
  rw [hc, hc, hc', hc']
  linear_combination (c.val * c'.val) * e

theorem secGerm_comp (w : Z ⟶ Y) (u : Y ⟶ X) (z : Z) (s : H0 L k) {i : Fin 1 → L.ι} (hi : u (w z) ∈ secChart L i) :
    secGerm (w ≫ u) z s i = (w.stalkMap z).hom (secGerm u (w z) s i) := by
  have key : ∀ a : Γ(X, secChart L i), gs (w ≫ u) z _ a = (w.stalkMap z).hom (gs u (w z) _ a) := fun a => by
    rw [gs_eq u (w z) _ hi, ← gs_pull w u z _ hi, gs_eq w z _ hi]
    exact (Scheme.Hom.germ_stalkMap_apply w _ z hi _).symm
  exact key _

theorem SecRatioEq.comp {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} (h : SecRatioEq L u v s₁ s₂ t₁ t₂)
    (w : Z ⟶ Y) : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun z i i' hi hi' => ?_
  rw [secGerm_comp w u z _ hi, secGerm_comp w u z _ hi, secGerm_comp w v z _ hi', secGerm_comp w v z _ hi',
    ← map_mul, ← map_mul, secRatioEq_iff_germ.1 h (w z) i i' hi hi']

theorem app_injective_of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] (W : Y.Opens) :
    Function.Injective (w.app W).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_basicOpen_eq_bot
  by_contra hne
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨z, hz⟩ := w.denseRange.exists_mem_open (Y.basicOpen a).isOpen ⟨y, hy⟩
  have hz' : z ∈ w ⁻¹ᵁ Y.basicOpen a := hz
  rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero] at hz'
  exact hz'

theorem SecRatioEq.of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] {u v : Y ⟶ X} {s₁ s₂ : H0 L k}
    {t₁ t₂ : H0 L k'} (h : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂) : SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  intro i i'
  apply app_injective_of_isDominant w
  refine fn_ext fun z hz => ?_
  have hz' : w z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := hz
  rw [gs_pull (𝟙 Z) w z _ hz', gs_pull (𝟙 Z) w z _ hz', Category.id_comp, gs_mul _ _ _ hz', gs_mul _ _ _ hz',
    gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz']
  exact (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).trans
    ((secRatioEq_iff_germ.1 h z i i' hz'.1 hz'.2).trans
      (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).symm)

def VeryAmpleAlong {K : Type} [CommRing K] {A : Scheme.{0}} (p : A ⟶ Spec (CommRingCat.of K)) (π : A ⟶ X)
    (L : LB X) {k m : ℕ} (σ : Fin (m + 1) → H0 L k) : Prop :=
  (⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) ∧ ∀ i, IsAffineOpen (π ⁻¹ᵁ nonzeroLocus (σ i)) ∧
    ∃ r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i)),
      (∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i) → π a ∈ secChart L c →
        secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i)) (r j) * secGerm π a (σ i) c) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSq
open NumberField
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCS

theorem norm_sum_sq_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (X lam : Fin N → ℂ) :
    ‖∑ j, X j * lam j‖ ^ 2 ≤ (∑ i, ‖(A⁻¹.mulVec X) i‖ ^ 2) * ∑ a, ‖∑ m, A m a * lam m‖ ^ 2 := by
  set Y := A⁻¹.mulVec X with hY
  have hX : X = A.mulVec Y := by
    rw [hY, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]
  have e : ∑ j, X j * lam j = ∑ a, Y a * ∑ m, A m a * lam m := by
    rw [hX]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  calc ‖∑ a, Y a * ∑ m, A m a * lam m‖ ^ 2 ≤ (∑ a, ‖Y a‖ * ‖∑ m, A m a * lam m‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
        simp only [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end GlobalTheory.FrameCS


open GlobalTheory.FrameCS in
theorem GlobalTheory.frame_semilinear_sq_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (σ : K →+* ℂ) (ℓ : W → ℂ), GlobalTheory.CompHt.IsFrame Nm W b g A → (∀ k, (gw k : V) = ∑ j, g j k • b j) → (∀ j, b j = ∑ k, c k j • (gw k : V)) → (∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ℓ x = ∑ k, σ (β k : K) * ℓ (u k)) → ∀ x : W, ‖ℓ x‖ ^ 2 ≤ Nm σ x ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 := by
  intro K V _ _ _ _ _ _ Nm W N n b g A c gw σ ℓ hF hg hc hℓ x
  set lam : Fin N → ℂ := fun j => ∑ k, σ (c k j) * ℓ (gw k) with hlam

  have h2 : ∀ k, ℓ (gw k) = ∑ j, σ (g j k) * lam j := by
    intro k
    set e : Fin n → K := fun l => ∑ j, g j k * c l j with he
    have hexp : (gw k : V) = ∑ l, e l • (gw l : V) := by
      rw [hg k]
      simp_rw [hc, he, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
      (Finset.univ.image e)
    choose β hβ using fun l => hd _ (Finset.mem_image_of_mem e (Finset.mem_univ l))
    have hβ' : ∀ l, ((β l : 𝓞 K) : K) = ((d : 𝓞 K) : K) * e l := fun l => by
      rw [← Algebra.smul_def, ← hβ l]
    have hx1 : (((d : 𝓞 K) • gw k : W) : V) = ∑ l, β l • (gw l : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul K, hexp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← algebraMap_smul K (β l), smul_smul]
      congr 1
      exact (hβ' l).symm
    have hx2 : (((d : 𝓞 K) • gw k : W) : V) = ∑ _i : Fin 1, (d : 𝓞 K) • (gw k : V) := by
      simp
    have e1 := hℓ n β gw _ hx1
    have e2 := hℓ 1 (fun _ => (d : 𝓞 K)) (fun _ => gw k) _ hx2
    simp only [Finset.univ_unique, Finset.sum_singleton] at e2
    have hd0 : σ ((d : 𝓞 K) : K) ≠ 0 := by
      rw [map_ne_zero, ne_eq, RingOfIntegers.coe_eq_zero_iff]
      exact nonZeroDivisors.coe_ne_zero d
    apply mul_left_cancel₀ hd0
    rw [← e2, e1]
    simp only [hβ', map_mul, hlam, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [he, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hxmem : (x : V) ∈ Submodule.span (𝓞 K) (Set.range fun k => (gw k : V)) := by
    have := hF.span
    have hfun : (fun k => ∑ j, g j k • b j) = fun k => (gw k : V) := funext fun k => (hg k).symm
    rw [hfun] at this
    rw [this]; exact x.2
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hxmem
  have h3 : ℓ x = ∑ j, σ (b.repr x j) * lam j := by
    rw [hℓ n β gw x hβ.symm]
    have hr : ∀ j, b.repr x j = ∑ k, (β k : K) * g j k := by
      intro j
      have hk : ∀ k, β k • (gw k : V) = ∑ j, ((β k : K) * g j k) • b j := by
        intro k
        rw [← algebraMap_smul K, hg k, Finset.smul_sum]
        simp_rw [smul_smul]
      rw [← hβ, Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      rw [Module.Basis.repr_sum_self]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hr, h2, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hN : Nm σ x ^ 2 = ∑ i, ‖((A σ)⁻¹.mulVec fun j => σ (b.repr x j)) i‖ ^ 2 := by
    rw [← hF.norm σ x, GlobalTheory.ChowHt.frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  have hu : ∀ a, ∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k) = ∑ m, A σ m a * lam m := by
    intro a
    simp only [hlam, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [hu, hN, h3]
  exact norm_sum_sq_le (A σ) (hF.herm σ) _ lam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSqStatement
open NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (σ : K →+* ℂ) (ℓ : W → ℂ), GlobalTheory.CompHt.IsFrame Nm W b g A → (∀ k, (gw k : V) = ∑ j, g j k • b j) → (∀ j, b j = ∑ k, c k j • (gw k : V)) → (∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ℓ x = ∑ k, σ (β k : K) * ℓ (u k)) → ∀ x : W, ‖ℓ x‖ ^ 2 ≤ Nm σ x ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 := by
  first | exact @GlobalTheory.frame_semilinear_sq_le | exact GlobalTheory.frame_semilinear_sq_le | (intros; apply GlobalTheory.frame_semilinear_sq_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem torMatch_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (g₂ : V →+* V₂) (β₂ : G₂.left ⟶ G'.left), Function.Injective g₂ → (∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V)) → ∀ ρ ρ₂, TorMatch U U' g β ρ → TorMatch U' U₂ g₂ β₂ ρ₂ → TorMatch U U₂ (g₂.comp g) (β₂ ≫ β) (ρ₂.comp ρ) := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ hVb G' _ _ hG' D' A' U' g β V₂ _ _ _ hV₂b G₂ _ _ hG₂ D₂ A₂ U₂ g₂ β₂
    hg₂ hkV ρ ρ₂ h₁ h₂
  intro F _ _ _ _ hF k hk τ τ₂ q q₂ a a₂ hτ₂ hττ hqy hqt hq₂y hq₂t ha ha₂
  have hinj : Function.Injective ((algebraMap (FractionRing V₂) F).comp ((algebraMap V₂ (FractionRing V₂)).comp g₂)) :=
    (algebraMap (FractionRing V₂) F).injective.comp ((IsFractionRing.injective V₂ (FractionRing V₂)).comp hg₂)
  letI : Algebra (FractionRing V) F := (IsFractionRing.lift hinj).toAlgebra
  have hV : ∀ v, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) v) =
      algebraMap (FractionRing V₂) F (algebraMap V₂ (FractionRing V₂) (g₂ v)) := fun v =>
    IsFractionRing.lift_algebraMap hinj v
  have hk' : IsUnit (k : V) := hkV k hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  let τ' : Multiplicative D'.toPre.X →* Fˣ := τ₂.comp (AddMonoidHom.toMultiplicative ρ₂)
  have hτ' : τ' ^ k = 1 := MonoidHom.ext fun χ => DFunLike.congr_fun hτ₂ _
  obtain ⟨q', hq'y, hq't⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (k := k) τ' hτ'
  obtain ⟨hV', _⟩ := hVb
  obtain ⟨f', ⟨i', -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV' D' A' G' hG' U' F k hk1
  have e₁ := h₁ F (fun r => by rw [hF, hV]; rfl) k hk τ τ' q q' a (f' q') hτ' hττ hqy hqt hq'y hq't ha ((i' _ _).2 rfl)
  have e₂ := h₂ F hV k hk' τ' τ₂ q' q₂ (f' q') a₂ hτ₂ (fun _ => rfl) hq'y hq't hq₂y hq₂t ((i' _ _).2 rfl) ha₂
  rw [e₁, reassoc_of% e₂]

end GlobalTheory.Poinc.Eq8
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyRelativeDimDrop
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory

theorem dim_ne_zero_of_isProjOver {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k)
    [IsIntegral Z] (hq : IsProjOver q) (hfin : Module.Finite ℤ k) (hc : CharZero Γ(Z, ⊤)) :
    topologicalKrullDim Z ≠ 0 := fun h0 => by
  obtain ⟨N, j, _, hj⟩ := hq
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)
  let t := q ≫ spMap (Int.castRingHom k)
  have : Flat t := (flat_int_iff_charZero t).2 hc
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap t (genericPoint_specializes (t (genericPoint Z)))
  have hs : Set.range t = Set.univ := by
    rw [← t.isClosedMap.isClosed_range.closure_eq]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec (Sp ℤ)).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ⟨z, hz⟩)))
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hs' := Set.range_eq_univ.1 hs
  obtain ⟨a, ha⟩ := hs' (⊥ : PrimeSpectrum ℤ)
  obtain ⟨b, hb⟩ := hs' (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2
    Int.prime_two⟩ : PrimeSpectrum ℤ)
  have e := congrArg PrimeSpectrum.asIdeal (hb.symm.trans (((hu b).trans (hu a).symm) ▸ ha))
  exact two_ne_zero (Ideal.span_singleton_eq_bot.1 e)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFractionFiniteNormalCover
open AlgebraicGeometry CategoryTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Geo.Tor


open GlobalTheory.Poinc.FinPts in
theorem GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₁ : M₁.Z) (z₂ : M₂.Z), q z₂ = z₁ → letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q _ hF hg z₁ z₂ hq x hx
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) := fun _ => rfl
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  have hz₂ : z₂ ∈ q ⁻¹ᵁ U := show q z₂ ∈ U by rw [hq]; exact hz
  obtain ⟨c, hc, d, hd, hd0, hdinv, e⟩ := GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ (hU.preimage q) z₂ hz₂ x hx
  exact ⟨c, (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc), d,
    (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hd), hd0, hdinv, e⟩
end
