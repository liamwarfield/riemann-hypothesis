module

public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSectionStab
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
namespace Formalism.FourierDecayAlt.P.BXiAsm
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem closed_of (hX : XiExists) : LemmaBClosed := Formalism.FourierDecayAlt.P.b_lemmaBClosed_of hX

theorem norm_of (hX : XiExists) : LemmaBNorm :=
  Formalism.FourierDecayAlt.Final.lemma_b_norm_of_parts (closed_of hX) Formalism.FourierDecayAlt.Final.conjugation_invariance_all Formalism.FourierDecayAlt.Final.dilation_jacobian_all
    Formalism.FourierDecayAlt.Final.integral_bound_all

theorem any_of (hX : XiExists) : LemmaBAny :=
  Formalism.FourierDecayAlt.Final.lemma_b_from_norm_bound (norm_of hX) Formalism.FourierDecayAlt.Final.integral_norm_bound_variant_b

end Formalism.FourierDecayAlt.P.BXiAsm

namespace Formalism.FourierDecayAlt.P

theorem b_any_of_xi : Formalism.FourierDecayAlt.B2.LemmaBAny := Formalism.FourierDecayAlt.P.BXiAsm.any_of exists_auxiliary_xi

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefTraceCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def BsAt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0) :
    B.RealPlaceData P.k P.r Wp Wq :=
  { Bs with μsec := μ0, sec := h0 }

def GTRMove : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0)
      (e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameB P (BsAt P Bs μ0 h0) e0 →
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e Φ = trR P (BsAt P Bs μ0 h0) e0 Φ

def GTRConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ KapF P Bs d e ∧
      ∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ'

def GTRRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ ρ : M.Ty P, ∃ m : ℤ, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + ((m : ℂ)) • trR P Bs e Φ ρ

def GTRInt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ ρ : M.Ty P, ∃ n : ℤ, uSum P - rhoSum P ρ = n

def GTRTrans : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ (ρ : M.Ty P) (m : ℂ),
        (∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
          trR P Bs e ((ThetaNF P d).1 Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
            fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + m • trR P Bs e Φ ρ) →
        ∀ ζ ∈ Ann P, ζ * A ρ ζ + star ζ * B ρ ζ =
          m + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)

theorem poly_coeff_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = 0) : ∀ j < N, a j = 0 := by
  intro j hj
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (a j)).mp ?_
  intro f
  have hp0 : (∑ i ∈ Finset.range N, Polynomial.C (f (a i)) * Polynomial.X ^ i : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro Y
    have hY := congrArg f (h Y)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hY
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← hY]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hc := congrArg (fun q => q.coeff j) hp0
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj] using hc

theorem poly_coeff_eq {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a b : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = ∑ j ∈ Finset.range N, Y ^ j • b j) :
    ∀ j < N, a j = b j := by
  intro j hj
  have hz : ∀ Y : ℂ, ∑ i ∈ Finset.range N, Y ^ i • (a - b) i = 0 := by
    intro Y
    simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, h Y, sub_self]
  exact sub_eq_zero.mp (poly_coeff_zero N (a - b) hz j hj)

theorem pr_fst_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (Y : ℂ) (x : Q.Pr V) : (Y • x).1 = Y • x.1 := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

theorem pr_fst_add {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : Q.Pr V) : (x + y).1 = x.1 + y.1 := rfl

theorem pr_fst_one {V : Type*} [AddCommGroup V] [Module ℂ V] : (1 : Q.Pr V).1 = 1 := rfl

theorem pr_fst_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (s : Finset ℕ) (f : ℕ → Q.Pr V) :
    (∑ j ∈ s, f j).1 = ∑ j ∈ s, (f j).1 := Prod.fst_sum

theorem final_arith (P : M.Par) (ρ : M.Ty P) (A ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (m N : ℤ)
    (hN : uSum P - rhoSum P ρ = N)
    (hA : ζ * A + star ζ * star A =
      (m : ℂ) + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)) :
    (ζ * (modA P ρ ζ - A)).re = ((N - m : ℤ) : ℝ) / 2 := by
  have hpos : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  have hne : ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hpos.ne'
  have haC : M.aC P ρ = uSum P / 2 - rhoSum P ρ := rfl
  have hre := congrArg Complex.re hA
  have h1 : (ζ * A + star ζ * star A).re = 2 * (ζ * A).re := by
    rw [← star_mul', Complex.add_re, Complex.star_def, Complex.conj_re]; ring
  rw [h1, Complex.add_re, Complex.intCast_re, Complex.ofReal_re] at hre
  have h2 : ζ * modA P ρ ζ = ((M.aC P ρ * Complex.normSq ζ / (Complex.normSq ζ - P.TT) : ℝ) : ℂ) := by
    unfold modA
    rw [Complex.star_def]
    push_cast
    rw [← Complex.mul_conj]
    field_simp
  rw [mul_sub, Complex.sub_re, h2, Complex.ofReal_re, haC]
  have hA' : (ζ * A).re = ((m : ℝ) + (-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT))) / 2 := by
    linarith
  rw [hA']
  push_cast
  rw [← hN]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDerivativeHolds
namespace Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

open Formalism.FourierDecayAlt.PB Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem localCores : Formalism.FourierDecayAlt.PB.LocalCores :=
  ⟨Formalism.FourierDecayAlt.Final.jx_pSDAgree,
   Formalism.FourierDecayAlt.Final.jx_schurProduct,
   Formalism.FourierDecayAlt.Final.jx_productDomination,
   Formalism.FourierDecayAlt.Final.jx_diagScale,
   Formalism.FourierDecayAlt.Final.jx_diagPhase,
   Formalism.FourierDecayAlt.Final.jx_blockDiagPSD,
   Formalism.FourierDecayAlt.Final.jx_productLemma,
   Formalism.FourierDecayAlt.Final.jx_scaleOk,
   Formalism.FourierDecayAlt.Final.jx_phaseOk,
   Formalism.FourierDecayAlt.Final.jx_outsideSysOk,
   Formalism.FourierDecayAlt.Final.jx_outsideDomination,
   Formalism.FourierDecayAlt.Final.jx_localPullback,
   Formalism.FourierDecayAlt.Final.jx_localUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_topPullback,
   Formalism.FourierDecayAlt.Final.jx_topUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_globalOfLocal,
   Formalism.FourierDecayAlt.Final.jx_uniformMajorantOn,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromSystems,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromFamilies,
   Formalism.FourierDecayAlt.Final.jx_kernelOfLocal,
   Formalism.FourierDecayAlt.Final.jx_localKernelPSD,
   Formalism.FourierDecayAlt.Final.tc_domMinOfText,
   Formalism.FourierDecayAlt.Final.tc_domAfterOfLocal,
   Formalism.FourierDecayAlt.Final.gram_determinant_dual_bound_a,
   Formalism.FourierDecayAlt.Final.parahoric_gram_matrix,
   Formalism.FourierDecayAlt.Final.zero_level_ones_vector,
   Formalism.FourierDecayAlt.Final.singleBlockParseval_true,
   Formalism.FourierDecayAlt.Final.theta_equality_first,
   Formalism.FourierDecayAlt.Final.singleBlockThetaProps_true,
   Formalism.FourierDecayAlt.Final.ns_support,
   Formalism.FourierDecayAlt.Final.ns_block_diagonal,
   Formalism.FourierDecayAlt.Final.latticeAverage_of_gram⟩

theorem globalCores : Formalism.FourierDecayAlt.PB.GlobalCores :=
  ⟨Formalism.FourierDecayAlt.Final.tc_theoremAAfter,
   Formalism.FourierDecayAlt.Final.tc_recursionWithDens,
   Formalism.FourierDecayAlt.Final.tc_domScaleTop,
   Formalism.FourierDecayAlt.Final.tc_sumBoundMax,
   Formalism.FourierDecayAlt.Final.tc_recHypScaleTop,
   Formalism.FourierDecayAlt.Final.tc_densSum,
   Formalism.FourierDecayAlt.Final.tc_densLeTwo,
   Formalism.FourierDecayAlt.Final.tc_densSize,
   Formalism.FourierDecayAlt.Final.tc_densChain,
   Formalism.FourierDecayAlt.Final.poisson_summation_text,
   Formalism.FourierDecayAlt.Final.jx_poissonJoint,
   Formalism.FourierDecayAlt.Final.jx_poissonStepJoint,
   Formalism.SA.P.smoothedSumBound,
   Formalism.FourierDecayAlt.Final.lattices_general_position_bound,
   Formalism.FourierDecayAlt.Final.ideals_match,
   Formalism.FourierDecayAlt.Final.ideal_norm_formula,
   Formalism.FourierDecayAlt.Final.field_extension_degree_facts,
   Formalism.FourierDecayAlt.Final.jx_frameProducts,
   Formalism.FourierDecayAlt.Final.jx_xIsLamOne,
   Formalism.FourierDecayAlt.Final.jx_latticeSumsJoint,
   Formalism.FourierDecayAlt.Final.jx_instSizes,
   Formalism.FourierDecayAlt.Final.jx_instLatticeSums,
   Formalism.FourierDecayAlt.Final.sz_sizesMain,
   Formalism.FourierDecayAlt.Final.jx_sizesToRecursion,
   Formalism.FourierDecayAlt.Final.jx_globPositive,
   Formalism.FourierDecayAlt.Final.counting_theorem,
   Formalism.FourierDecayAlt.Final.jx_formGivesMain⟩

end Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFderivChiBound
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Bump

theorem dZ_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZ f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

theorem dZb_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZb f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

end Bump

end Formalism.FourierDecayAlt.P5.HerB
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def kapB (n : ℕ) : ℝ := Real.pi ^ ((n + 1) * (n + 4) / 2)

theorem ptSize_two (h : C.LPt) (n : ℕ) (t c : ℂ) :
    D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := by
  simp [D.ptSize, List.map_append, List.sum_append]

def SliceOmBlock : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h p : C.LPt) (n : ℕ) (t c : ℂ)
    (hp : p = h ++ [(n + 1, t), (1, c)]) (hle : D.ptSize p ≤ r) (γ : B.Mat k (r - D.ptSize p)),
    D.IsLocPt p (D.ptSize p) →
    Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) →
    D.sliceAt k r z z' F p γ =
      ((kapB n : ℝ) : ℂ) •
        G.OmBlock U.betaU (n + 1) (fun Z => U.PhiFun k (r - D.ptSize p) (D.ptPerm h) (D.ptDiag h)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z')
          (D.castF (by subst hp; rw [ptSize_two] at hle ⊢; omega) F) Z γ) t c

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFOK
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_orbital_valid : FamJFOK := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG t ht
  obtain ⟨hsm, hcpt⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hcpt {t} isCompact_singleton (by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact ht)
  have hzero : ∀ γ, γ ∉ C → G t γ = 0 := by
    intro γ hγ
    by_contra h
    exact hγ (hCε t rfl γ h).1
  have hCk : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hsm t ht γ₀ hγ₀
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), ?_, hmem, ?_, ?_⟩
    · exact hU.preimage (continuous_const.prodMk continuous_id)
    · have hd : ContDiff ℝ ∞ (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
        contDiff_const.prodMk contDiff_id
      exact hf.comp hd.contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγV
      exact hfe (t, γ) hγ hγV
  refine ⟨⟨?_, ε, hε, ?_⟩, ?_⟩
  · exact JFxG.cptInCC_G hCk hC (fun g _ hg => hzero g hg)
  · intro g hg hne
    exact (hCε t rfl g hne).2 hg
  · refine HasCompactSupport.intro hC ?_
    exact hzero

end Formalism.FourierDecayAlt.P.CutSH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamAlg
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_algebraic : FamAlg := by
  intro Wp Wq _ _ _ _ _ _ P T j G G' hG hG' m hm
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨hG1', hG2'⟩ := hG'
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    obtain ⟨U', f', hU', hmem', hf', hfe'⟩ := hG1' t₀ ht₀ γ₀ hγ₀
    refine ⟨U ∩ U', fun p => f p + f' p, hU.inter hU', ⟨hmem, hmem'⟩,
      (hf.mono Set.inter_subset_left).add (hf'.mono Set.inter_subset_right), ?_⟩
    intro p hp hpG
    simp only [hfe p hp.1 hpG, hfe' p hp.2 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    obtain ⟨C', hC', ε', hε', hCε'⟩ := hG2' K hK hK0
    refine ⟨C ∪ C', hC.union hC', min ε ε', lt_min hε hε', ?_⟩
    intro t ht γ hne
    by_cases h0 : G t γ = 0
    · have h1 : G' t γ ≠ 0 := by
        intro h1; apply hne; simp [h0, h1]
      obtain ⟨hγ, hb⟩ := hCε' t ht γ h1
      exact ⟨Or.inr hγ, fun hg => (min_le_right _ _).trans (hb hg)⟩
    · obtain ⟨hγ, hb⟩ := hCε t ht γ h0
      exact ⟨Or.inl hγ, fun hg => (min_le_left _ _).trans (hb hg)⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t₀ ht₀ γ₀ hγ₀
    have hO : IsOpen {p : ℂ × B.Mat P.k (P.r - (j + 1)) | p.1 ≠ 0} :=
      isOpen_ne_fun continuous_fst continuous_const
    refine ⟨U ∩ {p | p.1 ≠ 0}, fun p => m p.1 • f p, hU.inter hO, ⟨hmem, ht₀⟩, ?_, ?_⟩
    · have hm' : ContDiffOn ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) => m p.1) (U ∩ {p | p.1 ≠ 0}) :=
        hm.comp contDiffOn_fst (fun p hp => hp.2)
      exact hm'.smul (hf.mono Set.inter_subset_left)
    · intro p hp hpG
      simp only [hfe p hp.1 hpG]
  · intro K hK hK0
    obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
    exact ⟨C, hC, ε, hε, fun t ht γ hne => hCε t ht γ (right_ne_zero_of_smul hne)⟩

end Formalism.FourierDecayAlt.P.CutSH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpP
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsR (i : Fin (k + 1)) : Fin (r + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r + i.val then j.val else j.val + 1, by have := j.isLt; have := i.isLt; split_ifs <;> omega⟩

def ginvH (g : Q.Mx k r) : Q.Mx k r := Hpk k r * gᴴ * Hpk k r

def colR (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1))
    (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : q.val < r then ginvH k r g *ᵥ bvec (eI k r ⟨r - 1 - q.val, by omega⟩)
  else if h2 : q.val = r then ginvH k r g *ᵥ z
  else bvec (J ⟨q.val - r - 1, by have := q.isLt; omega⟩)

def beJ (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) : ℂ :=
  (Matrix.of fun p q => colR k r z g J q p).det


open Classical in
def jSetR : Finset (Fin (r + k) → Fin (2 * r + k + 1)) := Finset.univ.filter fun J => StrictMono J

def rhatOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ i : Fin (k + 1), ∑ J ∈ jSetR k r,
    (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z g J) •
      qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) f g

end defs

def JDRRadP : Prop :=
  ∀ k r : ℕ, ∃ ε : ℂ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      Q.resG k r (Fin.last r) (fun x => ε • rhatOp k r z z' Y J x) c g = rhGrp k r z z' Y (Q.resG k r (Fin.last r) J) c g

def JDRRealInvP : Prop :=
  ∀ (ε : ℂ) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ (U : Set (Q.Mx S.G.k S.G.r)) (F : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsOpen U →
          Q.SmoothLev S.G.k S.G.r 0 U F → ∀ g ∈ Q.Glev S.G.k S.G.r 0 ∩ U,
            B.opApply Θ F g = ε • rhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F g

private theorem isDom_OmP_levTower_base {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := by
  refine ⟨?_, ?_⟩
  · have hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l := by
      intro l
      unfold Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    have hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := by
      unfold Formalism.QuantumDeterminants.Gf
      exact (Complex.continuous_normSq.comp (hD _)).sub
        (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
    unfold OmP
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isOpen_lt continuous_const hG).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)
  · rintro g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.1
    · rw [Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.2 a

private theorem w1_mem_UH_Hpk_of_ne_zero {k r : ℕ} (l : Fin r) (x : ℂ) (hx : x ≠ 0) :
    Q.w1 k r l x ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  have hl := l.isLt
  have hes : eI k r l ≠ esI k r l := by
    simp only [eI, esI, ne_eq, Fin.ext_iff]
    omega
  have hcol : ∀ j q, Q.w1 k r l x j q =
      if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then
        (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0 := by
    intro j q
    simp only [Q.w1]
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
      by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>
      (intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)
  have hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [esI] at hp
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [eI] at hp
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [esI] at hq
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [eI] at hq
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHes : Hpk k r (eI k r l) (esI k r l) = 1 := by
    have h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h1]
  have hHse : Hpk k r (esI k r l) (eI k r l) = 1 := by
    have h2 : ¬ (2 * r + k - (l : ℕ) < r) := by omega
    have h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h2, h3]
  show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
    first
    | exact absurd (hp1.symm.trans hp2) hes
    | exact absurd (hq1.symm.trans hq2) hes
    | simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]

private theorem mul_mem_UH_of_mem_of_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hh : h ∈ Formalism.QuantumDeterminants.UH H) : g * h ∈ Formalism.QuantumDeterminants.UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']

private theorem wCell_mem_UH_Hpk_of_ne_zero {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i : Fin (r + 1)) :
    Q.wCell k r i c ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  unfold Q.wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil =>
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih

private theorem wCell_last_mul_mem_Glev_zero {k r : ℕ} (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  ⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩

theorem jDRGrpP_of_parts (hR : JDRRadP) (hI : JDRRealInvP) : JDRGrpP := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨ε, hε⟩ := hR S.G.k S.G.r
  obtain ⟨Θ, hP, hC, hA⟩ := hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, hP, hC, ?_⟩
  intro J hJ c hc g hg hx
  have key := hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx
  rw [← key]
  have hx0 := wCell_last_mul_mem_Glev_zero c hc g hg
  obtain ⟨U, F, hU, hxU, hF, hFJ⟩ := hJ.1 _ ⟨hx0, hx⟩
  have hS : Q.SmoothLev S.G.k S.G.r 0 U J := fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩
  have := hA U J hU hS _ ⟨hx0, hxU⟩
  simp only [Q.resG, this]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormModel
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def FormModel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (a : ℝ) (mm : ℕ)
    (ε' : ℝ) (Sg : Set (B.Mat P0.k (P0.r - j))),
    0 < ε' → P5.Auser P0 w.length + 1 ≤ a → P5.mmUser P0 w.length ≤ mm →
    5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm →
    (∀ γ ∈ Sg, ε' ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' γ) →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
      (Mo : U.CCModel P0.k (P0.r - j) (Wd.Ix (Fin w.length) → (Wq →L[ℂ] Wp)) a mm Sg V),
      ∃ (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Cp : ℝ), 0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
        ∀ (u u' : V) (x x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε'' : ℝ), 0 < ε'' →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x e)) →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x' e)) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u γ e = x e γ) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u' γ e = x' e γ) →
          Bf u u' = D.formLev T sg j w x x'

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRDrTr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
  {Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)}

theorem drtr_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  rw [MA.cbA, actA_sc]
  rfl

theorem drtr_actA_c (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vc l) * f ρ := by
  rw [MA.cA, actA_sc]
  rfl

theorem drtr_dMul_one (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : dMul (fun _ => (1 : ℂ)) Φ = Φ := by
  funext c g
  simp [dMul]

theorem drtr_listb (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (ls : List (Fin P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : FamR P Bs Dc Φ) :
    FamR P Bs Dc (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) ∧
      trR P Bs.μsec e (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) =
        MA.actA P (ls.map fun a => MA.cbA P (MA.DQ P) a).prod (trR P Bs.μsec e Φ) := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [drtr_dMul_one, actA_one]
    exact ⟨hΦ, rfl⟩
  | cons a ls ih =>
    obtain ⟨hF, hT⟩ := ih
    have eq : dMul (fun c => ((a :: ls).map fun a => star (c a)).prod) Φ =
        Q.crd (cbOp a) (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) := by
      funext c g
      show _ = star (c a) • ((ls.map fun a => star (c a)).prod • Φ c g)
      simp only [dMul, List.map_cons, List.prod_cons, mul_smul]
    have hcb : FamR P Bs Dc (Q.crd (cbOp a) (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ)) :=
      famR_opL hF a 4
    refine ⟨eq ▸ hcb, ?_⟩
    rw [eq, trR_mul hpl hk he hF _ hcb (fun c => star (c a)) (fun _ _ => rfl) (MA.coordQ (TT := P.TT) (M.vcb a))
      (fun q => coordE_vcb _ _), List.map_cons, List.prod_cons, actA_mul, drtr_actA_cb, hT]

theorem drtr_listc (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (ls : List (Fin P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : FamR P Bs Dc Φ) :
    FamR P Bs Dc (dMul (fun c => (ls.map fun a => c a).prod) Φ) ∧
      trR P Bs.μsec e (dMul (fun c => (ls.map fun a => c a).prod) Φ) =
        MA.actA P (ls.map fun a => MA.cA P (MA.DQ P) a).prod (trR P Bs.μsec e Φ) := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [drtr_dMul_one, actA_one]
    exact ⟨hΦ, rfl⟩
  | cons a ls ih =>
    obtain ⟨hF, hT⟩ := ih
    have eq : dMul (fun c => ((a :: ls).map fun a => c a).prod) Φ =
        Q.crd (cOp a) (dMul (fun c => (ls.map fun a => c a).prod) Φ) := by
      funext c g
      show _ = c a • ((ls.map fun a => c a).prod • Φ c g)
      simp only [dMul, List.map_cons, List.prod_cons, mul_smul]
    have hc : FamR P Bs Dc (Q.crd (cOp a) (dMul (fun c => (ls.map fun a => c a).prod) Φ)) :=
      famR_opL hF a 1
    refine ⟨eq ▸ hc, ?_⟩
    rw [eq, trR_mul hpl hk he hF _ hc (fun c => c a) (fun _ _ => rfl) (MA.coordQ (TT := P.TT) (M.vc a))
      (fun q => coordE_vc _ _), List.map_cons, List.prod_cons, actA_mul, drtr_actA_c, hT]

end

theorem residue_derivative_transition : JDRDrTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ
  obtain ⟨-, -, hc, -, hcb, -⟩ := hL
  have eb : drbF P.r = fun c => ((List.finRange P.r).map fun a => star (c a)).prod := by
    funext c
    rw [drbF, map_prod, ← List.prod_ofFn, List.ofFn_eq_map]
    rfl
  have ec : drF P.r = fun c => ((List.finRange P.r).map fun a => c a).prod := by
    funext c
    rw [drF, ← List.prod_ofFn, List.ofFn_eq_map]
  have hDrb : L.Drb = ((List.finRange P.r).map fun a => MA.cbA P (MA.DQ P) a).prod := by
    rw [R.LevelData.Drb, hcb, List.ofFn_eq_map]
  have hDr : L.Dr = ((List.finRange P.r).map fun a => MA.cA P (MA.DQ P) a).prod := by
    rw [R.LevelData.Dr, hc, List.ofFn_eq_map]
  refine ⟨fun ρ => ?_, fun ρ => ?_⟩
  · have h := (drtr_listb hpl hk he (List.finRange P.r) Φ hΦ).2
    rw [← eb, ← hDrb] at h
    exact congrFun h ρ
  · have h := (drtr_listc hpl hk he (List.finRange P.r) Φ hΦ).2
    rw [← ec, ← hDr] at h
    exact congrFun h ρ

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def vABm (r : ℕ) (Y : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (id, fun _ => 0)
  | i + 1 =>
    if h : i < r then
      (fun f => Y • (vABm r Y i).1 f - pbOp ⟨i, h⟩ ((vABm r Y i).1 f) - cbOp ⟨i, h⟩ ((vABm r Y i).2 f),
        fun f => cbiOp ⟨i, h⟩ ((vABm r Y i).1 f))
    else vABm r Y i

end defs

def JDAGrp : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℂ),
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                dMul (drF S.G.r) (Q.crd (Q.cmp (Q.vAB S.G.r y S.G.r) 0)
                  (Q.resG S.G.k S.G.r (Fin.last S.G.r) J)) c g ∧
              Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                dMul (drbF S.G.r) (Q.crd (Q.cmp (vABm S.G.r y S.G.r) 0)
                  (Q.resG S.G.k S.G.r (Fin.last S.G.r) J)) c g

def JDAVTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
    ∀ y : ℂ,
      (Gauge.FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) Φ) ∧
        Gauge.VLem.trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) Φ) =
          MA.actA P (L.Ar y) (Gauge.VLem.trR P Bs.μsec e Φ)) ∧
      (Gauge.FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r y P.r) 0) Φ) ∧
        Gauge.VLem.trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r y P.r) 0) Φ) =
          MA.actA P (L.Avr y) (Gauge.VLem.trR P Bs.μsec e Φ))

theorem jDCapA_of_parts (hG : JDAGrp) (hV : JDAVTr) (hD : JDRDrTr) : JDCapA := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  obtain ⟨Θ, Θv, h1, h2, h3, h4, hR⟩ := hG Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ => ?_⟩
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  have hF := Gauge.tc_famR (D.parOf S v) (T v).base hpl J hJ
  obtain ⟨⟨hA, tA⟩, ⟨hAv, tAv⟩⟩ := hV _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hF y
  have hJR : trJ S T v e J = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e
      (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) := by
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e J ρ) = _
    rw [Gauge.tc_rawJ]
    rfl
  have hpt : ∀ (Θ' : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (F : Q.Fn S.G.k S.G.r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      (∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
        Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
        Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ' J) c g = F c g) →
      trJ S T v e (B.opApply Θ' J) = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e F := by
    intro Θ' F hF'
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e (B.opApply Θ' J) ρ) = _
    rw [Gauge.tc_rawJ]
    show MA.toSm _ _ = MA.toSm _ _
    congr 1
    funext q
    have hmu := Gauge.tc_mu (D.parOf S v) (T v).base hpl q
    simp only [Gauge.rawR]
    rw [hF' q.1.1 q.2.1 _ hmu.1 hmu.2]
  constructor
  · rw [hpt Θ _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).1), hJR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drF _) _) ρ) = _
    rw [(hD _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hA).2 ρ, R.LevelData.Ahat, Gauge.actA_mul, ← tA]
    rfl
  · rw [hpt Θv _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).2), hJR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drbF _) _) ρ) = _
    rw [(hD _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hAv).1 ρ, R.LevelData.Ahatv, Gauge.actA_mul, ← tAv]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP
end
