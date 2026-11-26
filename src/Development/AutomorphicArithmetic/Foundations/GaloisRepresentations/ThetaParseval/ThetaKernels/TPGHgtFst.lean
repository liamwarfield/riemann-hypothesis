module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsTransportFK
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.UnfoldOf
public import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGHgtFst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEDetUnitary
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.WeilEx.Jac

section Alg

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {α β ν X : Type} [Fintype β] [DecidableEq β]
  [AddCommGroup X] [Module R X] {e : ν ⊕ ν ≃ α}


variable [Invertible (2 : R)] {D : Matrix α β A ≃ₗ[R] X × X}
  (hΔ : ∀ w, GlobalTheory.SWLit.LinAct.Del e w → (D w).1 = 0)
  (hN : ∀ w, GlobalTheory.SWLit.LinAct.Nab e w → (D w).2 = 0)
include hΔ hN

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_det_unitary {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E))) = 1 := by
  set d := Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E)) with hd
  have hJu : IsUnit (incM F J).det := by
    have e0 : (incM F J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
    rw [e0]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have h := congrArg Matrix.det (show ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have h2 : (d : AE F E) * cA σ d = 1 := by
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
    exact hJu.mul_left_cancel (by linear_combination h)
  have hc : Units.map (cA σ : AE F E →* AE F E) d = conjUnit σ d := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rfl
  have h3 : d * Units.map (cA σ : AE F E →* AE F E) d = 1 := Units.ext (by simpa using h2)
  have h4 : absE F E d * absE F E d = 1 := by
    nth_rewrite 2 [← absE_conjUnit σ d]
    rw [← hc, ← map_mul, h3, map_one]
  apply NNReal.coe_injective
  have h6 : (absE F E d : ℝ) * absE F E d = 1 := by exact_mod_cast h4
  have h7 : (0 : ℝ) ≤ absE F E d := (absE F E d).2
  push_cast
  exact le_antisymm (by nlinarith) (by nlinarith)

end Main

end GlobalTheory.WeilEx.Jac
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl
namespace UpperTheory.TP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}
private theorem hgt_swap_pk (hJ : X.J.det ≠ 0) {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a)
    {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) (g : UA σ X.J) :
    a (e (g, 1)) = a (e (1, g⁻¹)) := by
  have hp : IsPar (e (g, g)) (g : GL (Fin n) (AE F E)) := by
    change mat2 (e (g, g)) * diagCols (E := AE F E) (Fin n) = diagCols (E := AE F E) (Fin n) * mat g
    rw [he, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp
  have e1 : e (g, 1) = e (g, g) * e (1, g⁻¹) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel]
  rw [e1, ha.mul hp, GlobalTheory.WeilEx.Jac.absE_det_unitary hJ g]
  simp
end UpperTheory.TP
theorem UpperTheory.TP.hgtFst_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.HgtFst_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he
  have cX := T.cpt F E σ B n X n 0 hB (.inl hX) (by simp)
  haveI := cX.lc
  haveI := cX.sc
  obtain ⟨μ₀, D, hμ₀, -⟩ := cX.ex
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.ThK.Dbl.hgtInt_of_k T.stab2 F E σ B n X n 0 hB (.inl hX) K a e hK ha he μ₀ hμ₀
  refine ⟨t₀, fun μ hμ t ht => ?_⟩
  haveI := hμ
  haveI := hμ₀
  haveI := cX.right μ hμ
  have hJ : X.J.det ≠ 0 := GlobalTheory.ThK.Dbl.Hgt.det_ne (.inl hX)
  have h1 : Integrable (fun g => a (e (1, g)) ^ t) μ := by
    rw [Measure.isMulLeftInvariant_eq_smul μ μ₀]
    exact (ht₀ t ht).smul_measure ENNReal.coe_ne_top
  obtain ⟨c, -, hc⟩ := inv_scale μ
  have h2 : Integrable (fun g => ((a (e (g, 1)) ^ t : ℝ) : ℂ)) μ := (hc _).1 (by
    simp only [UpperTheory.TP.hgt_swap_pk hJ ha he, inv_inv]
    exact h1.ofReal)
  simpa using h2.re
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCutX
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def WhitAtC_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (x : d.G) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))
theorem asc_whitAt_iff_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k c d Φ ↔ ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x := by
  constructor
  · intro h x nb lam 𝓖 hc ε w hw T hT
    exact h nb lam 𝓖 hc ε w hw T hT x
  · intro h nb lam 𝓖 hc ε w hw T hT x
    exact h x nb lam 𝓖 hc ε w hw T hT
def IwaRedC_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Q : d.Fn → Prop), (∀ Φ, Q Φ → Φ ∈ d.sch) → (∀ Φ, Q Φ → ∀ k ∈ d.K, Q (d.om k Φ)) →
    (∀ Φ, Q Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x) → ∀ Φ, Q Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x
def LinRedC_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.EisAll → ∀ (k : ℕ) (cs : Fin k → ℂ)
    (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i)) → ∀ x, (∀ i, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d (Φs i) x) → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d (∑ i, cs i • Φs i) x
def VacSpan_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac →
    ∃ (k : ℕ) (cs : Fin k → ℂ) (Φs : Fin k → d.Fn),
      (∀ i, d.KFin (Φs i) ∧ d.T (Φs i) ∈ R.vac ∧ ∃ gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R (Φs i) (fun _ => 1) gf) ∧ Φ = ∑ i, cs i • Φs i
def GenDictX_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
  ∃ (dd : ℕ) (J : Matrix (Fin d.m) (Fin d.m) E) (T' : Matrix (Fin d.n) (Fin d.n) E) (bs : Module.Basis (Fin dd) F E)
    (ψ : AddChar (AF F) ℂ) (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (l : InfinitePlace F → ℝ)
    (εs : InfinitePlace F → Fin d.m → Bool) (fr : InfinitePlace F → GL (Fin d.m) ℂ) (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)) (c : ℂ) (C : ℝ),
    Gen.Dat0 σ J T' bs ψ θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ J y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    0 < C ∧
    (∃ t : ℝ, ∀ z : ℂ, t < z.re →
      (Integrable (fun β => flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x)) lam →
        Integrable (Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z) ν) ∧
      ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
        c * (C : ℂ) ^ (z - s0 d.m d.n) *
          ∫ b, Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z b ∂ν) ∧
    ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m J μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m J μH 𝓕 ∧
      d.orb T (d.om x Φ) = c * HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
        (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m J Φg {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T'})
def CorePure_k (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ) : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ok d.m d.n → d.EisAll → ∀ Φ, d.KFin Φ →
    ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf → (vac → P = fun _ => 1) → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x
def CoreX_k : Prop := ∀ (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ), _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → Gen.WhitGenX ok vac c →
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c
def DictAsmX_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.KWhit.CellFormula_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelEx_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.HeightDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.MeasDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.ThetaDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k
theorem eisAll_of_k (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hE : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.EisAll :=
  fun Φ hΦ => hE F E σ d _ _ (hS F E σ d Φ hΦ)
theorem levi_kfin_k (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k)
    (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hok : ok d.m d.n) (hE : d.EisAll) :
    ∀ Φ, d.KFin Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x := by
  intro Φ hΦ x hx
  obtain ⟨R⟩ := hR F E σ d
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hP hT hF hPK F E σ d R Φ hΦ (hK F E σ d R Φ hΦ)
  refine hL hT hTC hLB hU hS c F E σ d hE k cs Φs (fun i => (hs i).1) x (fun i => ?_)
  obtain ⟨P, gf, hpg⟩ := (hs i).2
  exact hC F E σ d R hok hE (Φs i) (hs i).1 P gf hpg (fun h => absurd h hv) x hx
theorem all_kfin_k (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k)
    (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k)
    (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c) (hKK : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
      [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ))
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
    (hok : ok d.m d.n) (hE : d.EisAll) : ∀ Φ, d.KFin Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x :=
  hI hT c F E σ d d.KFin (fun Φ h => h.1) (hKK F E σ d)
    (_root_.PositivityTheory.SiegelWeilFormula.KWhit.levi_kfin_k ok vac hv c hT hTC hLB hR hF hK hPK hS hU hP hL hC d hok hE)
def KFinK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ)
theorem whitK_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hKK : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : Gen.WhitGenLt)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k := by
  intro F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hc ε w hw T hT' x
  have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.all_kfin_k (fun M n => n < M) False not_false 1 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d hnm hE Φ hΦ x nb lam 𝓖 hc ε w hw T hT'
  simpa only [one_mul] using this
theorem whitEq_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hKK : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k)
    (hW : Gen.WhitGenEq) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k := by
  intro F E _ _ _ _ _ σ d hmn Φ hΦ
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.asc_whitAt_iff_k]
  exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.all_kfin_k (fun M n => M = n ∧ 1 ≤ M) False not_false 2 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d ⟨hmn, d.ok.hm⟩ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.eisAll_of_k hS hEW d) Φ hΦ
theorem whitLow_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hV : _root_.PositivityTheory.SiegelWeilFormula.KWhit.VacSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (hW : Gen.WhitGenLow)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k := by
  intro F E _ _ _ _ _ σ d R hmn Φ hΦ hvac
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.asc_whitAt_iff_k]
  have hE := _root_.PositivityTheory.SiegelWeilFormula.KWhit.eisAll_of_k hS hEW d
  have hcore := hC _ _ _ hT hA hS hU hW hD
  refine hI hT 0 F E σ d (fun Φ => Φ ∈ d.sch ∧ d.T Φ ∈ R.vac) (fun Φ h => h.1)
    (fun Φ h k hk => ⟨d.ok.dbl.weil.2.1.pres k Φ h.1, (hVK F E σ d R).1 Φ h.1 h.2 k hk⟩) ?_ Φ ⟨hΦ, hvac⟩
  intro Φ' h' x hx
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hV hT hF hPK hVK F E σ d R Φ' h'.1 h'.2
  refine hL hT hTC hLB hU hS 0 F E σ d hE k cs Φs (fun i => (hs i).1) x (fun i => ?_)
  obtain ⟨gf, hpg⟩ := (hs i).2.2
  exact hcore F E σ d R ⟨hmn, d.ok.hm⟩ hE (Φs i) (hs i).1 _ gf hpg (fun _ => rfl) x hx
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainEq
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
open PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fc_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : ℂ) (f : d.G → ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (c • f) T x = c * fc d.B.ψ d.b nb lam 𝓖 f T x := by
  unfold fc
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _
theorem perLiftC_k (c : ℂ) (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hnm : d.n ≤ d.m) (hEA : d.EisAll)
    (hW : ∀ Φ, d.KFin Φ → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k c d Φ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w) {φ : PX d.m d.n →ₗ[ℂ] d.Fn}
    (hφ : R.IsLift w Ψ φ) (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ P) x) := by
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => c • d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hTT hTA (hφ P).1 (hφ Q).1, smul_add]
      map_smul' := fun a P => by rw [map_smul, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hTT a (hφ P).1, RingHom.id_apply, smul_comm] }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d).comp φ
  obtain ⟨-, ⟨ε, ww, hww, -⟩, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hsec1 : IsSec d.K d.χ (s0 d.m d.n) (d.sec0 (φ 1)) := hSK F E σ d (φ 1) (hKF 1)
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hGDat : GlobData (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht
      sl Il d.lamSet :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := by
        show Continuous (c • d.I (φ 1))
        exact ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1.const_smul c
      Ileft := by
        intro γ hγ g
        show c * d.I (φ 1) (γ * g) = c * d.I (φ 1) g
        rw [((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2 γ hγ g]
      Ik := by
        intro P g k hk
        show c * thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = c * thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := by
        intro g a b P
        show c * d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
        rw [hGI F E σ d R w Ψ hΨ φ hφ g a b P, mul_zero]
      Idil := by
        intro g X a ha
        obtain ⟨U, H, hU, hR, hc, hH⟩ := hGD F E σ d R w Ψ hΨ φ hφ g X a ha
        refine ⟨U, fun y z => c * H y z, hU, hR, continuousOn_const.mul hc,
          fun y => ⟨(hH y).1.const_mul c, fun t => ?_, fun r => ?_⟩⟩
        · show c * H y t = c * d.I (φ 1) (g * R.ι w (y * a t))
          rw [(hH y).2.1 t]
        · show iteratedDeriv r (fun z => c * H y z) 0 = c * d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
          rw [iteratedDeriv_const_mul' c r (H y)]
          show c * iteratedDeriv r (H y) 0 = _
          rw [(hH y).2.2 r]
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩
      Λadd := fun l hl => (hLB F E σ d l hl).1
      Λbd := fun l hl => (hLB F E σ d l hl).2
      Λsing := fun f hf hinv hz => hLS F E σ d R w f hf hinv hz
      Λval := by
        rintro l ⟨nb, lam, 𝓖, T, x, hcd, hT, rfl⟩
        obtain ⟨t', ht'⟩ := hU F E σ d _ _ hsec1 hE1
        have hWh := hW (φ 1) (hKF 1) nb lam 𝓖 hcd ε ww hww T hT x
        have hC := hTC F E σ d (φ 1) (hφ 1).1 nb lam 𝓖 hcd T x
        show HolValueAt (fun z => fc d.B.ψ d.b nb lam 𝓖 (d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z) T x) (s0 d.m d.n)
          (fc d.B.ψ d.b nb lam 𝓖 (c • d.I (φ 1)) T x)
        rw [_root_.PositivityTheory.SiegelWeilFormula.Atop.fc_smul_k, hC]
        exact hWh.congr ⟨t', fun z hz => ((ht' z hz nb lam 𝓖 hcd ε ww hww x).2 T hT).symm⟩ }
  exact hA d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD (hgood hnm)
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il d.lamSet hGDat P x
theorem mainC_of_k (c : ℂ) (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hRD : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k)
    (hLE : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k)
    (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hnm : d.n ≤ d.m)
    (hEA : d.EisAll) (hW : ∀ Φ, d.KFin Φ → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k c d Φ) : _root_.PositivityTheory.SiegelWeilFormula.MainC_k c d := by
  intro Φ hΦ x
  obtain ⟨R⟩ := hRD F E σ d
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨k, P, Ψ, hΨ, hsum⟩ := (hFM F E σ d R).2.2 w _ (hKP F E σ d R Φ hΦ)
  choose φ hφ using fun i => hLE F E σ d R w (Ψ i) (hΨ i)
  have hsch : ∀ i, φ i (P i) ∈ d.sch := fun i => (hφ i (P i)).1
  have eT : ∀ i, d.T (φ i (P i)) = R.tens w (fP (P i)) (Ψ i) := fun i => (hφ i (P i)).2
  have hΦeq : Φ = ∑ i, φ i (P i) := by
    have hmem : Φ - ∑ i, φ i (P i) ∈ d.sch := d.sch.sub_mem hΦ.1 (d.sch.sum_mem fun i _ => hsch i)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, eT, hsum, sub_self]
  have key : ∀ i, HolValueAt (fun z => d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x) (s0 d.m d.n)
      (c * d.I (φ i (P i)) x) := fun i =>
    _root_.PositivityTheory.SiegelWeilFormula.Atop.perLiftC_k c hA hT hTC hAux hFM hLo hLI hGS hGI hGD hPK hSK hLB hLS hU d hnm hEA hW R w (hΨ i) (hφ i) (P i) x
  have hv : d.I Φ x = ∑ i, d.I (φ i (P i)) x := by
    rw [hΦeq, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_sum_k d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
  have hKi : ∀ i, d.KFin (φ i (P i)) := fun i =>
    hPK F E σ d R _ (hsch i) (by rw [eT]; exact ((hFM F E σ d R).2.1 w (Ψ i) (hΨ i)).1 (P i))
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := hEA _ (hKi i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 Φ = fun y => ∑ i, d.sec0 (φ i (P i)) y := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦeq, ← _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_apply_k, map_sum, Finset.sum_apply]
    rfl
  have heq : EqRight (fun z => ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x (fun i _ => htt i z (hz' i))
    show ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x = d.eis (d.sec0 Φ) (s0 d.m d.n) z x
    rw [hsec]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis
    simp only [Finset.mul_sum]
    exact this.symm
  rw [hv, Finset.mul_sum]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq
theorem eisAll_of_k (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.EisAll :=
  fun Φ hΦ => hEW F E σ d (s0 d.m d.n) (d.sec0 Φ) (hSK F E σ d Φ hΦ)
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
def MainEqOf_k : Prop :=
  AbsThm → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.RDEx_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k → _root_.PositivityTheory.SiegelWeilFormula.GIdil_k → _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k →
    _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.LamSing_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k → _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k → _root_.PositivityTheory.SiegelWeilFormula.MainEq_k
theorem Atop.mainEq_of_k : _root_.PositivityTheory.SiegelWeilFormula.MainEqOf_k := by
  intro hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hEW hWE F E _ _ _ _ _ σ d hmn
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.mainC_of_k 2 hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU d hmn.ge
    (_root_.PositivityTheory.SiegelWeilFormula.Atop.eisAll_of_k hSK hEW d) (fun Φ hΦ => hWE F E σ d hmn Φ hΦ)
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfMain
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCore
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCover
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}
theorem exists_cover_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) :
    ∃ C : Set (nA σ Y b), IsCompact C ∧ ∀ β : nA σ Y b, ∃ ν : nF σ Y b, β + (ν : nA σ Y b) ∈ C := by
  obtain ⟨K, hK, hKx⟩ := PositivityTheory.SiegelWeilFormula.kfour.nF_cocompact (_root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB) hb
  refine ⟨K, hK, fun β => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hKx β
  exact ⟨⟨γ, hγ⟩, by rwa [add_comm]⟩
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}
theorem unfoldCore_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {nb : nA σ Y b → G2 σ Y}
    {lam : Measure (nA σ Y b)} {𝓖 : Set (nA σ Y b)} (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (φ : G2 σ Y → ℂ) (hφ : Continuous φ) (hrat : ∀ p ∈ par2 σ Y, p ∈ rat2 σ Y → ∀ y, φ (p * y) = φ y)
    (hone : ∀ p t, IsPar p t → Matrix.GeneralLinearGroup.det t = 1 → ∀ y, φ (p * y) = φ y)
    (hmaj : ∀ C : Set (G2 σ Y), IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ g q‖ ≤ u q)
    {ε : ℤˣ} {w : G2 σ Y} (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (x : G2 σ Y) :
    Integrable (fun β => φ (w * nb β * x)) lam ∧ ∀ T : nF σ Y b, IsND T →
      fc B.ψ b nb lam 𝓖 (GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ) T x =
        ∫ β, φ (w * nb β * x) * B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace)) ∂lam := by
  classical
  obtain ⟨hnb, hHaar, h𝓖, -⟩ := hc
  have := hHaar
  have : Countable (rat2 σ Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ Y
  have : Countable (GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y)) := Quotient.countable
  obtain ⟨ε₀, hε₀⟩ := hb.1
  have hw_rat : w ∈ rat2 σ Y := by
    refine rat_of_inFrame (b := b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
    rw [hw]
    ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
  have hLI : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ Y ⊓ rat2 σ Y) φ := fun γ hγ g => hrat γ hγ.1 hγ.2 g
  let nbR : nF σ Y b → rat2 σ Y := fun ν => ⟨nb ν.1, nb_rat hnb ν.2⟩
  have nbR_zero : nbR 0 = 1 := Subtype.ext (nb_zero hnb)
  have nbR_add : ∀ ν ν', nbR (ν + ν') = nbR ν * nbR ν' := fun ν ν' => Subtype.ext (nb_add hnb ν.1 ν'.1)
  let act : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nF σ Y b → GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) :=
    fun q ν => GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q
  have hact0 : ∀ q, act q 0 = q := fun q => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR 0) q = q
    rw [nbR_zero, GlobalTheory.AutomorphicL2Unitary.rmul_one]
  have hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν') := fun q ν ν' => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν') (GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q) = GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR (ν + ν')) q
    rw [nbR_add, GlobalTheory.AutomorphicL2Unitary.rmul_mul]
  let A : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nA σ Y b → ℂ := fun q β =>
    GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ (nb β * x) q
  have hA : ∀ q, Continuous (A q) := fun q =>
    hφ.comp (continuous_const.mul ((continuous_nb hnb).mul continuous_const))
  have hAmk : ∀ (γ : rat2 σ Y) β, A (GlobalTheory.AutomorphicL2Unitary.mk _ γ) β = φ (γ.1 * (nb β * x)) := fun γ β =>
    GlobalTheory.Eis.term_mk hLI (nb β * x) γ
  have hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : nA σ Y b)) := fun q ν β => by
    have e : act q ν = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * nbR ν) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [e, hAmk]
    show φ ((q.out : rat2 σ Y).1 * nb ν.1 * (nb β * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
    rw [nb_add hnb, nb_comm hnb β]
    simp only [mul_assoc]
  obtain ⟨C, hC, hcov⟩ := _root_.PositivityTheory.SiegelWeilFormula.kunf.exists_cover_k B hB hb
  obtain ⟨u, hu, hAu'⟩ := hmaj ((fun β => nb β * x) '' C) (hC.image ((continuous_nb hnb).mul continuous_const))
  have hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q := fun q β hβ => hAu' _ ⟨β, hβ, rfl⟩ q
  let q₀ : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) := GlobalTheory.AutomorphicL2Unitary.mk _ ⟨w, hw_rat⟩
  have hq₀ : ∀ ν, act q₀ ν = GlobalTheory.AutomorphicL2Unitary.mk _ (⟨w, hw_rat⟩ * nbR ν) := fun ν => rfl
  have hinj : Function.Injective (act q₀) := fun ν ν' h => by
    rw [hq₀, hq₀] at h
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hP : (w * nb ν'.1) * (w * nb ν.1)⁻¹ ∈ par2 σ Y := by
      have e : (w * nb ν'.1) = (γ : rat2 σ Y).1 * (w * nb ν.1) := (congrArg Subtype.val hγ).symm
      rw [e, mul_inv_cancel_right]
      exact Subgroup.mem_subgroupOf.1 γ.2
    exact (Subtype.ext (big_inj hb hw hnb hP)).symm
  have hAq₀ : ∀ β, A q₀ β = φ (w * nb β * x) := fun β => by
    rw [hAmk, mul_assoc]
  have hI := abs_integrable lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact C hC hcov u hu hAu q₀ hinj
  refine ⟨hI.congr (Filter.Eventually.of_forall hAq₀), fun T hT => ?_⟩
  let χ₀ : nA σ Y b → ℂ := fun β => B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace))
  have htr : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => Algebra.trace (AF F) (AE F E) M.trace :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))).comp continuous_id.matrix_trace
  have hχc : Continuous χ₀ :=
    hB.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val)).neg)
  have hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β' := fun β β' => by
    simp only [χ₀, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add]
    exact AddChar.map_add_eq_mul _ _ _
  have hχΛ : ∀ ν : nF σ Y b, χ₀ (ν : nA σ Y b) = 1 := fun ν => by
    simp only [χ₀, AddChar.map_neg_eq_inv, psi_rat hB.std T ν, inv_one]
  have hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) →
      ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β := fun q hq => by
    rcases _root_.PositivityTheory.SiegelWeilFormula.kunf.cells_k B hB hb hw hnb T hT (q.out : rat2 σ Y).1 (q.out : rat2 σ Y).2 with
      ⟨p, hpP, hpΓ, ν, hνF, hγ⟩ | ⟨β₀, hψ, t, hpar, hdet⟩
    · exfalso
      refine hq ⟨ν, hνF⟩ ?_
      rw [hq₀, ← Quotient.out_eq q]
      refine GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨⟨p, hpΓ⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
      exact hγ.symm
    · refine ⟨β₀, hψ, fun ν β => ?_⟩
      rw [hAact, hAact]
      show φ ((q.out : rat2 σ Y).1 * (nb (β + β₀ + ν.1) * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
      set γ := (q.out : rat2 σ Y).1
      have e : γ * (nb (β + β₀ + ν.1) * x) = (γ * nb β₀ * γ⁻¹) * (γ * (nb (β + ν.1) * x)) := by
        rw [show β + β₀ + ν.1 = β₀ + (β + ν.1) by abel, nb_add hnb]
        group
      rw [e, hone _ t hpar hdet]
  obtain ⟨-, -, heq⟩ := abs_unfold lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact χ₀ hχc hχadd hχΛ C hC hcov u hu hAu
    q₀ hinj hsmall
  show ∫ β in 𝓖, GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ (nb β * x) * χ₀ β ∂lam = ∫ β, φ (w * nb β * x) * χ₀ β ∂lam
  have e2 : ∫ β, φ (w * nb β * x) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam :=
    integral_congr_ae (Filter.Eventually.of_forall fun β => by simp only [hAq₀])
  rw [e2]
  exact heq
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
theorem unfold_k : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k := by
  intro F E _ _ _ _ _ σ d s₁ f hf hE
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := hE 0
  refine ⟨t, fun z hz nb lam 𝓖 hc ε w hw x => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = GlobalTheory.ThK.Dbl.flat d.a f s₁ z := funext fun x => by
    rw [GlobalTheory.ThK.Dbl.flat, _root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
  have hmaj' := (hmaj z hz).1
  rw [hΦ] at hmaj'
  have hlaw : Law d.χ (s₁ + d.n / 2) f := hf.law
  have hlawF := hlaw.flat (s₀ := s₁) d.ok.hgt (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z
  have hcore := _root_.PositivityTheory.SiegelWeilFormula.kunf.unfoldCore_k d.B d.ok.good d.ok.frame hc (GlobalTheory.ThK.Dbl.flat d.a f s₁ z)
    (continuous_flat hf.cont (_root_.PositivityTheory.SiegelWeilFormula.kunf.continuous_a_k d) (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z)
    (fun p hp hpr y => hlawF.rat d.ok.hecke hp hpr y)
    (fun p t ht hdet y => by rw [hlawF p t y ht, hdet]; simp)
    hmaj' hw x
  refine ⟨hcore.1, fun T hT => ?_⟩
  show fc d.B.ψ d.b nb lam 𝓖 (GlobalTheory.Eis.cosetSum _ _ (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x)) T x = _
  rw [hΦ]
  exact hcore.2 T hT
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGRallis
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
private theorem zero_of_half_pk {U : Set ℂ} (hU : IsOpen U) (hd : ∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U ∩ {z | τ < z.re})) {t : ℝ} (ht : ∀ z : ℂ, t < z.re → z ∈ U ∧ f z = 0) {s : ℂ} (hs : s ∈ U)
    (hs' : τ < s.re) : f s = 0 := by
  have hsh : Continuous fun z : ℂ => z + (τ : ℂ) := by fun_prop
  have key := eq_zero_of_right (U := (fun z : ℂ => z + (τ : ℂ)) ⁻¹' U) (hU.preimage hsh)
    (fun z => by
      have tt : Tendsto (fun z : ℂ => z + (τ : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + (τ : ℂ))) :=
        tendsto_nhdsWithin_iff.2 ⟨hsh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun w hw h => hw (add_right_cancel h)⟩
      exact tt.eventually (hd _))
    (f := fun z => f (z + (τ : ℂ)))
    (hf.comp (by fun_prop) fun z hz => ⟨hz.1, by simpa using hz.2⟩)
    (t := t - τ) (fun z hz => ⟨(ht _ (by simp; linarith [show t - τ < z.re from hz])).1,
      (ht _ (by simp; linarith [show t - τ < z.re from hz])).2⟩)
    (s := s - (τ : ℂ)) (by simpa using hs) (by simpa using hs')
  simpa using key
private theorem cpow_integral_pk {Y : Type} [MeasurableSpace Y] {μ : Measure Y} {A : Y → ℝ} {b : Y → ℂ} {t₀ q C : ℝ}
    (h0 : ∀ x, 0 < A x) (mA : Measurable A) (mb : AEStronglyMeasurable b μ) (hb : ∀ x, ‖b x‖ ≤ C * A x ^ q)
    (hi : ∀ t, t₀ ≤ t → Integrable (fun x => A x ^ t) μ) (s₀ : ℂ) :
    (∀ z : ℂ, t₀ < z.re - s₀.re + q → Integrable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ) ∧
      DifferentiableOn ℂ (fun z => ∫ x, (A x : ℂ) ^ (z - s₀) * b x ∂μ) {z : ℂ | t₀ < z.re - s₀.re + q} := by
  have mz : ∀ z : ℂ, AEStronglyMeasurable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ := fun z =>
    ((Complex.measurable_ofReal.comp mA).pow_const _).aestronglyMeasurable.mul mb
  have nz : ∀ (z : ℂ) x, ‖(A x : ℂ) ^ (z - s₀) * b x‖ ≤ |C| * A x ^ (z.re - s₀.re + q) := fun z x => by
    have p := h0 x
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos p, Complex.sub_re, Real.rpow_add p, mul_left_comm]
    exact mul_le_mul_of_nonneg_left ((hb x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg p.le _)))
      (Real.rpow_nonneg p.le _)
  refine ⟨fun z hz => ((hi _ hz.le).const_mul |C|).mono' (mz z) (.of_forall (nz z)), ?_⟩
  refine GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound
    (isOpen_lt continuous_const (by fun_prop)) (fun x z _ => ?_) (fun z _ => mz z) fun z hz => ?_
  · have : (A x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h0 x).ne'
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl this)).mul_const _ |>.differentiableWithinAt
  · have hz' : t₀ < z.re - s₀.re + q := hz
    set u := z.re - s₀.re + q with hu
    refine ⟨(u - t₀) / 2, by linarith, fun w hw => ?_, fun x => |C| * (A x ^ (u - (u - t₀) / 2) + A x ^ (u + (u - t₀) / 2)),
      (((hi _ (by linarith)).add (hi _ (by linarith))).const_mul _), fun w hw x => ?_⟩
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      show t₀ < w.re - s₀.re + q
      linarith [this.1]
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      refine (nz w x).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      have p := h0 x
      have p1 := Real.rpow_pos_of_pos p (u - (u - t₀) / 2)
      have p2 := Real.rpow_pos_of_pos p (u + (u - t₀) / 2)
      rcases le_total 1 (A x) with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h (show w.re - s₀.re + q ≤ u + (u - t₀) / 2 by linarith [this.2])
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge p h (show u - (u - t₀) / 2 ≤ w.re - s₀.re + q by linarith [this.1])
        linarith
private theorem coef_facts_pk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (hD : IsFundamentalDomain Γ D μ) [IsFiniteMeasure (μ.restrict D)] {φ : G → ℂ} (hc : Continuous φ) {C : ℝ} (hb : ∀ g, ‖φ g‖ ≤ C)
    (hi : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => pet μ D (fun y => φ (y * g)) φ) ∧ (∃ C' : ℝ, ∀ g, ‖pet μ D (fun y => φ (y * g)) φ‖ ≤ C') ∧
      ∀ g, pet μ D (fun y => φ (y * g⁻¹)) φ = star (pet μ D (fun y => φ (y * g)) φ) := by
  have C0 : 0 ≤ C := (norm_nonneg _).trans (hb 1)
  have nb : ∀ g y, ‖φ (y * g) * star (φ y)‖ ≤ C * C := fun g y => by
    rw [norm_mul, norm_star]; exact mul_le_mul (hb _) (hb _) (norm_nonneg _) C0
  have cm : ∀ g, Continuous fun y => φ (y * g) * star (φ y) := fun g => by fun_prop
  refine ⟨continuous_of_dominated (bound := fun _ => C * C) (fun g => (cm g).aestronglyMeasurable)
    (fun g => .of_forall (nb g)) (integrable_const _) (.of_forall fun y => by fun_prop), ⟨C * C * (μ.restrict D).real Set.univ, fun g => ?_⟩, fun g => ?_⟩
  · simpa [pet] using norm_integral_le_of_norm_le_const (μ := μ.restrict D) (.of_forall (nb g))
  · let f : G → ℂ := fun y => φ y * star (φ (y * g))
    have hf : ∀ (γ : Γ) x, f (γ • x) = f x := fun γ x => by
      simp only [f, Subgroup.smul_def, smul_eq_mul, mul_assoc]
      rw [hi _ γ.2, hi _ γ.2]
    have h2 : IsFundamentalDomain Γ (MulOpposite.op g⁻¹ • D) μ := hD.smul_of_comm (MulOpposite.op g⁻¹)
    have h3 : ∫ y in MulOpposite.op g⁻¹ • D, f y ∂μ = ∫ y in D, f (y * g⁻¹) ∂μ := by
      exact (measurePreserving_mul_right μ g⁻¹).setIntegral_image_emb (measurableEmbedding_mulRight g⁻¹) f D
    have h4 := h2.setIntegral_eq hD hf
    rw [h3] at h4
    simp only [pet]
    simp only [f, inv_mul_cancel_right] at h4
    rw [h4, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp [mul_comm]
theorem _root_.UpperTheory.TP.rallis_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Rallis_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP hn hd K a e hK ha he t₀ hi hlt ν hν Φ hΦ φ hφ
  have h0 : min n 0 = 0 := by simp
  have h0' : min d 0 = 0 := by simp
  have cX := T.cpt F E σ B _ X _ _ hP.base (.inl hP.herm) h0
  have cW := T.cpt F E σ B _ W _ _ hP.base (.inr hP.skew) h0'
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  have hKc := T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm) K hK
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hP.base (.inl hP.herm) h0
  obtain ⟨⟨K₁, a₁, hK₁, ha₁, ca, a0⟩, e₁, ce, he₁⟩ := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm)
  have eK : K₁ = K := Subgroup.ext fun k => (hK₁ k).trans (hK k).symm
  subst eK
  have ea : a₁ = a := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha₁.val p t hp k hk]
  subst ea
  have ee : e₁ = e := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he₁ x.1 x.2).trans (he x.1 x.2).symm))
  subst ee
  haveI := cX.sc; haveI := cW.sc; haveI := cX.lc; haveI := cW.lc; haveI := cX.cnt; haveI := hP.good.haar; haveI := cX.right M.μ hP.good.haar
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cX.fin _ _ hP.good.haar hP.good.dom⟩
  obtain ⟨c, c1, hc1⟩ := inv_scale M.μ
  have s1 := T.polSch F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP Φ hΦ
  have bT := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP).1 Φ s1
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := T.dbl F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨c', c0, hc⟩ := d4 ν hν
  have c2 : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 c0.ne'
  have sec := T.boxSec F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1 K₁ a₁ hK ha Φ hΦ Φ hΦ
  obtain ⟨U, Ê, hE, u, hv⟩ := T.swFull F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1
    K₁ a₁ hK ha μ D hμ hD Φ hΦ Φ hΦ
  set f : G2 σ X → ℂ := fun x => l (om₂ x (boxFun Φ (star Φ))) with hf
  set s₀ : ℂ := ((d : ℂ) - n) / 2 with hs₀
  have hap : ∀ g, a₁ (e₁ (1, g)) = a₁ (e₁ (g⁻¹, 1)) := fun g => by
    have := ha.mul (he g g).par (e₁ (g⁻¹, 1))
    rw [absE_det hJ, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at this
    simpa using this
  have hi' : ∀ t, t₀ ≤ t → Integrable (fun g => a₁ (e₁ (1, g)) ^ t) M.μ := fun t ht => by
    have h1 : Integrable (fun g => (((a₁ (e₁ (1, g)) ^ t : ℝ) : ℂ))) M.μ := (hc1 _).1 (by
      simpa [hap] using (hi t ht).ofReal (𝕜 := ℂ))
    simpa using h1.re
  have idf : ∀ g, f (e₁ (1, g)) * detInv χW g = c' * coef om ν Φ g⁻¹ := fun g => by
    have h1 := Law.diag sec.law hJ he g (e₁ (g⁻¹, 1))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at h1
    have e2 := ((d2 Φ s1 Φ s1).2 1 g⁻¹ 1 _ (he _ _)).2
    rw [detInv_rat hP.hW (one_mem _), one_smul, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, Module.End.one_apply] at e2
    rw [h1, hf]
    simp only [e2]
    rw [hc _ (hP.weil.isUSplitting.pres _ _ s1) _ s1, coef]
  have cF : Continuous (coef om ν Φ) := by
    have h1 : coef om ν Φ = fun g => (c' : ℂ)⁻¹ * (f (e₁ (1, g⁻¹)) * detInv χW g⁻¹) := funext fun g => by
      rw [idf, inv_inv, inv_mul_cancel_left₀ c2]
    rw [h1]
    exact continuous_const.mul ((sec.cont.comp (ce.comp (continuous_const.prodMk continuous_inv))).mul
      ((continuous_detInv hP.hW).comp continuous_inv))
  obtain ⟨Cf, hCf⟩ := Law.bound sec.law sec.cont ha hKc
  have hre : (s₀ + (n : ℂ) / 2).re = (d : ℝ) / 2 := by
    have : s₀ + (n : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have bF : ∀ g, ‖coef om ν Φ g‖ ≤ (c'⁻¹ * Cf) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    have h1 := idf g⁻¹
    rw [inv_inv] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_detInv, mul_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg c0.le] at h2
    have h3 := hCf (e₁ (1, g⁻¹))
    rw [hre, hap, inv_inv, h2] at h3
    rw [mul_assoc, le_inv_mul_iff₀ c0]
    exact h3
  obtain ⟨Cφ, hCφ⟩ := cX.bdd hφ.1 hφ.2
  obtain ⟨cm, ⟨Cm, hCm⟩, im⟩ := coef_facts_pk hP.good.dom hφ.1 hCφ hφ.2
  change Continuous (mc M φ) at cm
  change ∀ g, ‖mc M φ g‖ ≤ Cm at hCm
  change ∀ g, mc M φ g⁻¹ = star (mc M φ g) at im
  have Cm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 1)
  have a0' : ∀ g, 0 < a₁ (e₁ (g, 1)) := fun g => a0 _
  have mA : Measurable fun g => a₁ (e₁ (g, 1)) :=
    (ca.comp (ce.comp (continuous_id.prodMk continuous_const))).measurable
  have hb : ∀ g, ‖coef om ν Φ g * star (mc M φ g)‖ ≤ (c'⁻¹ * Cf * Cm) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    rw [norm_mul, norm_star, mul_right_comm]
    exact mul_le_mul (bF g) (hCm g) (norm_nonneg _) ((norm_nonneg _).trans (bF g))
  obtain ⟨iZ, dZ⟩ := cpow_integral_pk a0' mA (cF.mul cm.star).aestronglyMeasurable hb hi s₀
  have hsr : s₀.re = ((d : ℝ) - n) / 2 := by
    have : s₀ = ((((d : ℝ) - n) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have ib : Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ := by
    simpa using iZ s₀ (by simpa using hlt)
  refine ⟨ib, fun L0 => ?_⟩
  obtain ⟨hol, t₁, far⟩ := _root_.GlobalTheory.ThK.Dbl.kpair_cont_k hP.base (.inl hP.herm) h0 cX hP.hW he ce hKc ha ca a0 sec.cont sec.law hE hP.good.haar hP.good.dom hi'
  have rp : IsRapid φ := cX.rapid hφ.1 hφ.2
  have eqP : ∀ z : ℂ, t₁ < z.re → kpair χW e₁ M.μ M.dom (Ê z) φ =
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ) := fun z hz => by
    have ez : ∀ g, GlobalTheory.ThK.Dbl.flat a₁ f s₀ z (e₁ (1, g)) * detInv χW g * pet M.μ M.dom (fun h => φ (h * g)) φ =
        c' * ((a₁ (e₁ (g⁻¹, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g⁻¹ * star (mc M φ g⁻¹))) := fun g => by
      have h1 : star (mc M φ g⁻¹) = pet M.μ M.dom (fun h => φ (h * g)) φ := by rw [im, star_star]; rfl
      rw [h1, GlobalTheory.ThK.Dbl.flat, hap, mul_assoc (_ ^ _), idf]
      ring
    rw [(far z hz).2.2 φ rp]
    simp only [ez]
    rw [(hc1 fun g => c' * ((a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)))).2, integral_const_mul]
  have H0 := zero_of_half_pk (τ := t₀ + s₀.re - (d : ℝ) / 2) hE.isOpen hE.disc
    (f := fun z => kpair χW e₁ M.μ M.dom (Ê z) φ -
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ))
    (((hol φ rp).mono Set.inter_subset_left).sub (((dZ.mono fun z hz => by
      have : t₀ + s₀.re - (d : ℝ) / 2 < z.re := hz.2
      show t₀ < z.re - s₀.re + (d : ℝ) / 2
      linarith).const_mul _).const_mul _))
    (t := t₁) (fun z hz => ⟨(far z hz).1, sub_eq_zero.2 (eqP z hz)⟩) u (by linarith)
  have cT : Continuous fun x : UA σ W.J × UA σ X.J => theta om Φ x.2 x.1 := bT.1.comp continuous_swap
  have key := An.at_value (φ := φ) (M.μ.restrict M.dom) (μ.restrict D)
    ⟨cT, cW.bdd₂ cX cT fun γ hγ δ hδ g g' => bT.2.1 δ hδ γ hγ _ _⟩ ⟨hφ.1, Cφ, hCφ⟩
  have zl : ∀ h, ∫ g in M.dom, φ g * star (theta om Φ g h) ∂M.μ = 0 := fun h => by
    have h1 : lift M om Φ φ h = 0 := congrFun L0 h
    have h2 : star (lift M om Φ φ h) = 0 := by rw [h1, star_zero]
    rw [← h2, lift, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp [mul_comm]
  simp only [zl, zero_mul, integral_zero] at key
  have hk : kpair χW e₁ M.μ M.dom (Ê s₀) φ = (if n < d then 1 else 2) * (((μ.real D)⁻¹ : ℝ) : ℂ) *
      ∫ y, (∫ h in D, theta om Φ y.1 h * star (theta om Φ y.2 h) ∂μ) * (φ y.2 * star (φ y.1)) ∂(M.μ.restrict M.dom).prod (M.μ.restrict M.dom) := by
    rw [kpair, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, setAverage_eq, Complex.real_smul, ← fun g => (((d2 Φ s1 Φ s1).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  have H1 : c * (c' * ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ) = 0 := by
    have h2 : kpair χW e₁ M.μ M.dom (Ê s₀) φ = 0 := by rw [hk, key, mul_zero]
    simpa [h2] using H0
  exact (mul_eq_zero.1 ((mul_eq_zero.1 H1).resolve_left c1)).resolve_left c2
end UpperTheory.TP
end
end
end
