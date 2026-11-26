module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockNegSubst

open MvPolynomial

theorem map_conj_substF {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.CompactHowe.substF h g P) =
      GlobalTheory.CompactHowe.substF (fun τ => (h τ).map (starRingEnd ℂ)) (fun τ => (g τ).map (starRingEnd ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [GlobalTheory.CompactHowe.substF, MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_self, RingHom.id_apply]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul (GlobalTheory.CompactHowe.substF h g), map_mul (MvPolynomial.map (starRingEnd ℂ)), hp,
      map_mul (MvPolynomial.map (starRingEnd ℂ)), map_mul, MvPolynomial.map_X, GlobalTheory.CompactHowe.substF_X,
      GlobalTheory.CompactHowe.substF_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

theorem map_conj_conj {σ : Type} (P : MvPolynomial σ ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => Complex.conj_conj z
  rw [e, MvPolynomial.map_id]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_map_conj {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (MvPolynomial.map (starRingEnd ℂ) Q) =
      fun x => starRingEnd ℂ (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT
        (fun w => starRingEnd ℂ (f w)) Q x) := by
  funext x
  induction Q using MvPolynomial.induction_on' with
  | monomial k a =>
    have hm := GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f hψ hθ k x
    have e1 : (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have e2 : MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) =
        (starRingEnd ℂ a) • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e2, e1, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ← hm]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, hp, hq, map_add (f := _)]

end GlobalTheory.FockNegSubst

namespace GlobalTheory.FockNegSubst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT v : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ), IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f P = pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (v τ).map (starRingEnd ℂ)) (fun τ => (((u τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  intro D ψ θ S T hψ hθ BS u BT v f hf P
  have hf' : IsThetaFunO ψ S T (fun w => starRingEnd ℂ (f w)) := GlobalTheory.CjNeg.theta_negS' hψ hf
  rw [← map_conj_conj P,
    pureTensorO_negSp_map_conj ψ θ S T hψ hθ (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f
      (MvPolynomial.map (starRingEnd ℂ) P),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS u BT v _ hf' (MvPolynomial.map (starRingEnd ℂ) P),
    ← map_conj_substF, pureTensorO_negSp_map_conj ψ θ S T hψ hθ BS BT f]

end GlobalTheory.FockNegSubst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubstStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_negSpace_frameChange_conjSubst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT v : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ), IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f P = pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (v τ).map (starRingEnd ℂ)) (fun τ => (((u τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.FockNegSubst.pureTensorO_negSp_subst | exact GlobalTheory.FockNegSubst.pureTensorO_negSp_subst | (intros; apply GlobalTheory.FockNegSubst.pureTensorO_negSp_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockRealMove

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) {x : GA D V} (hx : x ∈ GfC V) :
    compAt θ τ (mt V x) = 1 :=
  GlobalTheory.LocWeil.CompactPart.infMat_of_fin V (θ τ) hx

theorem om_fin_fockVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x ∈ GfC S, ∀ y ∈ GfC T, IsThetaFunO ψ S T (om (x, y) f) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x, y) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sT f hf hvac x hx y hy
  refine ⟨hW.om_pres _ _ hf, fun τ z => ?_⟩
  have hS : sS τ * compAt θ τ (mt S x) = compAt θ τ (mt S x) * sS τ := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, Matrix.mul_one, Matrix.one_mul]
  have hT : sT τ * compAt θ τ (mt T y) = compAt θ τ (mt T y) * sT τ := by
    rw [compAt_mt_of_mem_GfC θ τ T hy, Matrix.mul_one, Matrix.one_mul]
  have key := GlobalTheory.FockMove.om_annih hW hθ x y τ hS hT (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) hf
  rw [hvac τ, map_zero] at key
  have e : compAt θ τ (mt T y) * (compAt θ τ (mt T y⁻¹) * z * compAt θ τ (mt S x)) * compAt θ τ (mt S x⁻¹) = z := by
    rw [compAt_mt_of_mem_GfC θ τ S hx, compAt_mt_of_mem_GfC θ τ S (inv_mem hx),
      compAt_mt_of_mem_GfC θ τ T hy, compAt_mt_of_mem_GfC θ τ T (inv_mem hy)]
    simp
  rw [e] at key
  exact key.symm

end GlobalTheory.FockRealMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_finitePoint_preserves_fockVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x ∈ GfC S, ∀ y ∈ GfC T, IsThetaFunO ψ S T (om (x, y) f) ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x, y) f) := by
  first | exact @GlobalTheory.FockRealMove.om_fin_fockVac | exact GlobalTheory.FockRealMove.om_fin_fockVac | (intros; apply GlobalTheory.FockRealMove.om_fin_fockVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevel
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.FormulaTwo

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem mem_xiVals {L : LevCh D T} {t : T} {n : ℕ} (hn : (L.xiH t).OrderDvd n) (hL : LocIn D.what₂.embLL (L.xiH t))
    {z : ℂˣ} (hz : z ∈ xiVals L t) : z ^ n = 1 ∧ (z : ℂ) ∈ Set.range D.what₂.embLL := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, x, rfl⟩ := hz
    refine ⟨?_, hL w x⟩
    have : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from hn]; rfl
    exact this
  | one => exact ⟨one_pow _, 1, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha.2
    obtain ⟨y, hy⟩ := hb.2
    exact ⟨by rw [mul_pow, ha.1, hb.1, one_mul], x * y, by simp [hx, hy]⟩
  | inv a _ ha =>
    obtain ⟨x, hx⟩ := ha.2
    exact ⟨by rw [inv_pow, ha.1, inv_one], x⁻¹, by simp [hx]⟩

theorem Bplus_smul_form {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (c : ℂ) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M φ (c • F) = c * Bplus W M φ F := by
  simpa using Bplus_smul W M 1 c φ F

theorem scalar_calc {e z z' c p b s u κ v w : ℂ} (he : e = z * z') (hz : z ≠ 0) (hz' : z' ≠ 0) (hc : c ≠ 0)
    (h1 : p = (z * c)⁻¹ * b) (h2 : b = z'⁻¹ * s * u) (h3 : u = κ * v) (h4 : w = s * v) : e * c * p = κ * w := by
  subst he h1 h2 h3 h4
  field_simp

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


set_option maxHeartbeats 4000000 in
theorem formulaAt_steps (hL : R.toLevCh.Is A.μ0) (hC : R.IsChain) (ch : Choice R) (hP : ProjAt ch) (hF : FlipAt ch)
    (hU : UnfoldAt ch) (hJ : JetsAt ch) (hc : ∀ i j t, ch.c i j t ≠ 0) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hK : ch.FieldOK) : ∃ κ ze, FormulaAt ch κ ze := by
  obtain ⟨τi, z, hF⟩ := hF
  obtain ⟨σ, z', hU⟩ := hU τi
  obtain ⟨hM, hJ⟩ := hJ
  obtain ⟨κ, hJ⟩ := hJ σ
  have key : ∀ t, ∃ e : D.what₂.LL, D.what₂.embLL e = (z t : ℂ) * z' t ∧ ∃ n : ℕ, 0 < n ∧ e ^ n = 1 := fun t => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    obtain ⟨h1, e, he⟩ := mem_xiVals ho (hK.chars.xi t) (mul_mem (hF t).1 (hU t).1)
    refine ⟨e, he, n, hn, D.what₂.embLL.injective ?_⟩
    rw [map_pow, he, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  choose ze hze hzn using key
  refine ⟨κ, ze, hzn, fun t x hx a => ?_⟩
  obtain ⟨τ, hτ, hfl⟩ := (hF t).2 (ch.Phi a)
  obtain ⟨M, hMt⟩ := exists_vol ch.G hL t
  choose Mβ hMβ using hM t (ch.Phi a)
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ch.S.IsExpansion t (ch.Phi a) β
      (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) := fun β hβ => Classical.epsilon_spec ((hS t a).ex β hβ)
  have e1 : psiK ch a (R.Th t (R.jX t x)) =
      Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.cv.lift t (R.jX t x))) := by
    exact congrArg (fun u => Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) u))
      ((form_Th ch hC t _).trans (hP t x hx))
  have e2 := (hU t).2 a τ hτ M hMt Mβ (fun β => Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β))
    (fun β hβ => ⟨hMβ β, hex β hβ⟩) (R.jX t x)
  have e3 : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
      defTot t ch.S.toGridChoice (Mβ β) σ (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (colFn ch a)
        (formTop ch t (R.jX t x))) = κ * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := by
    rw [(hS t a).vCore_eq _ hex, finsum_mem_eq_finite_toFinset_sum _ (hS t a).fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := (Set.Finite.mem_toFinset _).1 hβ
    exact (congrArg (HMul.hMul _) (hJ t a β hβ' (Mβ β) _ (hMβ β) (hex β hβ') (R.jX t x))).trans (mul_left_comm _ _ _)
  have e4 : vK ch t x a = ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := rfl
  have hct : cTot ch t ≠ 0 := (cTot_ne_zero_iff ch t).2 fun i j => hc i j t
  have e5 := congrArg (Bplus ch.W ch.M (colFn ch a)) (hfl M hMt (R.jX t x)).2
  exact scalar_calc (hze t) (z t).ne_zero (z' t).ne_zero hct (e1.trans (e5.trans (Bplus_smul_form _ _ _ _ _))) e2 e3 e4

theorem formula2K (hP : StepProj) (hF : StepFlip) (hU : StepUnfold) (hJ : StepJets) (hc : ConstK) (hS : SumOKK) :
    Formula2K := by
  obtain ⟨C0, H⟩ := ((((hP.and hF).and hU).and hJ).and hc).and hS
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j hK => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact formulaAt_steps s.core.lev s.core.chain ch a b c d (fun i j t => (f i j t).2) g hK

end GlobalTheory.RowClaim.FormulaTwo

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevelStatement
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestLiftFormula_principalLevel : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := by
  first | exact @GlobalTheory.RowClaim.FormulaTwo.formula2K | exact GlobalTheory.RowClaim.FormulaTwo.formula2K | (intros; apply GlobalTheory.RowClaim.FormulaTwo.formula2K <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.GaussLine

theorem pairInf_nondeg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (q : κ → mixedEmbedding.mixedSpace F),
    (∀ x, GlobalTheory.GaussLine.pairInf F κ x q = 0) → q = 0 := by
  intro F _ _ κ _ q hq
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have h := hq (Pi.single i b)
  rw [GlobalTheory.GaussLine.pairInf_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp),
    Pi.single_eq_same, mul_comm] at h
  simpa using h

end GlobalTheory.GaussLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePairingArchimedeanVars_nondegenerate_right : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (q : κ → mixedEmbedding.mixedSpace F),
    (∀ x, GlobalTheory.GaussLine.pairInf F κ x q = 0) → q = 0 := by
  first | exact @GlobalTheory.GaussLine.pairInf_nondeg | exact GlobalTheory.GaussLine.pairInf_nondeg | (intros; apply GlobalTheory.GaussLine.pairInf_nondeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.ArchUniq.SchrTransport

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coords (P : V → V → ℝ) (hP : IsPairing P) [FiniteDimensional ℝ V] (n : ℕ) (hn : Module.finrank ℝ V = n) :
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, pPart (φ v) = C v.1) ∧ ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2 := by
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  refine ⟨C, φ, fun v => ?_, fun v y => ?_⟩
  · ext i; simp [hφ, pPart, pairCoordsL]
  · rw [pair_expand C hP y v.2]
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]

theorem schr_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (v : V × V) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    schrF P v (f ∘ C) = rhoFun (φ v) f ∘ C := by
  funext y
  have h2 : ⟪pPart (φ v), qPart (φ v)⟫ = -P v.1 v.2 := by rw [hp, real_inner_comm, hq]
  have h3 : ⟪C v.1, qPart (φ v)⟫ = -P v.1 v.2 := by rw [real_inner_comm, hq]
  simp only [schrF, rhoFun, phase, Function.comp_apply, map_add (f := _), hp, hq, h3]
  congr 2
  push_cast
  ring

theorem dRho_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (u : V × V) (g : 𝓢(V, ℂ)) (h : Sch (Fin n))
    (hg : ⇑g = ⇑h ∘ ⇑C) (y : V) :
    fderiv ℝ (⇑g) y u.1 - 2 * Real.pi * Complex.I * (P y u.2 : ℂ) * g y = dRho (φ u) h (C y) := by
  have hd : HasFDerivAt (⇑h ∘ ⇑C) ((fderiv ℝ (⇑h) (C y)).comp (C : V →L[ℝ] EuclideanSpace ℝ (Fin n))) y :=
    (h.hasFDerivAt (C y)).comp y C.hasFDerivAt
  rw [dRho_apply, hg, hd.fderiv, hp, hq]
  simp
  ring

theorem quad_eq_sum {l : Type} [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    quad X = ∑ p : (l ⊕ l) × (l ⊕ l), ((4 * Real.pi * Complex.I : ℂ)⁻¹ *
      ((((X * Matrix.J l ℝ) p.1 p.2 + (X * Matrix.J l ℝ) p.2 p.1) / 2 : ℝ) : ℂ)) •
        (dRho (Pi.single p.1 1) * dRho (Pi.single p.2 1)) := by
  rw [quad, Fintype.sum_prod_type, Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => (4 * Real.pi * Complex.I : ℂ)⁻¹ • (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (dRho (Pi.single b 1) * dRho (Pi.single a 1))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_smul]
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem haar_coords {n : ℕ} [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, 0 < k ∧ ∀ F : V → ℝ, ∫ y, F y ∂μ = k * ∫ x, F (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ),
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun F => ?_⟩
  have h1 : ∫ y, F y ∂μ = ∫ x, F (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, F (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro V _ _ _ _ _ μ hμ P hP n hn H A T hAc hTadd hT0 hTi hTl2 hTc
  obtain ⟨C, φ, hp, hq⟩ := coords P hP n hn
  have hS := schr_coords P C φ hp hq
  let toE : 𝓢(V, ℂ) →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n) := fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := haar_coords μ C
  have c1 : ∀ w, Continuous fun t => A' t w := by
    intro w
    exact (φ.toLinearMap.continuous_of_finiteDimensional).comp (hAc (φ.symm w))
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have c6 : ∀ f y, Continuous fun t => T' t f y := by
    intro h y
    exact hTc (toV h) (C.symm y)
  obtain ⟨X, c, hX⟩ := H A' T' c1 c2 c3 c4 c5 c6
  let eq := (Fintype.equivFin ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))).symm
  let S := X * Matrix.J (Fin n) ℝ
  refine ⟨Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)), fun i => φ.symm (Pi.single (eq i).1 1),
    fun i => φ.symm (Pi.single (eq i).2 1),
    fun i => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S (eq i).1 (eq i).2 + S (eq i).2 (eq i).1) / 2 : ℝ) : ℂ), c, ?_⟩
  intro f g₁ g₂ hg₁ hg₂ y
  have hf : ⇑f = ⇑(toE f) ∘ ⇑C := by ext x; simp [htoE]
  have h1 : ∀ i, ⇑(g₁ i) = ⇑(dRho (Pi.single (eq i).2 1) (toE f)) ∘ ⇑C := fun i => by
    ext x
    rw [hg₁, dRho_coords P C φ hp hq _ f (toE f) hf, LinearEquiv.apply_symm_apply]
    rfl
  have h2 : ∀ i, g₂ i y = dRho (Pi.single (eq i).1 1) (dRho (Pi.single (eq i).2 1) (toE f)) (C y) := fun i => by
    rw [hg₂, dRho_coords P C φ hp hq _ (g₁ i) _ (h1 i), LinearEquiv.apply_symm_apply]
  have hd := hX (toE f) (C y)
  have e1 : (fun t => T' t (toE f) (C y)) = fun t => T t f y := by
    funext t
    simp [hT', htoE, hVE]
  rw [e1] at hd
  convert hd using 1
  have e2 : toE f (C y) = f y := by simp [htoE]
  rw [e2, quad_eq_sum]
  congr 1
  simp only [h2, ContinuousLinearMap.coe_sum', Finset.sum_apply, SchwartzMap.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.mul_apply, smul_eq_mul]
  exact Equiv.sum_comp eq (fun p => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S p.1 p.2 + S p.2 p.1) / 2 : ℝ) : ℂ) *
    dRho (Pi.single p.1 1) (dRho (Pi.single p.2 1) (toE f)) (C y))

end GlobalTheory.ArchUniq.SchrTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinatesStatement
open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPairingSpace_result_of_schrodingerCoordinates : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @GlobalTheory.ArchUniq.SchrTransport.transport | exact GlobalTheory.ArchUniq.SchrTransport.transport | (intros; apply GlobalTheory.ArchUniq.SchrTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerConvergence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowConvAll

theorem multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

end GlobalTheory.RowConvAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.EmbAtPlace

variable {D : D7}

theorem mat_ext {m n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {M N : Matrix m n (Formalism.L2.Theta.AE D)}
    (h1 : M.map (Formalism.L2.Theta.finPart D) = N.map (Formalism.L2.Theta.finPart D))
    (h2 : ∀ τ, M.map (fun z => θ τ (Formalism.L2.Theta.infPart D z)) = N.map (fun z => θ τ (Formalism.L2.Theta.infPart D z))) :
    M = N := by
  ext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j

theorem vec_ext {n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {v w : n → Formalism.L2.Theta.AE D}
    (h1 : ∀ i, Formalism.L2.Theta.finPart D (v i) = Formalism.L2.Theta.finPart D (w i))
    (h2 : ∀ τ i, θ τ (Formalism.L2.Theta.infPart D (v i)) = θ τ (Formalism.L2.Theta.infPart D (w i))) : v = w := by
  funext i
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact h1 i
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact h2 τ i

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (Formalism.L2.Theta.infPart D (incA D e)) = tauE D τ e := by
  have : Formalism.L2.Theta.infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
    simp [Formalism.L2.Theta.infPart, incA, inclR]
  rw [this]; exact (hθ τ).1 e

end GlobalTheory.EmbAtPlace

namespace GlobalTheory.EmbAtPlace

theorem embRel_atTau : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (τ : D.what₂.Tau)
    (h : Matrix (Fin A.rank) (Fin A.rank) ℂ) (g : Matrix (Fin B.rank) (Fin B.rank) ℂ), h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ) →
    g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ) → GlobalTheory.RealBessel.IsEmb (gramAt D B τ) ((frameMat B A ι).map (tauE D τ)) g h →
    EmbRel B A ι (atTau θ B τ g) (atTau θ A τ h) := by
  classical
  intro D θ hθ A B ι τ h g hh hg hE
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hX := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hg
  have hY := GlobalTheory.PointAtPlaceHom.atTau_spec hθ A τ hh
  have fX : (matHom B (atTau θ B τ g)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin B.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hX.1)).trans Units.val_one
  have fY : (matHom A (atTau θ A τ h)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hY.1)).trans Units.val_one
  have iX : ∀ τ', (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then g else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hX.2.1
    · exact hX.2.2 τ' e
  have iY : ∀ τ', (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then h else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hY.2.1
    · exact hY.2.2 τ' e
  have iF : ∀ τ', ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      (frameMat B A ι).map (tauE D τ') := fun τ' => by
    rw [Matrix.map_map]; congr 1; funext e; exact GlobalTheory.EmbAtPlace.theta_incA hθ τ' e
  refine ⟨?_, fun x hx => ?_⟩
  · refine GlobalTheory.EmbAtPlace.mat_ext hσ ?_ fun τ' => ?_
    · rw [Matrix.map_mul, Matrix.map_mul, fX, fY, Matrix.one_mul, Matrix.mul_one]
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change Matrix.map (_ * _) ⇑φ = Matrix.map (_ * _) ⇑φ
      rw [Matrix.map_mul, Matrix.map_mul]
      change (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
        ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z))
      rw [iX, iY, iF]
      split_ifs with e
      · subst e; exact hE.1
      · rw [Matrix.one_mul, Matrix.mul_one]
  · refine GlobalTheory.EmbAtPlace.vec_ext hσ (fun i => ?_) fun τ' i => ?_
    · rw [RingHom.map_mulVec, fX, Matrix.one_mulVec]; rfl
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change φ _ = φ _
      rw [RingHom.map_mulVec]
      change ((matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *ᵥ
        fun j => θ τ' (Formalism.L2.Theta.infPart D (incA D (x j)))) i = θ τ' (Formalism.L2.Theta.infPart D (incA D (x i)))
      simp only [GlobalTheory.EmbAtPlace.theta_incA hθ]
      rw [iX]
      split_ifs with e
      · subst e
        have h0 : (((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ') *ᵥ (fun j => tauE D τ' (x j)) = 0 := by
          have hm : ((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ' =
              (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).map (tauE D τ') := by
            rw [Matrix.map_mul]
            congr 1
            ext a b
            simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
            exact (Formalism.IndefR.Eqv.tauE_star D τ' _).symm
          rw [hm]
          funext i
          have := RingHom.map_mulVec (tauE D τ') (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram) x i
          simp only [Function.comp_def] at this
          rw [← this, hx]
          simp
        exact congrFun (hE.2 _ h0) i
      · rw [Matrix.one_mulVec]

end GlobalTheory.EmbAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embRel_atRealPlace_of_unitaryEmbedding : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (τ : D.what₂.Tau)
    (h : Matrix (Fin A.rank) (Fin A.rank) ℂ) (g : Matrix (Fin B.rank) (Fin B.rank) ℂ), h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ) →
    g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ) → GlobalTheory.RealBessel.IsEmb (gramAt D B τ) ((frameMat B A ι).map (tauE D τ)) g h →
    EmbRel B A ι (atTau θ B τ g) (atTau θ A τ h) := by
  first | exact @GlobalTheory.EmbAtPlace.embRel_atTau | exact GlobalTheory.EmbAtPlace.embRel_atTau | (intros; apply GlobalTheory.EmbAtPlace.embRel_atTau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslates
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfWaves

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

theorem isSBHalf_trans {a : AE D} {Λ : AddSubgroup (WO S T)} {x : WO S T} (hx : IsHalf a x) {k : ℕ} (hk : 0 < k)
    (hkx : k • x ∈ Λ) : IsSBHalf a Λ fun t => halfInd a Λ (t + x) := by
  have hx' := (isHalf_iff S T).1 hx
  refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    refine (isHalf_iff S T).2 ?_
    exact (add_mem_cancel_right hx').1 ((isHalf_iff S T).1 h.2)
  · have hm : k • u ∈ Λ ⊓ half S T a :=
      nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k
    rw [halfInd_eq_ind]
    change ind _ (t + k • u + x) = ind _ (t + x)
    rw [add_right_comm]
    exact ind_add _ _ hm
  · have h : t + x ∈ Λ ∧ IsHalf a (t + x) := by
      by_contra h
      exact ht (if_neg h)
    have e : k • t = k • (t + x) - k • x := by rw [nsmul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem h.1 k) hkx

theorem isSBHalf_modul (ψ : AddChar (AF D.host.F) ℂ) {a : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : IsHalf (cA D a) y) {k : ℕ} (hk : 0 < k) (hky : k • y ∈ Λ) {Φ : WO S T → ℂ}
    (hΦ : IsSBHalf a Λ Φ) : IsSBHalf a Λ fun t => ψ (symplO S T t y) * Φ t := by
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  obtain ⟨a1, k', hk1, a2, a3⟩ := hΦ
  refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_nsmul]
      exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
    have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
      rw [mul_nsmul']
      exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _
        ⟨hky, nsmul_mem ((isHalf_iff S T).1 hy) k⟩)
    simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
  · rw [mul_nsmul']
    exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k

end GlobalTheory.HalfWaves

namespace GlobalTheory.PlaceTensor

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.HalfWaves

theorem halfWaves_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → a * cA D a = 0 → infPart D a = 0 → (∀ x y : WO S T, IsHalf a x → IsHalf (cA D a) y → IsSBHalf a (latO S T ΛS ΛT fun _ => True) (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Tm (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) = heisO ψ S T y (heisO ψ S T x f₀)) ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → Φ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧ Ψ = fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)} := by
  intro D ψ S T ΛS ΛT hψ hS hT e he _ hinf
  have hSfull := GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS
  have hTfull := GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin0 := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin0 k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hsb : ∀ x, IsHalf e x → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x hx => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hSfull hTfull x (infPart_of_half hinf hx)
    exact isSBHalf_trans hx hk hk'
  have hmod : ∀ x y, IsHalf e x → IsHalf (cA D e) y → IsSBHalf e (latO S T ΛS ΛT fun _ => True)
      fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := fun x y hx hy => by
    obtain ⟨k, hk, hk'⟩ := exists_nsmul_mem_latO' hSfull hTfull y (infPart_of_half (infPart_cA hinf) hy)
    exact isSBHalf_modul ψ hLL' hy hk hk' (hsb x hx)
  refine ⟨fun x y hx hy => ⟨hmod x y hx hy, fun f₀ Tm hTm => ?_⟩, fun Φ hΦ => ?_⟩
  · have v := hTm.vac
    rw [one_smul] at v
    rw [hTm.modul _ (hsb x hx) y hy, hTm.trans _ (GlobalTheory.isSBHalf_halfInd e _) x hx, v]
  · have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
        ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
      obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
      exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
        (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
        fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
    refine (Submodule.span_le.2 ?_) hm
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        ψ (symplO S T x y) • fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) (t + x) := by
      funext t
      simp only [wave, Pi.smul_apply, smul_eq_mul, halfInd_eq_ind, symplO_add_left, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, y, (isHalf_iff S T).2 hx, (isHalf_iff S T).2 hy, rfl⟩)

end GlobalTheory.PlaceTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → a * cA D a = 0 → infPart D a = 0 → (∀ x y : WO S T, IsHalf a x → IsHalf (cA D a) y → IsSBHalf a (latO S T ΛS ΛT fun _ => True) (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Tm (fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)) = heisO ψ S T y (heisO ψ S T x f₀)) ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → Φ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧ Ψ = fun t => ψ (symplO S T t y) * halfInd a (latO S T ΛS ΛT fun _ => True) (t + x)} := by
  first | exact @GlobalTheory.PlaceTensor.halfWaves_span | exact GlobalTheory.PlaceTensor.halfWaves_span | (intros; apply GlobalTheory.PlaceTensor.halfWaves_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchCancel

theorem eq_of_tens_eq : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (r : (κ → AF F) → ℂ),
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → r (x + z) = r x) → (∃ x, r x ≠ 0) →
    ∀ f₁ f₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₂ r → f₁ = f₂ := by
  intro F _ _ κ _ r hr hne f₁ f₂ h
  obtain ⟨x₀, hx₀⟩ := hne
  refine DFunLike.ext f₁ f₂ fun y => ?_
  let z : κ → AF F := fun i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)), 0)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
    intro u hu
    funext i
    have hu1 : u.1 = 0 := by
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
    show u * z i = 0
    refine Prod.ext ?_ ?_
    · show u.1 * (z i).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (z i).2 = 0
      show u.2 * 0 = 0
      rw [mul_zero]
  have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x₀ + z) i)) = y := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x₀ i).1 +
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i))) = y i
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) + (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)) = y i
    exact add_sub_cancel _ _
  have h2 := congrFun h (x₀ + z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at h2
  rw [hev, hr x₀ z hz] at h2
  exact mul_right_cancel₀ hx₀ h2

end GlobalTheory.ArchCancel
end
