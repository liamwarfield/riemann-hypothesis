module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowRep

open GlobalTheory.SmoothMultilinear

theorem act_list {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : (∀ τ, M.H τ) → K)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      F (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (F y))
    (y : ∀ τ, M.H τ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V p.1)) :
    ρ (l.map fun p => atTau θ V p.1 p.2).prod (F y) =
      F fun τ => M.rep τ (l.map fun p => if p.1 = τ then p.2 else 1).prod (y τ) := by
  induction l with
  | nil => simp [rep_one]
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1) := fun q hq => hl q (by simp [hq])
    rw [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl',
      ← h p.1 p.2 (hl p (by simp))]
    congr 1
    funext τ
    rw [List.map_cons, List.prod_cons]
    by_cases e : p.1 = τ
    · subst e
      rw [Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]
      apply GlobalTheory.SmoothMultilinear.prod_mem
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      split_ifs with e
      · exact e ▸ hl' q hq
      · exact GlobalTheory.SmoothMultilinear.prod_mem _ [] (by simp)
    · rw [Function.update_of_ne (Ne.symm e), if_neg e, one_mul]

theorem smooth_of_contDiff {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (F : (∀ τ, M.H τ) → K) (hF : ContDiff ℝ ∞ F)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      F (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (F y)) (v : M.Vec) :
    GlobalTheory.HolDict.IsSmoothVector' θ V ρ (F fun τ => (v τ : M.H τ)) := by
  have hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) := fun τ => smooth_of_span _ _ _ (v τ).2
  intro k τs Xs hX
  have e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (F fun τ => (v τ : M.H τ))) =
      fun t : Fin k → ℝ => F fun τ => M.rep τ
        (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ) := by
    funext t
    have := act_list θ M ρ F h (fun τ => (v τ : M.H τ))
      (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by
        intro p hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact exp_mem _ _ (hX i) _)
    simp only [List.map_ofFn] at this
    refine this.trans ?_
    congr 1
    funext τ
    congr 4
    funext i
    dsimp only [Function.comp_apply, Prod.fst, Prod.snd]
    split_ifs <;> simp
  rw [e]
  refine hF.comp (contDiff_pi.2 fun τ => ?_)
  refine hs τ k _ fun i => ?_
  split_ifs with e
  · exact e ▸ hX i
  · simp [lieAt]

theorem contDiff_anti {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] (c : A ≃ₗᵢ⋆[ℂ] B) : ContDiff ℝ ∞ c := by
  let L : A →L[ℝ] B :=
    { toFun := c
      map_add' := c.map_add
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, c.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]; rfl
      cont := c.continuous }
  exact L.contDiff


set_option maxHeartbeats 1000000 in
theorem exists_contRep : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) := by
  intro _ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ u
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, M.H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCd : ContDiff ℝ ∞ C := by
    refine contDiff_pi.2 fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (contDiff_anti (c τ)).comp (contDiff_pi.1 contDiff_id τ)
  let F : (∀ τ, M.H τ) → L2X X := fun y => Φ (X.B.tens (C y))
  have hF : ContDiff ℝ ∞ F := by
    have e : F = fun y => (Φ.compContinuousMultilinearMap m) (C y) := by
      funext y
      show Φ (X.B.tens (C y)) = Φ (m (C y))
      rw [hm]
    rw [e]
    exact (((Φ.compContinuousMultilinearMap m).contDiff (n := ∞)).restrict_scalars ℝ).comp hCd
  have hsm := smooth_of_contDiff θ M ρ F hF (fun τ a ha y => by
    obtain ⟨q1, q2, -⟩ := hat τ a ha
    rw [h3]
    refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
    obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
    rw [hC, hC]
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hc _ a ha _
    · rw [Function.update_of_ne e]
      have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
      rw [q]
      have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
      show _ = X.B.σ (X.pl.symm τ') 1 _
      rw [this]
      rfl) u
  obtain ⟨R, L, -, hR, -⟩ := GlobalTheory.TensRep.exists_adelic_rep (ι := fun v x => X.B.I.ext v (T x)) hθ h1 h2 h5 h6 h7
    h8 h9 hU
  obtain ⟨p1, p2⟩ := hR _ hsm (fun k hk hk' => by
    rw [h3]
    have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
    rw [e]
    exact hlev _ (hUg k hk) _)
  refine ⟨fun x => R (F fun τ => (u τ : M.H τ)) (T.symm x),
    GlobalTheory.RepSmooth.isContRep_of_ae X.B (p1.comp hT') (fun γ hγ x => ?_) ?_⟩
  · have e : (fun x => R (F fun τ => (u τ : M.H τ)) (T.symm γ * x)) = R (F fun τ => (u τ : M.H τ)) :=
      ((p1.comp (continuous_const_mul _)).ae_eq_iff_eq μ p1).1
        (Filter.EventuallyEq.trans
          (((measurePreserving_mul_left μ _).quasiMeasurePreserving.ae p2).mono fun _ hy => hy.symm)
          ((h10 (T.symm γ) (by rw [T.apply_symm_apply]; exact hγ) _).trans p2))
    rw [map_mul]
    exact congrFun e _
  · filter_upwards [h4 _ p2] with x hx
    rw [← hx, T.apply_symm_apply]
    rfl

end GlobalTheory.ConjRowRep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_leftInvariant_rep_conjugateTensor : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) := by
  first | exact @GlobalTheory.ConjRowRep.exists_contRep | exact GlobalTheory.ConjRowRep.exists_contRep | (intros; apply GlobalTheory.ConjRowRep.exists_contRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatio
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

namespace GlobalTheory.Core.Rk.SchPeriod

theorem theta_eq_sum_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x : Mx D B.rank A.rank, (Summable fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => ‖sch ψ A B ν 𝓨 f (x + rat ξ)‖) ∧ HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ)) (f ((dblDec A).extX B x)) := by
  intro D ψ hψ A B ν 𝓨 hcov f hf x
  have hF : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B ((dblDec A).extX B x) f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ (dblSp A) B).1 _ _ hf
  have h1 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ f hf).1
  have h5 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ _ hF).2.2.2.2 0
  have h0 : heisO ψ (dblSp A) B ((dblDec A).extX B x) f ((dblDec A).ext0 B 0) = f ((dblDec A).extX B x) := by
    rw [map_zero]
    simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have H : HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ))
      (f ((dblDec A).extX B x)) := by
    rw [h0] at h5
    convert h5 using 1
    funext ξ
    rw [h1, add_comm]
    rfl
  exact ⟨summable_norm_iff.2 H.summable, H⟩

end GlobalTheory.Core.Rk.SchPeriod

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatioStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x : Mx D B.rank A.rank, (Summable fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => ‖sch ψ A B ν 𝓨 f (x + rat ξ)‖) ∧ HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ)) (f ((dblDec A).extX B x)) := by
  first | exact @GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch | exact GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch | (intros; apply GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProducts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProducts
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.FinRank

theorem span_eval_eq_top {α : Type*} (E : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ E] :
    Submodule.span ℂ (Set.range fun u : α => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) = ⊤ := by
  set Sp := Submodule.span ℂ (Set.range fun u : α => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype)
  have hb : Sp.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext u
    have := hx _ (Submodule.subset_span ⟨u, rfl⟩)
    simpa using this
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Sp)
  rw [← this, hb, Submodule.dualAnnihilator_bot]

theorem sum_prod_of_slices {α β : Type*} (C : α → β → ℂ) (E : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ E]
    (E' : Submodule ℂ (β → ℂ)) (hl : ∀ v, (fun u => C u v) ∈ E) (hr : ∀ u, C u ∈ E') :
    ∃ (n : ℕ) (e : Fin n → α → ℂ) (g : Fin n → β → ℂ), (∀ i, e i ∈ E) ∧ (∀ i, g i ∈ E') ∧
      ∀ u v, C u v = ∑ i, e i u * g i v := by
  let b := Module.finBasis ℂ E
  let ev : α → Module.Dual ℂ E := fun u => (LinearMap.proj u : (α → ℂ) →ₗ[ℂ] ℂ).comp E.subtype
  have hsurj : ∀ φ : Module.Dual ℂ E, ∃ a : α →₀ ℂ, Finsupp.linearCombination ℂ ev a = φ := by
    intro φ
    have h1 : φ ∈ LinearMap.range (Finsupp.linearCombination ℂ ev) := by
      rw [Finsupp.range_linearCombination]
      rw [span_eval_eq_top E]
      trivial
    exact h1
  choose a ha using fun i => hsurj (b.coord i)
  refine ⟨Module.finrank ℂ E, fun i => (b i : α → ℂ), fun i => ∑ u ∈ (a i).support, a i u • C u,
    fun i => (b i).2, fun i => Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (hr u), ?_⟩
  intro u v
  have hs := b.sum_repr ⟨fun u => C u v, hl v⟩
  have h2 := congrArg (fun w : E => (w : α → ℂ) u) hs
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  have h3 := congrArg (fun φ : Module.Dual ℂ E => φ ⟨fun u => C u v, hl v⟩) (ha i)
  simp only [Module.Basis.coord_apply] at h3
  rw [← h3, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  simp [ev, Finset.sum_apply]

end GlobalTheory.SeeSaw.FinRank

namespace GlobalTheory.SeeSaw.FinRank

theorem biVac_sum_fock : ∀ (D : D7), CenFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (χ' : GA D S → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C u v) = χ a • fun u => C u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k'.om (b, 1) (C u) = χ' b • C u) → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := by
  intro D hF ψ θ hθ A S A' x y z hx hy hz k k' hk hk' χ χ' C hC hχ hχ'
  obtain ⟨W, hW, hWf⟩ := hF ψ θ hθ A S x y hx hy k hk χ
  obtain ⟨W', _, hWf'⟩ := hF ψ θ hθ S A' y z hy hz k' hk' χ'
  haveI := hW
  let T := pureTensorO ψ θ A S x.s y.s x.B y.B k.vac
  let T' := pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac
  have hl : ∀ v, (fun u => C u v) ∈ W.map T := by
    intro v
    obtain ⟨P, hP, e⟩ := hWf _ (hC.left v).1 (hC.left v).2 (fun a ha hc => hχ a ha hc v)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  have hr : ∀ u, C u ∈ W'.map T' := by
    intro u
    obtain ⟨P, hP, e⟩ := hWf' _ (hC.right u).1 (hC.right u).2 (fun b hb hc => hχ' b hb hc u)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  obtain ⟨n, e, g, he, hg, hs⟩ := sum_prod_of_slices C (W.map T) (W'.map T') hl hr
  choose P _ hP using fun i => Submodule.mem_map.1 (he i)
  choose P' _ hP' using fun i => Submodule.mem_map.1 (hg i)
  refine ⟨n, P, P', fun u v => ?_⟩
  rw [hs u v]
  refine Finset.sum_congr rfl fun i _ => ?_
  show e i u * g i v = T (P i) u * T' (P' i) v
  rw [hP i, hP' i]

end GlobalTheory.SeeSaw.FinRank

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProductsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralEigen_realDatum_finite_sum_fockProducts : ∀ (D : D7), CenFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (χ' : GA D S → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C u v) = χ a • fun u => C u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k'.om (b, 1) (C u) = χ' b • C u) → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := by
  first | exact @GlobalTheory.SeeSaw.FinRank.biVac_sum_fock | exact GlobalTheory.SeeSaw.FinRank.biVac_sum_fock | (intros; apply GlobalTheory.SeeSaw.FinRank.biVac_sum_fock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLifts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem comb_sum_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) {n : ℕ} (a : Fin n → ℂ)
    (F : Fin n → WO S T → ℂ) :
    comb ψ S T c (fun w => ∑ i, a i * F i w) = fun w => ∑ i, a i * comb ψ S T c (F i) w := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => by ring

theorem comb_pureTensorO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS sT BS BT) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (c : WO S T →₀ ℂ)
    (hc : IsFinComb c) (P : PolF D T.rank S.rank) :
    comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) P := by
  let e := c.support.equivFin
  have key := (GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D ψ θ S T hψ hθ sS sT BS BT f hf c.support.card (fun i => c (e.symm i).1)
    (fun i => (e.symm i).1) (fun i => hc _ (e.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ c.support, c u • g u = ∑ i, c (e.symm i).1 • g (e.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort c.support]
    exact (Equiv.sum_comp e.symm (fun u : c.support => c u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem integrableOn_kernel {S T : HSp D} (hS : CoCpt S) (v : Vol S) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {φ : GA D S → ℂ} (hφ : IsContAut S φ) (h : GA D T) :
    IntegrableOn (fun g => om (g, h) f 0 * φ g) v.𝓕 v.μ := by
  have hc : Continuous fun g : GA D S => om (g, h) f 0 :=
    (hw.om_cont f hf 0).comp (by fun_prop : Continuous fun g : GA D S => (g, h))
  refine (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS v Unit (fun g _ => om (g, h) f 0 * φ g) ((hc.mul hφ.2).comp continuous_fst) ?_).1 ()
  intro γ hγ g _
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply, hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ _ hf), hφ.1 γ hγ g]

theorem biLift_biComb_fockSum : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank) (C : WO A S → WO S A' → ℂ), (∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D _ _ hL ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C hC φ hφ
  obtain ⟨χA, χS, hwA⟩ := hk.weil
  obtain ⟨χS', χA', hwB⟩ := hk'.weil
  have hX : ∀ i, IsThetaFunO ψ A S (k.pt ψ θ x y (P i)) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).1
  have hY : ∀ i, IsThetaFunO ψ S A' (k'.pt ψ θ y z (P' i)) := fun i => (hL ψ θ hθ S A' y z hy hz k' hk' (P' i)).1
  have hLc : ∀ i, IsContAut S (k.lift ψ θ x y (P i) φ) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).2.1 φ hφ
  have hcX : ∀ i, comb ψ A S k.c (pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i)) = k.pt ψ θ x y (P i) := fun i =>
    comb_pureTensorO ψ θ A S hwA.std hθ _ _ _ _ k.vac hk.vac.2.theta k.c hk.fin (P i)
  have hcY : ∀ i, comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) = k'.pt ψ θ y z (P' i) :=
    fun i => comb_pureTensorO ψ θ S A' hwB.std hθ _ _ _ _ k'.vac hk'.vac.2.theta k'.c hk'.fin (P' i)
  have hbi : biComb ψ A S A' k.c k'.c C = fun u v => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v := by
    funext u v
    simp only [biComb]
    have e1 : (fun u' => comb ψ S A' k'.c (C u') v) = fun u' => ∑ i,
        comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) v *
          pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' := by
      funext u'
      have : C u' = fun v => ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' *
          pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := funext (hC u')
      rw [this, comb_sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e1, comb_sum_mul]
    simp only [hcX, hcY]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hint : ∀ h₀ h₁ h₂, k'.om (h₁, h₂) (fun v => k.om (h₀, h₁)
      (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) 0 =
      ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₀ h₁ h₂
    have e1 : ∀ v, (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) =
        ∑ i, k'.pt ψ θ y z (P' i) v • k.pt ψ θ x y (P i) := by
      intro v; funext u; simp [Finset.sum_apply, mul_comm]
    have e2 : (fun v => k.om (h₀, h₁) (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) =
        ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 • k'.pt ψ θ y z (P' i) := by
      funext v; rw [e1 v, map_sum]; simp [Finset.sum_apply, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, map_sum]; simp [Finset.sum_apply]
  funext h₂
  have hin : ∀ h₁, ∫ h₀ in x.vol.𝓕, φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
      k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 ∂x.vol.μ =
      ∑ i, k.lift ψ θ x y (P i) φ h₁ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₁
    have e : (fun h₀ => φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
        k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0) = fun h₀ => ∑ i,
          k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * φ h₀ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
      funext h₀; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
      rfl
    · intro i _
      exact (integrableOn_kernel hx.cpt x.vol hwA (hX i) hφ h₁).mul_const _
  simp only [biLift, hbi, hint, hin, Finset.sum_apply]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [KerDat.lift, liftT_apply]
    congr 1
    funext h₁
    exact mul_comm _ _
  · intro i _
    have := (integrableOn_kernel hy.cpt y.vol hwB (hY i) (hLc i) h₂)
    exact Integrable.congr this (Filter.Eventually.of_forall fun h₁ => mul_comm _ _)

end GlobalTheory.SeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLiftsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleLift_fockSum_eq_sum_iteratedLifts : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank) (C : WO A S → WO S A' → ℂ), (∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  first | exact @GlobalTheory.SeeSaw.biLift_biComb_fockSum | exact GlobalTheory.SeeSaw.biLift_biComb_fockSum | (intros; apply GlobalTheory.SeeSaw.biLift_biComb_fockSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisati
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisati
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RealParamSize

variable {D : D7} {m n : ℕ}

theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [map_add, map_add]

theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) :
    compAt θ τ (-x) = -compAt θ τ x := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.neg_apply]
  rw [(infPart D).map_neg, (θ τ).map_neg]

def realVec {k : ℕ} (θ : InfFam D) (L : (Fin k → ℝ) →+ Mx D m n) :
    (Fin k → ℝ) →+ (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun t := fun τ i j => compAt θ τ (L t) i j
  map_zero' := by ext τ i j; simp [compAt]
  map_add' a b := by ext τ i j; simp [compAt_add]

theorem norm_compAt_le (θ : InfFam D) (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem norm_vec_le (θ : InfFam D) (x : Mx D m n) :
    ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ ≤ GlobalTheory.Unf.realSize θ x :=
  (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j

theorem realSize_le (θ : InfFam D) (x : Mx D m n) :
    GlobalTheory.Unf.realSize θ x ≤ (Fintype.card D.what₂.Tau * (m * n) : ℝ) *
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ := by
  set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv
  unfold GlobalTheory.Unf.realSize
  calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ ∑ τ : D.what₂.Tau, ∑ i : Fin m, ∑ j : Fin n, ‖v‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (v τ i) j).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
    _ = _ := by simp [Finset.sum_const]; ring

theorem realSize_add_le (θ : InfFam D) (x y : Mx D m n) :
    GlobalTheory.Unf.realSize θ (x + y) ≤ GlobalTheory.Unf.realSize θ x + GlobalTheory.Unf.realSize θ y := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_add, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem realSize_neg (θ : InfFam D) (x : Mx D m n) : GlobalTheory.Unf.realSize θ (-x) = GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_neg, Matrix.neg_apply, norm_neg]

theorem continuous_realVec {θ : InfFam D} (hθ : IsInfFam θ) {k : ℕ} {L : (Fin k → ℝ) →+ Mx D m n}
    (hL : Continuous L) : Continuous (realVec θ L) :=
  continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp ((continuous_apply i).comp hL))

end GlobalTheory.RealParamSize


open GlobalTheory.RealParamSize in
theorem GlobalTheory.Unf.realParam_size_bounds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L → (∃ C : ℝ, ∀ t, GlobalTheory.Unf.realSize θ (L t) ≤ C * ‖t‖) ∧ (Function.Injective L → ∃ C : ℝ, ∀ (x : Mx D m n) t, ‖t‖ ≤ C * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x)) := by
  intro D θ hθ m n k L hL
  have hc := continuous_realVec hθ hL.1
  set A := (realVec θ L).toRealLinearMap hc with hA
  have hAt : ∀ t, A t = realVec θ L t := fun t => rfl
  have hvec : ∀ t, realVec θ L t = (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    fun t => rfl
  refine ⟨⟨(Fintype.card D.what₂.Tau * (m * n) : ℝ) * ‖A‖, fun t => ?_⟩, fun hinj => ?_⟩
  · refine (realSize_le θ (L t)).trans ?_
    rw [mul_assoc _ ‖A‖, ← hvec, ← hAt]
    exact mul_le_mul_of_nonneg_left (A.le_opNorm t) (by positivity)
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    have hker : (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      have h0 : realVec θ L t = 0 := by rw [← hAt]; exact ht
      have hLt : L t = 0 := by
        ext i j
        refine hσ.ext _ ?_ fun τ => ?_
        · have h := congrFun (congrFun (hL.2 t) i) j
          simpa only [Matrix.map_apply, Matrix.zero_apply] using h
        · have h := congrFun (congrFun (congrFun h0 τ) i) j
          exact h
      exact hinj (hLt.trans L.map_zero.symm)
    obtain ⟨K, -, hK⟩ := (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker
    refine ⟨K, fun x t => ?_⟩
    have h1 : ‖t‖ ≤ K * ‖A t‖ := by
      have := hK.le_mul_dist t 0
      simpa [dist_eq_norm] using this
    have h2 : ‖A t‖ ≤ GlobalTheory.Unf.realSize θ (L t) := by rw [hAt, hvec]; exact norm_vec_le θ (L t)
    have h3 : GlobalTheory.Unf.realSize θ (L t) ≤ GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x := by
      have := realSize_add_le θ (x + L t) (-x)
      rwa [realSize_neg, add_neg_cancel_comm] at this
    calc ‖t‖ ≤ K * ‖A t‖ := h1
      _ ≤ K * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) K.coe_nonneg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisatiStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L → (∃ C : ℝ, ∀ t, GlobalTheory.Unf.realSize θ (L t) ≤ C * ‖t‖) ∧ (Function.Injective L → ∃ C : ℝ, ∀ (x : Mx D m n) t, ‖t‖ ≤ C * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x)) := by
  first | exact @GlobalTheory.Unf.realParam_size_bounds | exact GlobalTheory.Unf.realParam_size_bounds | (intros; apply GlobalTheory.Unf.realParam_size_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem prod_diagonal_block_dets_eq_lower_block_det {κ : Type} [CommRing κ] {r t j n : ℕ} (hn : n = r + j * t) {g : GL (Fin n) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    ∏ c ∈ Finset.range j, dBlk (blkOf r t) (c + 1) g = dBlk (blk2 r) 1 g := by
  classical
  have hg2 : g ∈ blockTri (blk2 r) := blockTri_blkOf_le r t hg
  set M : Matrix (Fin n) (Fin n) κ := (g : Matrix (Fin n) (Fin n) κ) with hM
  have sq : ∀ (b : Fin n → ℕ) (c : ℕ), g ∈ blockTri b → ((dBlk b c g : κˣ) : κ) = (M.toSquareBlock b c).det := by
    intro b c h; rw [diag_block_det_val c h]; rfl
  have emp : ∀ (b : Fin n → ℕ) (c : ℕ), c ∉ Finset.univ.image b → (M.toSquareBlock b c).det = 1 := by
    intro b c hc
    haveI : IsEmpty {a : Fin n // b a = c} := ⟨fun a => hc (Finset.mem_image.2 ⟨a.1, Finset.mem_univ _, a.2⟩)⟩
    exact Matrix.det_isEmpty
  have hdet : ∀ (b : Fin n → ℕ) (N : ℕ), (∀ a, b a < N) → M.BlockTriangular b →
      M.det = ∏ c ∈ Finset.range N, (M.toSquareBlock b c).det := by
    intro b N hb hB
    rw [hB.det]
    refine Finset.prod_subset (fun c hc => ?_) (fun c _ hc => emp b c hc)
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2 (hb a)
  have h1 := hdet (blkOf r t) (j + 1) (fun a => by
      unfold blkOf
      split_ifs with h
      · omega
      · have ha : a.val - r < j * t := by have := a.2; omega
        have ht : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · simp [h0] at ha
          · exact h0
        have : (a.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ha)
        omega) hg
  have h2 := hdet (blk2 r) 2 (fun a => by unfold blk2; split_ifs <;> omega) hg2
  rw [Finset.prod_range_succ'] at h1
  rw [Finset.prod_range_succ', Finset.prod_range_one] at h2
  have h0 : (M.toSquareBlock (blkOf r t) 0).det = (M.toSquareBlock (blk2 r) 0).det := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (p := fun a : Fin n => blk2 r a = 0)
      (q := fun a : Fin n => blkOf r t a = 0) (fun a => by unfold blk2 blkOf; split_ifs <;> simp_all))]
    rfl
  have hu : IsUnit (M.toSquareBlock (blk2 r) 0).det := by rw [← sq _ 0 hg2]; exact Units.isUnit _
  apply Units.ext
  rw [Units.coe_prod, sq _ 1 hg2]
  rw [Finset.prod_congr rfl (fun c _ => sq _ (c + 1) hg)]
  rw [h0] at h1
  exact hu.mul_right_cancel (h1.symm.trans h2)

end GlobalTheory.FlatLevel

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem multT_le {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : MultT θ M J χ ≤ MultT θ M J' χ' :=
  Submodule.map_mono (Submodule.span_mono fun X hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩)


open Classical in
theorem lev_flat_le (c : Com D) (w : Twist D) (hw : w.Is c) (j : ℕ) {n : ℕ} (hn : n = D.R.r + j * D.R.t)
    (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D)) (hr hr' : D.R.r ≤ n)
    (x : GL (Fin n) (Lev.EAf D))
    (hx : x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B)) :
    x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) ∧
      levFn β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x =
        levFn β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x := by
  obtain ⟨hp, hP⟩ := mem_lev.1 hx
  obtain ⟨hUA, hSt, h3, -⟩ := mem_parLev.1 hp
  have h3' : ∀ PP ∈ c.Pg, redFn β PP x ∈ blockTri (blkOf D.R.r D.R.t) := h3
  have hP' : (fun PP : c.Pg => upperLeftBlock hr (redFn β PP.1 x)) ∈ c.P.H := hP
  have hone := (hw.grp _).1 hP'
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  refine ⟨mem_lev.2 ⟨mem_parLev.2 ⟨hUA, hSt, fun PP h => h3' PP (hPg PP h),
    fun PP h => blockTri_blkOf_le _ _ (h3' PP (hQ PP h))⟩, ?_⟩, ?_⟩
  · show _ ∈ (⊥ : Subgroup (G0 w.Pg D.R.r))
    refine Subgroup.mem_bot.2 (funext fun PP => ?_)
    exact hone ⟨PP.1, hPg PP.1 PP.2⟩ PP.2
  · unfold levFn
    have e1 : ext1 (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 c.P.H c.P.chi _ = 1
      unfold ext1
      split_ifs
      · rw [hw.chr]; rfl
      · rfl
    have e2 : ext1 (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 (LevelP.triv w.Pg D.R.r ℂ).H (LevelP.triv w.Pg D.R.r ℂ).chi _ = 1
      unfold ext1
      split_ifs
      · rfl
      · rfl
    rw [e1, e2]
    show 1 * (∏ PP ∈ c.Pg, ∏ c' ∈ Finset.range j, c.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ (∅ : Finset (Pl D.host.E)), (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x)) =
      1 * (∏ PP ∈ w.Pg, ∏ c' ∈ Finset.range j, w.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ w.Q, (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x))
    rw [Finset.prod_empty, mul_one, one_mul, one_mul, hw.union, Finset.prod_union hw.disj]
    congr 1
    · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c' _ => ?_
      rw [hw.chiPg (c' + 1) PP hP]
    · refine Finset.prod_congr rfl fun PP hP => ?_
      simp_rw [hw.chiQ _ PP hP]
      rw [← map_prod, prod_diagonal_block_dets_eq_lower_block_det hn (h3' PP (hQ PP hP))]


open Classical in
theorem flatLe : ∀ D : D7, FlatLe D := by
  intro D c w hw j _ s hs hr
  obtain ⟨hr', hL, hflat⟩ := hs
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  show MultT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) ≤
    MultT c.θ s.M (levS s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
      (Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
  rw [hL]
  refine multT_le c.θ s.M fun k hk => ?_
  obtain ⟨h1, h2⟩ := lev_flat_le c w hw j hn s.V.gram s.β hr hr' _ hk.2
  exact ⟨⟨hk.1, h1⟩, (congrArg (fun u : ℂˣ => (u : ℂ)) h2).symm⟩

end GlobalTheory.FlatLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level : ∀ D : D7, FlatLe D := by
  first | exact @GlobalTheory.FlatLevel.flatLe | exact GlobalTheory.FlatLevel.flatLe | (intros; apply GlobalTheory.FlatLevel.flatLe <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlace
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeUnif

theorem mul_not_mem_sq {R : Type*} [CommRing R] [IsDedekindDomain R] (Q : HeightOneSpectrum R) {a b : R}
    (hab : IsCoprime a b) (ha : a ∈ Q.asIdeal → a ∉ Q.asIdeal ^ 2) (hb : b ∈ Q.asIdeal → b ∉ Q.asIdeal ^ 2) :
    a * b ∉ Q.asIdeal ^ 2 := by
  intro h
  have := Q.isPrime
  have hle : Q.asIdeal ^ 2 ≤ Q.asIdeal := Ideal.pow_le_self two_ne_zero
  rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal h with h1 | h1
  · rcases Ideal.IsPrime.mul_mem_pow Q.asIdeal (mul_comm a b ▸ h) with h2 | h2
    · obtain ⟨u, v, huv⟩ := hab
      exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left u h1) (Q.asIdeal.mul_mem_left v h2)))
    · exact ha h1 h2
  · exact hb (hle h1) h1

theorem prod_not_mem_sq : ∀ (D : D7) (Q : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := by
  intro D Q _
  have key : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := fun k hk =>
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) Q hk).2.1
  have hc : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  rw [Nat.cast_mul]
  exact mul_not_mem_sq Q (Nat.Coprime.cast hc) (key 0) (key 1)

end GlobalTheory.TypePrimeUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlaceStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimes_product_not_mem_sq_place : ∀ (D : D7) (Q : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := by
  first | exact @GlobalTheory.TypePrimeUnif.prod_not_mem_sq | exact GlobalTheory.TypePrimeUnif.prod_not_mem_sq | (intros; apply GlobalTheory.TypePrimeUnif.prod_not_mem_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimePlaceMemOrConjGenusTypePlaceSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimePlaceMemOrConjGenusTypePlaceSet
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverConj

theorem isConjugatePlace_conjugateIdealPlace (D : D7) (P : Pl D.host.E) : Formalism.L2.DIV.IsConjPl P (Formalism.DivisionValues.conjPl P) := by
  intro a b hab
  have hb : b = Formalism.DivisionValues.cO D.host.E a := RingOfIntegers.ext (by rw [hab]; rfl)
  subst hb
  show a ∈ P.asIdeal ↔ Formalism.DivisionValues.cO D.host.E a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    rw [Ideal.mem_map_of_equiv] at h
    obtain ⟨x, hx, hxa⟩ := h
    rwa [← (Formalism.DivisionValues.cO D.host.E).injective hxa]

theorem cover : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  intro D Pg hPg Q hQ
  have hv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]
    exact hQ
  obtain ⟨PP, ⟨hPP, hunder⟩, -⟩ := hPg.2 _ hv
  refine ⟨PP, hPP, ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hunder.symm with h | h
  · exact Or.inl h
  · right
    intro s
    have hc : Formalism.L2.DIV.IsConjPl PP Q := h ▸ isConjugatePlace_conjugateIdealPlace D PP
    exact (Formalism.L2.DIV.resS_sigS_eq_zero_iff (instOf D).cm hc.symm s).symm

end GlobalTheory.CoverConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimePlaceMemOrConjGenusTypePlaceSetStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  first | exact @GlobalTheory.CoverConj.cover | exact GlobalTheory.CoverConj.cover | (intros; apply GlobalTheory.CoverConj.cover <;> assumption)
end
end
