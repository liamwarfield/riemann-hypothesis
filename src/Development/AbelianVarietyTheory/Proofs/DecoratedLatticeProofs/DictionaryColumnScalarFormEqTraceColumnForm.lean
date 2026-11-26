module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelRealPartMatrixFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelRealPartMatrixFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.RealMat

variable {D : D7}

theorem psiT_incA (τ : D.what₂.Tau) (x : D.host.E) : Formalism.IndefR.Eqv.psiT D τ (incA D x) = tauE D τ x := by
  show Formalism.IndefR.Eqv.thetaC D τ ((fstA D.host.F 1) ⊗ₜ[D.host.F] x) = _
  rw [Formalism.IndefR.Eqv.thetaC_tmul]
  simp

theorem embA_cols {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) :
    HMul.hMul (Formalism.L2.Theta.mt S (embA d o a)) (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) =
      HMul.hMul (rat (d.i₀ * o.iA) : Matrix (Fin S.rank) (Fin A.rank) (AE D)) (Formalism.L2.Theta.mt A a) := by
  have e : (rat (d.i₀ * o.iA) : Mx D S.rank A.rank) = HMul.hMul d.j0 o.jA := rat_mul _ _
  rw [e, GlobalTheory.MixPer.embA_apply d o a, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]

theorem embA_cols_at {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A) (τ : D.what₂.Tau) :
    (Formalism.L2.Theta.mt S (embA d o a)).map (Formalism.IndefR.Eqv.psiT D τ) * (d.i₀ * o.iA).map (tauE D τ) =
      (d.i₀ * o.iA).map (tauE D τ) * (Formalism.L2.Theta.mt A a).map (Formalism.IndefR.Eqv.psiT D τ) := by
  have e : (d.i₀ * o.iA).map (tauE D τ) =
      (rat (d.i₀ * o.iA) : Mx D S.rank A.rank).map (Formalism.IndefR.Eqv.psiT D τ) := by
    ext i j
    exact (psiT_incA τ _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, embA_cols]

theorem act_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (hr : (D.sp.Y 0).rank = I.n) (k : GA D (D.sp.Y 0))
    (τ : D.what₂.Tau) {m : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin m) D.host.E) (M : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin m → Fin I.n → I.E) (hx : ∀ i j, C i j = ιE (x j (Fin.cast hr i)))
    (hC : (Formalism.L2.Theta.mt (D.sp.Y 0) k).map (Formalism.IndefR.Eqv.psiT D τ) * C.map (tauE D τ) = C.map (tauE D τ) * M) (b : Fin m) :
    uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 (pl.symm τ)) *ᵥ rv I (pl.symm τ) (x b) =
      ∑ i, M i b • rv I (pl.symm τ) (x i) := by
  subst h
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (SeeReal.phi_inst v x))
  have hcol : ∀ j, (fun i => (Formalism.L2.SG.InstExistsPf.instOf D).φ (pl.symm τ) (x j i)) =
      fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    funext i
    rw [hφ, Equiv.apply_symm_apply]
    exact (congrArg (tauE D τ) (hx i j)).symm
  subst hpl
  have hT : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := rfl
  have hP := Formalism.L2.SG.EvalTIota.P_isUnit_det' (D := D) (Formalism.L2.Host.tauPl D τ)
  have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i (Formalism.IndefR.RationalEmbedding.iota D k) τ
  rw [ContinuousMulEquiv.symm_apply_apply, Formalism.IndefR.Eqv.infMat_thetaC] at hbr
  have hu := SeeReal.eq_of_conj hP hbr.symm
  have hrv : ∀ j, rv (Formalism.L2.SG.InstExistsPf.instOf D) ((Formalism.L2.Host.tauPl D).symm.symm τ) (x j) =
      (Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j := by
    intro j
    rw [← hcol j]
    rfl
  have main : Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ
      ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i b) =
      ∑ j, M j b • ((Formalism.L2.SG.EvalTIota.Pi (D := D) (Formalism.L2.Host.tauPl D τ))⁻¹ *ᵥ
        fun i : Fin (D.sp.Y 0).rank => (C.map (tauE D τ)) i j) := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (Formalism.L2.SG.EvalTIota.Pi _), Matrix.mul_nonsing_inv _ hP,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    congr 1
    funext i
    have e := congrFun (congrFun hC i) b
    simp only [Matrix.mul_apply] at e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact e.trans (Finset.sum_congr rfl fun j _ => mul_comm _ _)
  refine (congrArg (fun w => Formalism.L2.SG.EvalTIota.uM' (Formalism.IndefR.RationalEmbedding.iota D k) (Formalism.L2.Host.tauPl D τ) *ᵥ w) (hrv b)).trans ?_
  exact main.trans (Finset.sum_congr rfl fun j _ => congrArg (fun w => M j b • w) (hrv j).symm)

theorem gramQ_isUnit (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : (∀ x y, (VS D).hT (wt x) (wt y) = (VS D).hT x y) ∧ (∀ a, wt (X.eX a) = D.sp.hypE a) ∧
      (∀ a, wt (X.fY a) = D.sp.hypF a) ∧ wt (X.zu u) = D.zmOf u) (v : InfinitePlace X.B.I.F) :
    IsUnit (Formalism.L2.SG.ColDict.gramQ X wt v).det := by
  obtain ⟨Q, Qi, G', hQQi, hQiQ, hQq, -, -, -, hG', hblk⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set φ := X.B.I.φ v with hφ
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hGdef
  have hgram : Formalism.L2.SG.ColDict.gramQ X wt v = G.map φ := by
    ext a b
    have h1 := congrFun (congrFun hblk (Sum.inl a)) (Sum.inl b)
    rw [Matrix.fromBlocks_apply₁₁] at h1
    rw [Matrix.map_apply, ← h1]
    simp only [Formalism.L2.SG.ColDict.gramQ, Matrix.of_apply, Formalism.L2.SG.ColDict.rvV]
    have := PI.ScPiFrameW.hJ_rv X.B.I v (X.crd (Formalism.L2.SG.ColDict.qFr wt a)) (X.crd (Formalism.L2.SG.ColDict.qFr wt b))
    refine this.trans ?_
    congr 1
    simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hQq, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdetG : G.det ≠ 0 := by
    have hJu : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det
    have hJinv : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJu
    have hR : Matrix.fromBlocks G 0 0 G' *
        (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ) = 1 := by
      rw [← hblk]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q Qi, hQQi, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJinv, Matrix.one_mul,
        ← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    have hd := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fromBlocks_zero₂₁] at hd
    exact left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hd)
  have hm : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
  rw [hgram, hm, isUnit_iff_ne_zero, map_ne_zero]
  exact hdetG

end GlobalTheory.Core.Mi.RealMat


open GlobalTheory.Core.Mi.RealMat in
theorem GlobalTheory.Core.Mi.sTil_toH_eq_infM : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (θ : InfFam D), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau), Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH a).1 : X.B.I.Ginf) τ = GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ := by
  intro D X h u ψ B F tr θ hθ hE hA a τ
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hdetQ := gramQ_isUnit X u tr.wt ⟨tr.wt_isom, tr.wt_e, tr.wt_f, tr.weight_z⟩ (X.pl.symm τ)
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hact := act_gen h X.ιE hE X.pl X.φ_eq (rank_eq X h) (embA B.d B.o a) τ (B.d.i₀ * B.o.iA) _
    (fun j => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast hn j))) hA (embA_cols_at B.d B.o a τ)
  have hlin : ∀ b, uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
      Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b) =
      ∑ i, GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ i b •
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt i) := by
    intro b
    refine (hact (Fin.cast hn.symm b)).trans ?_
    exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl
  have hM : (Matrix.of fun a' b => hJ (X.B.I.ε (X.pl.symm τ))
      (Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt a'))
      (uMat (((B.toH a).1 : X.B.I.Ginf) (X.pl.symm τ)) *ᵥ
        Formalism.L2.SG.ColDict.rvV X (X.pl.symm τ) (Formalism.L2.SG.ColDict.qFr tr.wt b))) =
      Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ) * GlobalTheory.AdForm.infM (Formalism.IndefR.Eqv.thetaC D) (D.sp.X 0) hn a τ := by
    ext a' b
    rw [Matrix.of_apply, hlin, Matrix.mul_apply]
    simp only [hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, Formalism.L2.SG.ColDict.gramQ,
      Matrix.of_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  show (Formalism.L2.SG.ColDict.gramQ X tr.wt (X.pl.symm τ))⁻¹ * _ = _
  rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelRealPartMatrixFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondModel_realPart_matrix_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (θ : InfFam D), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau), Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH a).1 : X.B.I.Ginf) τ = GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ := by
  first | exact @GlobalTheory.Core.Mi.sTil_toH_eq_infM | exact GlobalTheory.Core.Mi.sTil_toH_eq_infM | (intros; apply GlobalTheory.Core.Mi.sTil_toH_eq_infM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelImageRationalStabilizerPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelImageRationalStabilizerPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem toH_rat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (a : GA D (D.sp.X 0)), a ∈ GQ (D.sp.X 0) → ∃ γ : Gam X u, iotaI X u γ = (B.toH a).1 ∧ iotaF X u γ = (B.toH a).2 := by
  intro D X h u ψ B a ha
  have hrat : embA B.d B.o a ∈ GQ (D.sp.Y 0) := by
    have e : embA B.d B.o a = B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ ha (one_mem _))
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset → castGA e x ∈ I'.GFset := by
    intro I I' e x hx
    subst e
    exact hx
  have hr : iotaX X h (embA B.d B.o a) ∈ X.B.I.GFset :=
    k h.symm _ ((Formalism.IndefR.RationalEmbedding.iota_rat D _).1 hrat)
  have hH := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
  exact ⟨⟨iotaX X h (embA B.d B.o a), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩, rfl, rfl⟩

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelImageRationalStabilizerPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondModel_image_rational_stabilizerPoint : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (a : GA D (D.sp.X 0)), a ∈ GQ (D.sp.X 0) → ∃ γ : Gam X u, iotaI X u γ = (B.toH a).1 ∧ iotaF X u γ = (B.toH a).2 := by
  first | exact @GlobalTheory.Core.Mi.toH_rat | exact GlobalTheory.Core.Mi.toH_rat | (intros; apply GlobalTheory.Core.Mi.toH_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalRepLevelDecompositionFiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalRepLevelDecompositionFiniteUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem exists_isDec_finM : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (g : GA D (D.sp.X 0)), ∃ p, GlobalTheory.AdForm.IsDec F.cls0.lev F.cls0.y (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p :=
  fun D _ F g => GlobalTheory.AdForm.Model.exists_dec (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) F.cls0.lev F.cls0.y F.cls0.y_bij.2 g

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalRepLevelDecompositionFiniteUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalRepLevelDecomposition_finiteUnitary : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (g : GA D (D.sp.X 0)), ∃ p, GlobalTheory.AdForm.IsDec F.cls0.lev F.cls0.y (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p := by
  first | exact @GlobalTheory.Core.Mi.exists_isDec_finM | exact GlobalTheory.Core.Mi.exists_isDec_finM | (intros; apply GlobalTheory.Core.Mi.exists_isDec_finM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealRepresentationMovesRieszVectorFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealRepresentationMovesRieszVectorFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem piU_rieszJ : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (s : X.B.I.Ginf), s ∈ Hinf X u → ∀ z z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt s) z z' → X.piU u s (rieszJ tr z) = rieszJ tr z' := by
  intro D X u F tr s hs z z' hz
  have hrep := X.piU_rep u
  have hS := hinf_le_sinf X u s hs
  have hSi := hinf_le_sinf X u _ ((Hinf X u).inv_mem hs)
  refine ext_inner_left ℂ fun η => ?_
  have hη : X.piU u s (X.piU u s⁻¹ η) = η := by
    rw [← ContinuousLinearMap.mul_apply, ← hrep.2.1 _ hS _ hSi, mul_inv_cancel, hrep.1]
    rfl
  rw [← hη, hrep.2.2.1 s hS, inner_rieszJ, inner_rieszJ, tr.J_eqv s hs _ z' z hz]

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealRepresentationMovesRieszVectorFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realRepresentation_moves_rieszVector_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (s : X.B.I.Ginf), s ∈ Hinf X u → ∀ z z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt s) z z' → X.piU u s (rieszJ tr z) = rieszJ tr z' := by
  first | exact @GlobalTheory.Core.Mi.piU_rieszJ | exact GlobalTheory.Core.Mi.piU_rieszJ | (intros; apply GlobalTheory.Core.Mi.piU_rieszJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi


set_option maxHeartbeats 1000000 in
theorem colForm_of_dec {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u)
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0))
    (hθ : IsInfFam θ) (hE : IdE X) (hAd : B.Adapted tr.wt) (hH0 : IsTransportAdelicCorrection tr a₀)
    (hLM : Formalism.L2.SG.ColDict.LevelMatch X tr hK) (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0))
    (c : (D.mem u).C.cls 0) (γ : GL (Fin (D.R.N 0)) D.host.E) (κ : F.cls0.lev.U)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)))
    (hx : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1) :
    (F.cls0.lev.chi κ : ℂ) * GlobalTheory.AdForm.atFr (fun z => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z)
        (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) := by
  obtain ⟨aγ, hQ, hfγ, hiγ⟩ := GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace D θ hθ γ hγ
  obtain ⟨γ', hγ'1, hγ'2⟩ := GlobalTheory.T.secondModel_image_rational_stabilizerPoint D X h u ψ B aγ hQ
  have finv : ∀ (a : GA D (D.sp.X 0)) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)),
      Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1 →
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = Bm := by
    intro a Bm hB
    have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
      rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
          GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have iinv : ∀ (a : GA D (D.sp.X 0)) (τ : D.what₂.Tau) (Bm : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ),
      Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 →
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = Bm := by
    intro a τ Bm hB
    have h1 : GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ = 1 := by
      rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
    calc _ = (Bm * GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ) *
          GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ τ := by rw [hB, one_mul]
      _ = Bm := by rw [mul_assoc, h1, mul_one]
  have hfγi : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ =
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 := by
    apply finv
    rw [hfγ, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hh : ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    have : (tr.h0⁻¹).1.1 * tr.h0.1.1 = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    exact this
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ = (tr.h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hfa0i : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ = ((tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    finv _ _ (by rw [e0]; exact hh)
  have hiγi : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) aγ⁻¹ τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ := by
    intro τ
    apply iinv
    rw [hiγ τ]
    unfold Formalism.L2.Forms.atInf
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨r, hr⟩ : ∃ r, r = aγ⁻¹ * g * a₀⁻¹ := ⟨_, rfl⟩
  have hg : g * a₀⁻¹ = aγ * r := by rw [hr]; group
  have hκP : κ.1 ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((F.cls0.lev.U_eq κ.1).1 κ.2).1
  obtain ⟨yk, hyk⟩ : ∃ yk : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), yk = tr.h0 * ⟨κ.1, hκP⟩ * tr.h0⁻¹ := ⟨_, rfl⟩
  have hfr : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r =
      ((F.cls0.y c * tr.h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) * (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    rw [hr, unitaryAdelicPointFiniteMatrix_base_space_mul, unitaryAdelicPointFiniteMatrix_base_space_mul, hfγi, hx, hfa0i]
    have : (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ⁻¹).1 *
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (F.cls0.y c).1 * κ.1).1 *
        (tr.h0⁻¹).1.1 = (F.cls0.y c * tr.h0⁻¹).1.1 * yk.1.1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hyk]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_inv]
      group
    exact this
  have hir : ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ := by
    intro τ
    rw [hr, unitaryAdelicPointInfiniteMatrices_base_space_mul, unitaryAdelicPointInfiniteMatrices_base_space_mul, hiγi, unitaryAdelicPointInfiniteMatrices_eq_one_of_finite θ a₀⁻¹ (inv_mem hH0.1), mul_one]

  have hRfin := GlobalTheory.T.secondModel_finitePart_frameActionMatrix D X h u ψ B F tr hE hAd r
  have hreal := GlobalTheory.T.secondModel_realPart_matrix_frame D X h u ψ B F tr θ hθ hE hAd r
  obtain ⟨κ'', hκ''⟩ : ∃ κ'' : Hfin X u, κ'' = (tr.hc c)⁻¹ * (B.toH r).2 := ⟨_, rfl⟩
  have hmulκ : ((tr.hc c : Hfin X u) : X.B.I.Gf) * (κ'' : X.B.I.Gf) = ((B.toH r).2 : X.B.I.Gf) := by
    rw [hκ'', ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hRk : RepM X tr.wt tr.ιA (κ'' : X.B.I.Gf) (yk.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine RepM_cancel (tr.hc_rep c) ?_
    rw [hmulκ, ← hfr]
    exact hRfin
  have hRF : Formalism.L2.SG.ColDict.RepF X tr.wt tr.ιA (κ'' : X.B.I.Gf) yk := hRk
  have hconj : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) = κ.1 := by
    rw [hyk]
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  have hκU : ((tr.h0⁻¹ * yk * tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈ F.cls0.lev.U := hconj ▸ κ.2
  obtain ⟨hmemIff, hpsi⟩ := hLM.2 κ'' yk hRF
  have hmem : κ'' ∈ Ku X u hK := hmemIff.2 hκU
  have hpsiv := hpsi hmem hκU
  have hchi : ((F.cls0.lev.chi ⟨_, hκU⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi κ : ℂˣ) : ℂ) := by
    congr 2
    exact Subtype.ext hconj

  have hdet : ∀ τ, IsUnit (GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ((F.val0.eY y).2 τ)
    refine Matrix.isUnit_det_of_right_inverse (B := GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r⁻¹ τ) ?_
    rw [← unitaryAdelicPointInfiniteMatrices_base_space_mul, mul_inv_cancel, unitaryAdelicPointInfiniteMatrices_base_space_one]
  let z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) :=
    ⟨fun τ => GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) r τ * (F.val0.eY y).1 τ, hdet⟩
  have htr : Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt ((B.toH r).1 : X.B.I.Ginf)) (F.val0.eY y) z' := by
    intro τ
    show _ = _ * _
    rw [hreal τ]
  have hriesz := GlobalTheory.T.realRepresentation_moves_rieszVector_frame D X u F tr ((B.toH r).1 : X.B.I.Ginf) (B.toH r).1.2 (F.val0.eY y) z' htr

  have hlhs : GlobalTheory.AdForm.atFr (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w)
      (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hfun : (fun τ => Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g τ * (F.val0.eY y).1 τ) = z'.1 := by
      funext τ
      show _ = _ * _
      rw [hir τ]
    unfold GlobalTheory.AdForm.atFr
    rw [dite_eq_left (by rw [hfun]; exact z'.2)]
    congr 1
    exact Subtype.ext hfun
  refine Eq.trans (congrArg (fun t => ((F.cls0.lev.chi κ : ℂˣ) : ℂ) * t) hlhs) ?_

  have hT := T.2
  have hT1 := hT.1 (rieszJ tr (F.val0.eY y))
  have htoHaγ : B.toH aγ = (iotaI X u γ', iotaF X u γ') := Prod.ext hγ'1.symm hγ'2.symm
  have hdec : B.toH r = ((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'') := by
    ext
    · simp
    · simp [hκ'']
  have eR : B.colForm T.1 (rieszJ tr (F.val0.eY y)) (g * a₀⁻¹) =
      ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z' := by
    have hx1 : B.toH (g * a₀⁻¹) = (iotaI X u γ', iotaF X u γ') *
        (((1 : Hinf X u), tr.hc c) * ((B.toH r).1, (1 : Hfin X u)) * ((1 : Hinf X u), κ'')) :=
      (congrArg B.toH hg).trans ((toH_mul B aγ r).trans (congrArg₂ (· * ·) htoHaγ hdec))
    unfold SBes.colForm
    rewrite [hx1, hT1.1 γ', hT1.2 _ ⟨κ'', hmem⟩]
    have h3 := hT.2 (B.toH r).1 (rieszJ tr (F.val0.eY y)) ((1 : Hinf X u), tr.hc c)
    have h4 := Formalism.L2.SG.ColDict.inner_shP X u T.1 (tr.hc c) (rieszJ tr z')
    have h5 := inner_rieszJ tr z' (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c))
    have h6 := congrArg (fun v => T.1 v ((1 : Hinf X u), tr.hc c)) hriesz
    refine congrArg (fun t => ((psiK X u hK ⟨κ'', hmem⟩ : ℂˣ) : ℂ) * t) ?_
    exact h3.symm.trans (h6.trans (h4.symm.trans h5))
  refine Eq.trans ?_ eR.symm
  exact congrArg (fun t => t * tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) z') (hchi.symm.trans hpsiv.symm)

end GlobalTheory.Core.Mi

theorem GlobalTheory.Core.Mi.colDict_rd_eq_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0)), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → Formalism.L2.SG.ColDict.LevelMatch X tr hK → ∃ ξ : (D.mem u).C.Y 0 → X.Vpi u, Submodule.span ℂ (Set.range ξ) = ⊤ ∧ ∀ (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0)), (chart0 F).rd θ (Formalism.L2.SG.ColDict.colDictL X tr hK T) y g = B.colForm T.1 (ξ y) (g * a₀⁻¹) := by
  intro D X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM
  refine ⟨fun y => GlobalTheory.Core.Mi.rieszJ tr (F.val0.eY y), GlobalTheory.Core.Mi.span_rieszJ tr, ?_⟩
  intro T y g
  unfold GlobalTheory.AdForm.Chart.rd chart0 GlobalTheory.AdForm.rdS
  simp only
  have hd : ∃ p, GlobalTheory.AdForm.IsDec F.cls0.toChart.lev F.cls0.toChart.y
      (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) g) p := GlobalTheory.T.exists_rationalRepLevelDecomposition_finiteUnitary D u F g
  rw [dite_eq_left hd]
  have hfe : (fun z => Formalism.L2.SG.ColDict.colDictL X tr hK T (id hd.choose.1) (F.val0.eY.symm z)) =
      (fun w => tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc hd.choose.1)) w) :=
    funext (GlobalTheory.Core.Mi.colDictL_eY_symm tr hK T hd.choose.1)
  rw [hfe]
  exact GlobalTheory.Core.Mi.colForm_of_dec X h u ψ B F tr hK θ a₀ hθ hE hAd hH0 hLM T y g hd.choose.1 hd.choose.2.1 hd.choose.2.2
    hd.choose_spec.1 hd.choose_spec.2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DictionaryColumnScalarFormEqTraceColumnFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (θ : InfFam D) (a₀ : GA D (D.sp.X 0)), IsInfFam θ → GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → Formalism.L2.SG.ColDict.LevelMatch X tr hK → ∃ ξ : (D.mem u).C.Y 0 → X.Vpi u, Submodule.span ℂ (Set.range ξ) = ⊤ ∧ ∀ (T : Cu X u hK) (y : (D.mem u).C.Y 0) (g : GA D (D.sp.X 0)), (chart0 F).rd θ (Formalism.L2.SG.ColDict.colDictL X tr hK T) y g = B.colForm T.1 (ξ y) (g * a₀⁻¹) := by
  first | exact @GlobalTheory.Core.Mi.colDict_rd_eq_colForm | exact GlobalTheory.Core.Mi.colDict_rd_eq_colForm | (intros; apply GlobalTheory.Core.Mi.colDict_rd_eq_colForm <;> assumption)
end
