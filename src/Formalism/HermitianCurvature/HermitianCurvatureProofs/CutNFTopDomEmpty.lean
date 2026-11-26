module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomEmpty
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section mul

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nfMulOp (c : B.Mat k r → ℂ) : B.DiffOp k r Wp Wq :=
  [{ coef := fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
     coefAdj := fun g => star (c g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
     word := []
     word_lie := by simp
     adj_id := by
       intro x A B'
       unfold B.hsInner
       simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.id_apply]
       rw [TBBx2.Tri.hsVec_smul, TBBx2.Tri.hsVec_smul, inner_smul_right, inner_smul_left]
       simp }]

theorem nfMulOp_apply (c : B.Mat k r → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (nfMulOp (Wp := Wp) (Wq := Wq) c) F g = c g • F g := by
  unfold B.opApply nfMulOp B.Rw
  simp

theorem nfMulOp_poly {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) :
    CutMP.PolyOp 0 κ (nfMulOp (Wp := Wp) (Wq := Wq) c) := by
  unfold CutMP.PolyOp
  intro Tm hTm
  simp only [nfMulOp, List.mem_singleton] at hTm
  subst hTm
  exact ⟨le_refl _, c, hc, fun g => rfl, fun g => rfl⟩

end mul

theorem nf_isPolyDeg_one {N : ℕ} : U.IsPolyDeg (N := N) 0 (fun _ => (1 : ℂ)) := by
  unfold U.IsPolyDeg
  exact ⟨1, by simp, fun g => by simp⟩

theorem nf_isPolyDeg_pow {N κ : ℕ} {c : Matrix (Fin N) (Fin N) ℂ → ℂ} (hc : U.IsPolyDeg κ c) (e : ℕ) :
    U.IsPolyDeg (κ * e) (fun g => c g ^ e) := by
  unfold U.IsPolyDeg at hc ⊢
  obtain ⟨q, hq, hcq⟩ := hc
  refine ⟨q ^ e, ?_, fun g => ?_⟩
  · calc (q ^ e).totalDegree ≤ e * q.totalDegree := MvPolynomial.totalDegree_pow q e
      _ ≤ e * κ := Nat.mul_le_mul_left e hq
      _ = κ * e := Nat.mul_comm e κ
  · simp only [hcq g, map_pow]

theorem empty_operator_list_holds : NFEmptyOps := by
  refine ⟨2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p N
  have hn : (1 : ℝ) ≤ CutMP.nDim P.k P.r := by unfold CutMP.nDim; push_cast; linarith
  have ok : ∀ (κ : ℕ) (c : B.Mat P.k P.r → ℂ), U.IsPolyDeg κ c → (κ : ℝ) ≤ 2 * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) →
      (∀ pp : B.SS P.k P.r, p.T.base.inSS pp → ∀ g, c (B.sgs pp g) = c g) → NFOpOK 2 p N (nfMulOp c) := by
    intro κ c hc hκ hinv
    obtain ⟨hs, hg, ho⟩ := CutMP.polynomial_decay_admissible P.k P.r Wp Wq 0 κ (nfMulOp c) (nfMulOp_poly hc)
    refine ⟨hs _, ?_, hg _ hκ, ?_⟩
    · intro pp hpp f _ g _
      have hfun : B.opApply (nfMulOp (Wp := Wp) (Wq := Wq) c) f = fun g => c g • f g := funext (nfMulOp_apply c f)
      rw [nfMulOp_apply, hfun]
      unfold B.rho
      show _ = (p.T.base.π (Matrix.of pp.1.1)).comp ((c (B.sgs pp g) • f (B.sgs pp g)).comp (p.T.base.π' (Matrix.of pp.2.1)⁻¹))
      rw [hinv pp hpp g, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    · have : (B.opOrder (nfMulOp (Wp := Wp) (Wq := Wq) c) : ℝ) ≤ 0 := by exact_mod_cast ho
      have : (0 : ℝ) ≤ 2 * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
      linarith
  refine ⟨nfMulOp (fun _ => (1 : ℂ)), nfMulOp (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ)),
    ok 0 _ nf_isPolyDeg_one (by push_cast; positivity) (fun _ _ _ => rfl), ok ((2 * P.r + 2) * N) _ ?_ ?_ ?_, fun F g => ?_⟩
  · have h := nf_isPolyDeg_pow (Formalism.FourierDecayAlt.P.gram_function_polynomial P.k P.r p.T.base.z p.T.base.z') N
    refine ⟨h.choose, h.choose_spec.1, fun g => ?_⟩
    rw [← h.choose_spec.2 g]; push_cast; rfl
  · push_cast
    have h1 : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul h1 hn (by norm_num) (by positivity)]
  · intro pp hpp g
    rw [TBBx2.Gf_sgs p.T.base pp hpp g]
  · rw [nfMulOp_apply, nfMulOp_apply, one_smul]
    exact ⟨rfl, rfl⟩

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeas
namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

def TypeComm : Prop :=
  ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)) (z e : Fin (2 * P.r + P.k + 1) → ℂ) (TP : Top.TypeProj P π z e),
    IsCRepOn (UWset P.k P.r z) π → ContinuousOn π (UWset P.k P.r z) →
    (∀ h ∈ UWset P.k P.r z, ∀ v, ‖π h v‖ = ‖v‖) →
    1 ≤ P.k → inWb P.k P.r z → 0 < Tz P.k P.r z → inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 →
    herm (Hpk P.k P.r) e e = 1 →
    ∀ g ∈ UWset P.k P.r z, ∀ l : ℂ, g *ᵥ e = l • e → ∀ ρ, (TP.E ρ).comp (π g) = (π g).comp (TP.E ρ)

def HouseMeas : Prop :=
  ∀ (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ), inWb k r z → (herm (Hpk k r) z z).re < 0 →
    inWb k r e → herm (Hpk k r) e z = 0 → herm (Hpk k r) e e = 1 →
    ∃ h : (Fin (2 * r + k + 1) → ℂ) → B.Mat k r, Measurable h ∧ (∀ u, h u ∈ UWset k r z) ∧
      ∀ u, inWb k r u → herm (Hpk k r) u z = 0 → u ≠ 0 → ∃ l : ℂ, h u *ᵥ u = l • e

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def trJKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P fun q =>
    ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq p.T.base q.1)))

def IsFrameKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

end kb

def NFBddPtw : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∃ C : ℝ, ∀ (u : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT),
      ∑ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤ C * ∑ ρ, ‖MA.evQ P (u ρ) q‖ ^ 2

def NFTrNormKB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameKB p e → ∃ C : ℝ, ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT), q.1 = ((fun l => c l.castSucc), c (Fin.last P.r)) →
      D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
        C * (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomVMul
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem vector_multiplication_holds : NFVMul := by
  intro Wp Wq _ _ _ _ _ _ P p φ F γ _hγ hG
  by_cases hc : ((φ (TBB.Gp p γ) : ℝ) : ℂ) = 0
  · rw [hc, zero_smul]
    unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · have hae : ∀ᵐ q ∂p.T.base.μSS,
          D.orbIntegrand p.T.base h2.choose
            (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) q =
          (1 : ℂ) • D.orbIntegrand p.T.base h2.choose (fun _ => (0 : Wq →L[ℂ] Wp)) q := by
        filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
        have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
          rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
          rfl
        unfold D.orbIntegrand B.rho
        simp [hGq, hc]
      rw [TBBx4.orbJ_smul_ae _ _ _ _ _ _ one_ne_zero hae, one_smul]
      have h0 := TBBx4.orbJ_smul_ae p.T.base h2.choose
        (D.muR p.T.base h2.choose (h1.1.2 ▸ D.ptPerm γ)) (fun _ => (0 : Wq →L[ℂ] Wp))
        (fun _ => (0 : Wq →L[ℂ] Wp)) (2 : ℂ) two_ne_zero
        (ae_of_all _ fun q => by unfold D.orbIntegrand B.rho; simp)
      rw [two_smul] at h0
      simpa using h0
    · simp
    · simp
  · unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · apply TBBx4.orbJ_smul_ae _ _ _ _ _ _ hc
      filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
      have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
        rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
        rfl
      unfold D.orbIntegrand B.rho
      simp only [hGq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [smul_comm]
    · simp
    · simp

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure ShiftAtR {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) where
  up : ℕ → ℝ
  up' : ℕ → ℝ
  um : ℕ → ℝ
  um' : ℕ → ℝ
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  pp : KB.Pl (shP P up up') Wp Wqp
  pm : KB.Pl (shP P um um') Wp Wqm
  Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)
  Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)
  ApPt : C.LPt → (Wqp →L[ℂ] Wq)
  AmPt : C.LPt → (Wqm →L[ℂ] Wq)
  hzp : pp.T.base.z = p.T.base.z
  hzp' : pp.T.base.z' = p.T.base.z'
  hzm : pm.T.base.z = p.T.base.z
  hzm' : pm.T.base.z' = p.T.base.z'
  polyP : PolyOp (n₀ * (P.r + 1)) Ap
  polyM : PolyOp (n₀ * (P.r + 1)) Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAtR.iNp ShiftAtR.iIp ShiftAtR.iFp ShiftAtR.iNm ShiftAtR.iIm ShiftAtR.iFm

section pieces

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

def SwapTie (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') : Prop :=
  q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧
    q.T.base.μW = p.T.base.μW ∧ q.T.base.μN = p.T.base.μN ∧ q.T.base.μW' = p.T.base.μW' ∧
    q.ν' = p.ν' ∧ q.m₀ = p.m₀


open Classical in
def ptRep (p : KB.Pl P Wp Wq) (γ : C.LPt) : B.Mat P.k P.r :=
  if h : ∃ g ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g then h.choose else 1

end pieces

def WigEquiv {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, A (n * g * n') = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h ∈ UWset k r z, A (h * g) = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h' ∈ UWset k r z', A (g * h') = (π' h'⁻¹).comp ((A g).comp (π'' h')))

def WigUpper {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (n₀ : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, ‖A g‖ ^ 2 ≤ (Gf k r z z' g / Tz k r z') ^ n₀

def WigLower {k r : ℕ} {Wq Wqp Wqm : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
    [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
    (z z' : Fin (2 * r + k + 1) → ℂ) (b : ℝ) (n₀ : ℕ)
    (Ap : B.Mat k r → (Wqp →L[ℂ] Wq)) (Am : B.Mat k r → (Wqm →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ v : Wq,
    ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tz k r z' / Gf k r z z' g) ^ n₀ *
      (‖(ContinuousLinearMap.adjoint (Ap g)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (Am g)) v‖ ^ 2)

def CellIdSh : Prop :=
  ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq')
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ),
    SwapTie p q → WigEquiv p.T.base.z p.T.base.z' p.T.base.π' q.T.base.π' A →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
    ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (A (ptRep p γ))

theorem ptRep_spec {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {γ : C.LPt} (hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ) :
    ptRep p γ ∈ B.GV P.k P.r ∧ Gf P.k P.r p.T.base.z p.T.base.z' (ptRep p γ) = Gp p γ := by
  have hex : ∃ g ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g :=
    Formalism.FourierDecayAlt.P.Dx2.dFrameExists P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ p.hF hγ hG
  have hrep : ptRep p γ = hex.choose := by
    unfold ptRep
    rw [dite_eq_left hex]
  obtain ⟨hmem, hz, _⟩ := hex.choose_spec
  refine ⟨by rw [hrep]; exact hmem, ?_⟩
  rw [hrep, Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ γ hz]
  rfl

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtwAsm
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

lemma nf_norm_sum_sq_le {E : Type*} [SeminormedAddCommGroup E] {n : ℕ} (x : Fin n → E) :
    ‖∑ i, x i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  have h1 : ‖∑ i, x i‖ ≤ ∑ i, ‖x i‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun i => ‖x i‖)
  calc ‖∑ i, x i‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa using h2

lemma nf_globCoef_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {Θ : B.DiffOp k r Wp Wq} {d d' : ℝ}
    (h : CutMP.GlobCoef Θ d) (hd : d ≤ d') : CutMP.GlobCoef Θ d' := by
  intro Tm hTm
  obtain ⟨h1, h2, h3⟩ := h Tm hTm
  refine ⟨h1, h2, fun m => ?_⟩
  obtain ⟨Cb, hCb⟩ := h3 m
  refine ⟨max Cb 0, fun u w hu hw hl g hg => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hp : B.gN g ^ d ≤ B.gN g ^ d' := Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hp0 : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (by linarith) _
  obtain ⟨a1, a2⟩ := hCb u w hu hw hl g hg
  constructor
  · calc _ ≤ Cb * B.gN g ^ d := a1
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ d' := mul_le_mul_of_nonneg_left hp (le_max_right _ _)
  · calc _ ≤ Cb * B.gN g ^ d := a2
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ d' := mul_le_mul_of_nonneg_left hp (le_max_right _ _)

lemma nfOpOK_mono {C C' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {N : ℕ} {Th : B.DiffOp P.k P.r Wp Wq} (h : NFOpOK C p N Th) (hC : C ≤ C') :
    NFOpOK C' p N Th := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hn : 0 ≤ CutMP.nDim P.k P.r := by unfold CutMP.nDim; positivity
  refine ⟨h1, h2, nf_globCoef_mono h3 ?_, le_trans h4 ?_⟩
  · have : 0 ≤ ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
    have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) =
        x * (((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) := fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hC this
  · have : 0 ≤ CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
    have e : ∀ x : ℝ, x * CutMP.nDim P.k P.r * ((N : ℝ) + 1) = x * (CutMP.nDim P.k P.r * ((N : ℝ) + 1)) :=
      fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hC this

lemma nf_empty_bound (hV : NFVMul) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ N : ℕ) (hNp : N ≤ 2 * p₀) (χ : ℝ → ℝ) (K : ℝ)
    (Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq)
    (hap : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g)
    (ε : ℝ) (c : Fin (P.r + 1) → ℂ) (hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1))
    (hG : 0 < TBB.Gp p (TBB.bigPt P.r c)) (hK : |χ (TBB.Gp p (TBB.bigPt P.r c) / ε)| ≤ K) :
    ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) [] c‖ ≤
      K ^ 2 * ∑ t : Fin 2, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (B.opApply (![Th₀, Th₁] t) f) (P.r + 1) [] (TBB.bigPt P.r c) := by
  set γ := TBB.bigPt P.r c with hγ
  have hH : D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      fun g => (((fun y => χ (y / ε) * y ^ p₀) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • f g := by
    funext g
    simp only [D.cutF, TBBx4.fpm, ContinuousLinearMap.comp_id, smul_smul, Complex.ofReal_mul, Complex.ofReal_pow]
  have h0 : B.opApply Th₀ f = f := funext fun g => (hap f g).1
  have h1 : B.opApply Th₁ f = fun g => (((fun y : ℝ => y ^ N) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • f g :=
    funext fun g => (hap f g).2
  show ‖TBB.Ew p (fun _ => 1) _ (P.r + 1) [] γ‖ ≤ _
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hH, h0, h1, TBBx2.Tri.Ew_top p _ hl, TBBx2.Tri.Ew_top p _ hl, TBBx2.Tri.Ew_top p _ hl,
    hV Wp Wq P p (fun y => χ (y / ε) * y ^ p₀) f γ hl hG, hV Wp Wq P p (fun y : ℝ => y ^ N) f γ hl hG, TBBx4.hsVec_real_smul_sq, TBBx4.hsVec_real_smul_sq]
  set G := TBB.Gp p γ
  set S := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ)
  set v := ‖B.hsVec (p.V f γ)‖ ^ 2
  set x := χ (G / ε)
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hv : 0 ≤ v := sq_nonneg _
  have hG0 : 0 ≤ G := hG.le
  have hx2 : x ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hK 2
  have hGa : G ^ (2 * p₀) = G ^ (2 * p₀ - N) * G ^ N := by rw [← pow_add, Nat.sub_add_cancel hNp]
  have hGN : G ^ N ≤ 1 + (G ^ N) ^ 2 := by nlinarith [sq_nonneg (G ^ N - 1), pow_nonneg hG0 N]
  have hLHS : 0 ≤ S * ((x * G ^ p₀) ^ 2 * v) := by positivity
  rw [Real.norm_of_nonneg hLHS, Real.norm_of_nonneg hG0]
  have e1 : S * ((x * G ^ p₀) ^ 2 * v) = (S * v * G ^ (2 * p₀ - N)) * (x ^ 2 * G ^ N) := by
    rw [mul_pow, ← pow_mul, mul_comm p₀ 2, hGa]; ring
  have e2 : K ^ 2 * (G ^ (2 * p₀ - N) * (S * v) + G ^ (2 * p₀ - N) * (S * ((G ^ N) ^ 2 * v))) =
      (S * v * G ^ (2 * p₀ - N)) * (K ^ 2 * (1 + (G ^ N) ^ 2)) := by ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul hx2 hGN (pow_nonneg hG0 N) (sq_nonneg K)

lemma nf_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {n : ℕ} (E : Wp →L[ℂ] Wp) (a : Fin n → ℂ) (W : Fin n → (Wq →L[ℂ] Wp)) :
    E.comp (∑ q, a q • W q) = ∑ q, a q • E.comp (W q) := by
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

lemma nf_block {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ} (E : Wp →L[ℂ] Wp) (a : Fin n → ℝ) (Kt : ℝ)
    (ha : ∀ q, |a q| ≤ Kt) (W : Fin n → (Wq →L[ℂ] Wp)) (d : ℝ) :
    d ^ 2 * ‖B.hsVec (E.comp (∑ q, ((a q : ℝ) : ℂ) • W q))‖ ^ 2 ≤
      (n : ℝ) * Kt ^ 2 * ∑ q, d ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
  rw [nf_comp_sum, TBBx2.Tri.hsVec_sum]
  simp only [TBBx2.Tri.hsVec_smul]
  have h1 := nf_norm_sum_sq_le (fun q => ((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q)))
  have h2 : ∀ q, ‖((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2 ≤ Kt ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
    intro q
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have : |a q| ^ 2 ≤ Kt ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (ha q) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h3 : ∑ q, ‖((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2 ≤ Kt ^ 2 * ∑ q, ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun q _ => h2 q
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc d ^ 2 * ‖∑ q, ((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2
      ≤ d ^ 2 * ((n : ℝ) * (Kt ^ 2 * ∑ q, ‖B.hsVec (E.comp (W q))‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h3 hn)) (sq_nonneg d)
    _ = (n : ℝ) * Kt ^ 2 * ∑ q, d ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqNF
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem fpmSh_eq_fpm (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (p₀ : ℕ) :
    fpmSh q f A p₀ = TBBx4.fpm q (fun g => (f g).comp (A g)) (fun _ => ContinuousLinearMap.id ℂ Wq') p₀ := by
  first
  | rfl
  | (unfold fpmSh; rfl)
  | unfold fpmSh

theorem inCC_compSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} {A₀ : ℝ} {d : ℕ} (hf : ∀ m : ℕ, B.InCC A₀ m f) (hA : PolyOp d A) :
    ∀ m : ℕ, B.InCC (A₀ - d) m (fun g => (f g).comp (A g)) := by
  intro m
  have h := shifted_decay P Wp Wq Wq' u u' q f A A₀ d 0 hf hA m
  simp only [mul_zero, Nat.cast_zero, sub_zero] at h
  first
  | exact h
  | (convert h using 2; rw [fpmSh_eq_fpm]; simp [TBBx4.fpm])
  | (convert h using 2; rw [fpmSh_eq_fpm]; unfold TBBx4.fpm)

end sh




end

end Formalism.FourierDecayAlt.P.CutBPEq
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCutSup
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Filter Topology

noncomputable section

theorem xD_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    xD (fun y => φ (y / ε)) = fun x => xD φ (x / ε) := by
  funext x
  simp only [xD]
  have h : (fun y => φ (y / ε)) = fun y => φ (ε⁻¹ * y) := by
    funext y
    rw [div_eq_inv_mul]
  rw [h, deriv_comp_mul_left, smul_eq_mul, div_eq_inv_mul]
  ring

theorem xD_iter_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    xD^[q] (fun y => φ (y / ε)) = fun x => (xD^[q] φ) (x / ε) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih, xD_dil _ hε]
    funext x
    rw [Function.iterate_succ_apply']

theorem xD_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD φ) := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  exact contDiff_id.mul hd

theorem xD_iter_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (q : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] φ) := by
  induction q with
  | zero => simpa using hφ
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact xD_contDiff ih

theorem xD_zero_of_const {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ) (hφ : ∀ y ∈ U, φ y = c) :
    ∀ y ∈ U, xD φ y = 0 := by
  intro y hy
  have h : φ =ᶠ[nhds y] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hy) hφ
  show y * deriv φ y = 0
  rw [h.deriv_eq]
  simp

private theorem xD_iterate_eq_ite_of_const_on_open {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ)
    (hφ : ∀ y ∈ U, φ y = c) : ∀ q : ℕ, ∀ y ∈ U, (xD^[q] φ) y = if q = 0 then c else 0 := by
  intro q
  induction q with
  | zero => intro y hy; simpa using hφ y hy
  | succ q ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    simp only [Nat.succ_ne_zero, if_false]
    exact xD_zero_of_const hU _ ih y hy

theorem truncated_supremum_bound_holds : NFCutSup := by
  unfold NFCutSup
  intro χ hχ q
  obtain ⟨hs, -, h1⟩ := hχ
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] χ) := xD_iter_contDiff hs q
  obtain ⟨K0, hK0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  refine ⟨max K0 1, fun ε hε x hx => ?_⟩
  rw [xD_iter_dil χ hε q]
  show |(xD^[q] χ) (x / ε)| ≤ max K0 1
  have hy : 0 < x / ε := div_pos hx hε
  rcases le_or_gt (x / ε) 1 with hy1 | hy1
  · have hb := hK0 (x / ε) ⟨hy.le, hy1⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left _ _)
  · rw [xD_iterate_eq_ite_of_const_on_open isOpen_Ioi 1 (fun z hz => h1 z (le_of_lt hz)) q (x / ε) hy1]
    refine le_trans ?_ (le_max_right _ _)
    split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutBP
end
