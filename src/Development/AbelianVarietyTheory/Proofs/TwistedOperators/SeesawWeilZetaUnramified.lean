module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointEqUnipotentFrameChangeCosetRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaUnramified
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaDer

theorem schr_comp_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  have hh : ⅟(2 : R) + ⅟(2 : R) = 1 := by rw [← two_mul, mul_invOf_self]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, add_assoc]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * hh

theorem exists_equiv {A : Type} [CommRing A] {m k d : ℕ} {G H : Matrix (Fin m) (Fin m) A} (hHG : H * G = 1)
    (hGH : G * H = 1) (e : Fin k ≃ Fin d) :
    ∃ T : Matrix (Fin m) (Fin k) A ≃+ Matrix (Fin d) (Fin m) A,
      (∀ u, T u = uᵀ.submatrix e.symm id * G) ∧ ∀ x, T.symm x = ((x * H)ᵀ).submatrix id e := by
  refine ⟨{ toFun := fun u => uᵀ.submatrix e.symm id * G
            invFun := fun x => ((x * H)ᵀ).submatrix id e
            left_inv := fun u => ?_
            right_inv := fun x => ?_
            map_add' := fun u v => ?_ }, fun u => rfl, fun x => rfl⟩
  · ext i j
    simp [Matrix.mul_assoc, hGH]
  · simp [Matrix.transpose_submatrix, Matrix.submatrix_submatrix, Matrix.mul_assoc, hHG]
  · simp [Matrix.transpose_add, Matrix.submatrix_add, Matrix.add_mul]

private theorem rho_add_twisted_operators {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ) (p q : W)
    (Φ : (κ → R) → ℂ) (z : κ → R) :
    co.rho ψ (p + q) Φ z = ψ (-(⅟(2 : R) * B p q)) * co.rho ψ p (co.rho ψ q Φ) z := by
  simp only [GlobalTheory.WeilM.Darboux.rho]
  rw [schr_comp_apply, ← co.form, map_add (f := _), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

set_option maxHeartbeats 6400000 in
private theorem tendsto_add_smul_punctured_of_differentiableAt {D : D7} {n d m : ℕ} (u₀ : Matrix (Fin n) (Fin d) (AE D)) (e' : Fin d ≃ Fin m)
    (G : Matrix (Fin n) (Fin n) (AE D)) :
    Continuous fun t : ℝ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e'.symm id * G := by
  have c0 : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F) := GlobalTheory.ThetaLineDeriv.continuous_realAd
  have c1 : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀ := c0.smul continuous_const
  exact (c1.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const

private theorem fin_realAd_smul_eq_zero {D : D7} (t : ℝ) (a : AE D) :
    finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • a) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) = 0 := by
    show finPart D ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    have hs : sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 := rfl
    simp only [Formalism.L2.Theta.finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, hs,
      TensorProduct.zero_tmul]
  rw [h0, zero_mul]


set_option maxHeartbeats 1600000 in
theorem thO_pure_deriv {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hVJ : Vs.J = -S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : ∀ i j, D.sp.cm.sig (Vs.J j i) = Vs.J i j)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ)
    (u₀ : Matrix (Fin S.rank) (Fin d) (AE D)) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (hact : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u₀) g g₁)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ L : ℝ →+ WO S X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
      GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) =
        fun x => deriv (fun t : ℝ => heisO Bs.ψ S X (L t)
          (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) 0 := by
  classical
  have hTR : NumberField.IsTotallyReal D.host.F := hBs.cm.1
  have hCh : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hdet : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (gram_det_ne S)
  have hinc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
    simp
  have hinc' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨T, hT, hTs⟩ := exists_equiv (A := AE D) hinc' hinc e
  have hpt : ∀ x, GlobalTheory.TripleRead.ptO S.gram e x = T.symm x := fun x => (hTs x).symm
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F v} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA g φ hφ hstd
  have hΦ' := GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ hstd
  have hd : ∀ z, HasDerivAt (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ z) 0 :=
    fun z => hact _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd) z

  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram)ᵀ := by
    ext i j
    have h1 := hV j i
    rw [hVJ] at h1
    simp only [Matrix.neg_apply, map_neg, neg_inj] at h1
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR, h1]
  have h2 : (⅟(2 : AF D.host.F)) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [show (2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  have hphase : ∀ (x : WO S X) (q : Matrix (Fin S.rank) (Fin d) (AE D)),
      symplOH S X x (T q) = ⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x) q := by
    intro x q
    conv_lhs => rw [← T.apply_symm_apply x]
    have hh := GlobalTheory.SquareAgree.hTens_transpose_mul (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) hinc' hG (T.symm x) q
    rw [← hT, ← hT] at hh
    have hs := GlobalTheory.WeilSchrodinger.symp_eq_symplO D S X (X.gramᵀ) (D.host.xi0 • S.gram⁻¹) 1 rfl (by rw [one_smul])
      (T (T.symm x)) (T q)
    simp only [symplOH, ← hs, h2, GlobalTheory.WeilM.symp, one_mul, neg_one_mul, map_neg]
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hVJ]
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • Matrix.reindex e.symm e.symm (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hJW, Matrix.reindex_apply, map_mul]
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
    have e4 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [e4, e3, hh, e1, e2, map_neg]

  let ln : ℝ →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
    AddMonoidHom.mk' (fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (fun s t => by simp only [GlobalTheory.ThetaLineDeriv.realAd_add, add_smul])
  refine ⟨T.toAddMonoidHom.comp ln, ?_, ?_, ?_⟩
  · have hfun : (fun t => (T.toAddMonoidHom.comp ln) t) =
        fun t => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram :=
      funext fun t => hT _
    show Continuous fun t => (T.toAddMonoidHom.comp ln) t
    rw [hfun]
    exact tendsto_add_smul_punctured_of_differentiableAt u₀ e _
  · intro t
    show (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)).map (finPart D) = 0
    rw [hT, Matrix.map_mul]
    have hz : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id).map (finPart D) = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, fin_realAd_smul_eq_zero,
        Matrix.zero_apply]
    rw [hz, Matrix.zero_mul]
  · funext x
    have hfun : (fun t : ℝ => heisO Bs.ψ S X ((T.toAddMonoidHom.comp ln) t)
        (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) =
        fun t => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ (T.symm x)
          (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := by
      funext t
      show heisO Bs.ψ S X (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)) _ x = _
      simp only [heisO, GlobalTheory.TripleRead.thO, hpt, map_add (f := _), T.symm_apply_apply]
      rw [show M.co.rho Bs.ψ (T.symm x + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) =
        fun z => Bs.ψ (-(⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀))) *
          M.co.rho Bs.ψ (T.symm x) (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) z
        from funext (rho_add_twisted_operators M.co Bs.ψ _ _ _)]
      simp only [GlobalTheory.WeilM.thetaSum]
      rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul, hphase, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
    have hder := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr Bs.ψ hTR hCh (M.co.e u₀) hΦ hΦ' (by
      simpa only [GlobalTheory.WeilM.Darboux.rho, map_smul] using hd) (M.co.e (T.symm x))
    rw [hfun]
    simp only [GlobalTheory.WeilM.Darboux.rho, map_smul]
    rw [hder.deriv]
    simp only [GlobalTheory.TripleRead.thO, hpt, GlobalTheory.WeilM.Darboux.rho]

end GlobalTheory.ThetaDer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentUnitDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.SplitCharValue

theorem values_of_rel (D : D7) (z : ℂ) (K : ℕ) (b : D.host.Eˣ) (m : D.what₂.Tau → ℤ) (hK : 0 < K)
    (h : z ^ K * ∏ τ, (tauE D τ (b : D.host.E) / (‖tauE D τ (b : D.host.E)‖ : ℂ)) ^ m τ = 1) :
    Mod1All z ∧ ∀ (q : ℕ) [Fact q.Prime], (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E (b : D.host.E) = 1) → GlobalTheory.MovedKappaEx.UnitAt q z := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hz, H⟩ := GlobalTheory.HeckeVal.root_value (tauE D) m b z K hK h
  refine ⟨⟨hz, fun σ => H ℂ σ fun τ => ?_⟩, fun q hq hb lam => ?_⟩
  · have := IsCMField.complexEmbedding_complexConj D.host.E (σ.comp τ) (b : D.host.E)
    simp only [RingHom.comp_apply] at this
    rw [this, Complex.norm_conj]
  · obtain ⟨M, hM, i1⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)
      fun P hP => (hb P hP).le
    obtain ⟨M', hM', i2⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)⁻¹
      fun P hP => by rw [map_inv₀, hb P hP, inv_one]
    have key : ∀ ψ : D.host.E →+* ℂ_[q], ‖ψ (b : D.host.E)‖ = 1 := fun ψ => by
      have j1 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM i1
      have j2 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM' i2
      rw [map_inv₀, norm_inv] at j2
      have h0 : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero _).2 b.ne_zero)
      exact le_antisymm j1 ((inv_le_one₀ h0).1 j2)
    rw [Formalism.MainNotions.TaylorLogMetric.lamC, dite_eq_left hz]
    refine H _ lam fun τ => ?_
    exact (key (lam.comp τ)).trans
      (key ((lam.comp τ).comp (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E))).symm

theorem inf_val (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) : ∃ m : D.what₂.Tau → ℤ, ∀ (k : D.host.Eˣ) (x : (Formalism.L2.Theta.AE D)ˣ),
      Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) →
      ((c x : Circle) : ℂ) = ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ m τ := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : InfFam D, IsInfFam θ := GlobalTheory.DualPairCompare.exists_infFam D
  have H : ∀ τ, ∃ m : ℤ, ∀ x : (Formalism.L2.Theta.AE D)ˣ, Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      (∀ τ', τ' ≠ τ → θ τ' (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) = 1) →
        ((c x : Circle) : ℂ) = (θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) / (‖θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D))‖ : ℂ)) ^ m := fun τ => by
    obtain ⟨a, m, -, -, h⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ c n τ hθ hc hr
    exact ⟨m, h θ hθ⟩
  choose m hm using H
  refine ⟨m, fun k x hx1 hx2 => ?_⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  let z : D.what₂.Tau → ℂˣ := fun τ => Units.map (tauE D τ).toMonoidHom k
  let f : ∀ _ : D.what₂.Tau, ℂ →* Formalism.L2.Theta.AE D := fun τ => e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have hθk : ∀ τ, θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E))) = tauE D τ k := fun τ => (hθ τ).1 k
  have ex : x = ∏ τ, Units.map (f τ) (z τ) := by
    apply Units.ext
    rw [Units.coe_prod]
    have e3 : (∏ τ, ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) = e (fun τ => tauE D τ k) := by
      change ∏ τ, e (Pi.mulSingle τ (tauE D τ k)) = _
      rw [← map_prod, Finset.univ_prod_mulSingle]
    rw [e3]
    exact GlobalTheory.SplitCharExp.ext_of_chart h (hx1.trans (e1 _).symm) fun τ => by rw [hx2, hθk, e2]
  rw [ex, map_prod]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
  have f2 : ∀ τ', θ τ' (Formalism.L2.Theta.infPart D ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) =
      (Pi.mulSingle τ (tauE D τ k) : D.what₂.Tau → ℂ) τ' := fun τ' => e2 _ τ'
  have := hm τ (Units.map (f τ) (z τ)) (e1 _) fun τ' ht => by rw [f2, Pi.mulSingle_eq_of_ne ht]
  rw [f2, Pi.mulSingle_eq_same] at this
  exact this

def finIso (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E)

theorem finIso_one_tmul (D : D7) (x : D.host.E) : finIso D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := GlobalTheory.Mem.Col2.afIso_tmul_one _ _ x

theorem mem_intAE_iff (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (finIso D y P) ≤ 1 :=
  (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (GlobalTheory.Mem.Col2.mem_rInt_iff _ _ _)


set_option maxHeartbeats 800000 in
theorem exists_pow_rel (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = 1) :
    ∃ (h : ℕ) (k : D.host.Eˣ) (y w : (Formalism.L2.Theta.AE D)ˣ), 0 < h ∧ Formalism.L2.Pj.FinUnit w ∧ Formalism.L2.Theta.finPart D (y : Formalism.L2.Theta.AE D) = 1 ∧
      Formalism.L2.Theta.infPart D (y : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) ∧
      x ^ h * y = w * Units.map (Formalism.L2.Theta.incA D).toMonoidHom k ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), finIso D (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) P = 1 →
        P.valuation D.host.E (k : D.host.E) = 1 := by
  obtain ⟨Φ, -, -, h1, -, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (finIso D) (finIso_one_tmul D) (mem_intAE_iff D)
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs1 : ∀ z : Formalism.L2.Theta.AE D, (s z).1 = Formalism.L2.Theta.infPart D z := fun z => (hs z).1
  have hs2 : ∀ z : Formalism.L2.Theta.AE D, (s z).2 = Formalism.L2.Theta.finPart D z := fun z => (hs z).2
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup D.host.E
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔
    (Neutral.B1.diagUnits D.host.E).range).pow_index_mem (Units.map Φ.toRingHom.toMonoidHom x))
  generalize hh : (GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔ (Neutral.B1.diagUnits D.host.E).range).index = h at e
  have h0 : 0 < h := hh ▸ Nat.pos_of_ne_zero hfi.index_ne_zero
  let Ψ : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΨ : ∀ a, Φ ((Ψ a : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = a := fun a => Φ.apply_symm_apply _
  let K : (Formalism.L2.Theta.AE D)ˣ := Units.map (Formalism.L2.Theta.incA D).toMonoidHom k
  have e' : Ψ u * K = x ^ h := by
    have a1 : Ψ (Neutral.B1.diagUnits D.host.E k) = K := Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    have a2 : Ψ (Units.map Φ.toRingHom.toMonoidHom x) = x := Units.ext (Φ.symm_apply_apply _)
    rw [← a1, ← map_mul, e, map_pow, a2]
  let g : Formalism.L2.Theta.AE D →* Formalism.L2.Theta.AE D := s.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ (Af D.host.F ⊗[D.host.F] D.host.E)).comp (Formalism.L2.Theta.infPart D).toMonoidHom)
  have g1 : ∀ a, Formalism.L2.Theta.infPart D (g a) = Formalism.L2.Theta.infPart D a := fun a =>
    (hs1 _).symm.trans (congrArg Prod.fst (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have g2 : ∀ a, Formalism.L2.Theta.finPart D (g a) = 1 := fun a =>
    (hs2 _).symm.trans (congrArg Prod.snd (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have hint : ∀ a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E, ∀ b : (Formalism.L2.Theta.AE D)ˣ,
      Formalism.L2.Theta.finPart D ((Ψ a * Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := fun a ha b => by
    have : Formalism.L2.Theta.finPart D ((Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = 1 := g2 _
    rw [Units.val_mul, RingHom.map_mul, this, mul_one, mem_intAE_iff, ← (h3 _).2, hΨ]
    exact fun P => (ha P).le
  refine ⟨h, k, Units.map g K, Ψ u * Units.map g K, h0, ⟨?_, hint u hu K, ?_⟩, g2 _, g1 _, ?_, fun P hP => ?_⟩
  · have a1 : Formalism.L2.Theta.infPart D ((Units.map g K : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (K : Formalism.L2.Theta.AE D) := g1 _
    rw [Units.val_mul, RingHom.map_mul, a1, ← RingHom.map_mul, ← Units.val_mul, e', Units.val_pow_eq_pow_val,
      RingHom.map_pow, hx, one_pow]
  · rw [mul_inv, ← Ψ.map_inv u, ← (Units.map g).map_inv K]
    exact hint u⁻¹ ((GlobalTheory.Mem.Chr.unitIdl D.host.E).inv_mem hu) K⁻¹
  · rw [← e', mul_right_comm]
  · have a1 : (u : AdeleRing (𝓞 D.host.E) D.host.E).2 P * algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) =
        ((Φ (x : Formalism.L2.Theta.AE D)).2 P) ^ h :=
      congrArg (fun a : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ => (a : AdeleRing (𝓞 D.host.E) D.host.E).2 P) e
    rw [(h3 _).2, hP, one_pow] at a1
    have a2 := congrArg (Valued.v : Valuation (P.adicCompletion D.host.E) _) a1
    rw [map_mul, hu P, one_mul, map_one] at a2
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : D.host.E)).symm.trans a2

theorem finIso_idem (D : D7) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {q : ℕ} (hq : GlobalTheory.MovedKappaEx.OffPrime e q)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : finIso D (Formalism.L2.Theta.finPart D e) P = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h4⟩ := he
  have hv := hq v ε hε h4
  obtain ⟨α, rfl, -, hα⟩ := hε
  have hne : P.under (𝓞 D.host.F) ≠ v := by
    rintro rfl
    apply hv
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal
    rwa [map_natCast]
  have h5 : finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0 := by
    rw [h4]
    refine (GlobalTheory.SplitProj.afIso_one_tmul_apply α P).trans ?_
    have : α (P.under (𝓞 D.host.F)) = 0 := hα _ hne
    rw [GlobalTheory.AdeleBaseChange.adMap_apply, this, map_zero]
  have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, RingEquiv.map_mul]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0
  rw [h5, mul_zero]

theorem char_split_value (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e) (x₀ : (Formalism.L2.Theta.AE D)ˣ)
    (a : Formalism.L2.Theta.AE D) (hx : (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e)) :
    Mod1All ((c x₀ : Circle) : ℂ) ∧ ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((c x₀ : Circle) : ℂ) := by
  obtain ⟨m, hm⟩ := inf_val D c n hc hr
  obtain ⟨-, -, -, M, hM, hMu⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1
  have hinf : Formalism.L2.Theta.infPart D (x₀ : Formalism.L2.Theta.AE D) = 1 := by
    rw [hx, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one,
      GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, sub_zero, zero_add]
  obtain ⟨h, k, y, w, hh, hw, hy1, hy2, e1, hk⟩ := exists_pow_rel D x₀ hinf
  have e2 : c x₀ ^ (h * M) * c y ^ M = 1 := by
    rw [pow_mul, ← mul_pow, ← map_pow, ← map_mul, e1, map_mul, hc.2 k, mul_one, hMu w hw]
  have e3 : ((c x₀ : Circle) : ℂ) ^ (h * M) *
      ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ (m τ * M) = 1 := by
    simp only [zpow_mul, zpow_natCast]
    rw [Finset.prod_pow, ← hm k y hy1 hy2, ← Circle.coe_pow, ← Circle.coe_pow, ← Circle.coe_mul, e2, Circle.coe_one]
  obtain ⟨h1, h2⟩ := values_of_rel D _ (h * M) k (fun τ => m τ * M) (Nat.mul_pos hh hM) e3
  refine ⟨h1, fun q _ hq => h2 q fun P hP => hk P ?_⟩
  rw [hx, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one, RingEquiv.map_add (e := _), RingEquiv.map_sub,
    RingEquiv.map_mul, RingEquiv.map_one]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D a) P + (1 - finIso D (Formalism.L2.Theta.finPart D e) P) = 1
  rw [finIso_idem D he hq P hP, zero_mul, sub_zero, zero_add]

theorem offPrime_conj {D : D7} {e : Formalism.L2.Theta.AE D} {q : ℕ} (h : GlobalTheory.MovedKappaEx.OffPrime e q) :
    GlobalTheory.MovedKappaEx.OffPrime (cA D e) q := fun v ε hv hε =>
  h v ε hv (by rw [← hε, GlobalTheory.MovedIdem.cA_cA, add_comm])

theorem defPair_inRange {T : Type} {m : ℕ} {p : Pair T} (h : DefPair m p) : p.InRange m := by
  cases p <;> simp only [DefPair, Pair.InRange, Pair.big, Node.InRange] at h ⊢ <;> omega

end GlobalTheory.SplitCharValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeKernelCosetFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeKernelCosetFramedPoint
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option autoImplicit false

namespace GlobalTheory.HeckeExist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] GlobalTheory.HeckeEx.fieldCAt GlobalTheory.HeckeEx.algClosedCAt

theorem spMap_epsMul_one {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) : spMap (epsMul (1 : ℂ)) ≫ v = v := by
  have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
    apply RingHom.ext
    intro a
    ext <;> simp [epsMul]
  rw [e0]
  have : spMap (RingHom.id (DualNumber ℂ)) = 𝟙 _ := by
    first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
  rw [this, Category.id_comp]


set_option maxHeartbeats 1000000 in
theorem similitude_tri_of_hkIsog {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U)
    (P : Ideal (𝓞 E)) (p m : ℕ) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p) (k k' : U.Comp) (x : (U.X k).dom)
    (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ))
    (t : Ix Dw → (CAt σ)ˣ) (hK : Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p m C)
    (ψ : pullback Xo.univ.t.G.hom (U.un k x).x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk (U.un k x).x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G))
    (hI : IsHkIsog p (U.un k x).x z.x C ψ ψp)
    (hL : ∀ τ j, IsLieImageH p ψ ((U.un k x).u τ j) (z.u τ j)) (hB : FrBor t (U.un k' x') z) :
    ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ),
      (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) =
        (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧
      (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧
      (∀ τ, ∀ n < Dw.mult τ, ∀ v : (U.X k).Λ, perFr (U.X k') x'.1 (gam v : Fin r → E) (relab c σ τ) n =
        p * ∑ j ∈ Finset.range (Dw.mult τ), A τ n j * perFr (U.X k) x.1 (v : Fin r → E) (relab c σ τ) j) ∧
      ∀ τ (n : Fin (Dw.mult τ)), A τ n n = toC (t (some ⟨τ, n⟩) : CAt σ) := by
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨Pm, hPm, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨Pm', hPm', per', hPx', hv', -⟩ := hpt k' x'
  have hpp : p.Prime := hP.2.2.2.1
  have hC : ∀ a ∈ C, a ^ p ^ 2 = 1 := fun a ha => GlobalTheory.HkPts.pow_eq_one hP.2.2.2.2 hK ha
  obtain ⟨gam, h, hiso, hh, honto, hder⟩ := GlobalTheory.HeckeEx.exists_lift_deriv F (ik k) (ik k') Pm Pm' per per' hpp hPx
    (hB.1.trans hPx') C ψ ψp hC hI
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hcol : ∀ τ n, h.toLinearMap (Pi.single (e.symm ⟨τ, n⟩) 1) =
      (∑ j, ((p : ℂ) * toC (cf τ n j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ n
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL τ n
    have d2 := hder (Pi.single (e.symm ⟨τ, n⟩) 1) wv hw2 (by have q := hv τ n; rw [← hw1] at q; exact q)
    have d1 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' per' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ n)
      (z.u τ n)).1 (hPx' ▸ hcf3 τ n)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ n = wv ≫ ψ ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (GlobalTheory.HeckeEx.spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0]
      exact spMap_epsMul_one _
    rw [e3] at d3
    have tn := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' per'
    show h (Pi.single (e.symm ⟨τ, n⟩) 1) = _
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (smul_smul (p : ℂ) (toC (cf τ n j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))
  refine ⟨(φ k').toLinearMap ∘ₗ gam ∘ₗ (φ k).symm.toLinearMap,
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun w => ?_, fun τ i j hji => ?_,
    fun τ n hn v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
    push_cast
    ring
  · obtain ⟨a, ha⟩ := honto ((φ k').symm w)
    refine ⟨φ k a, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [ha, map_nsmul, LinearEquiv.apply_symm_apply]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have a1 := hPm' (gam v) (e.symm ⟨τ, ⟨n, hn⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range, Finset.mul_sum]
    refine (GlobalTheory.LevelCusp.apply_of_cols e h.toLinearMap
      (fun τ i j => (p : ℂ) * toC (cf τ i j)) hcol (Pm v) τ ⟨n, hn⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hPm, Equiv.apply_symm_apply, dite_eq_left ⟨hn, j.2⟩, _root_.mul_assoc]
  · beta_reduce
    rw [dite_eq_left ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.HeckeExist

namespace GlobalTheory.HeckeExist

attribute [local instance] GlobalTheory.HeckeEx.fieldCAt GlobalTheory.HeckeEx.algClosedCAt

theorem isHeckePrime_of {D : D7} {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh) (P : Formalism.L2.DIV.Pl D.host.E) (p : ℕ)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) (hp : p.Prime) (hpP : (p : 𝓞 D.host.E) ∈ P.asIdeal)
    (hM : ¬ p ∣ l.M') : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P.asIdeal p := by
  refine GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, ?_, hp, hpP, hM⟩
  have hQ : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Hh.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    rw [Ideal.map]
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, e⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.coe_injective
      show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = (r : D.host.E)
      rw [Hh.bar_eq]
      exact e.symm
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = _
      rw [Hh.bar_eq]
      rfl
  rw [← hQ]
  have hmax : (P.asIdeal.map (Hh.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal :=
    Ideal.map_isMaximal_of_equiv Hh.bar
  rw [← hQ] at hmax
  by_contra hne
  have hle : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≤ P.asIdeal :=
    le_sup_right.trans ((P.isMaximal.eq_of_le hne le_sup_left).symm.le)
  exact hc (hmax.eq_of_le P.isMaximal.ne_top hle)

theorem exists_coset_frBor_of_hkKer : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∃ a ∈ Rc, ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLv hG hFam hMod hTh hTie i σ hσ hV hPin P p k α Rc hS h hx C
  obtain ⟨-, hTot, hFun, -⟩ := id hHk
  have hL := hTie.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ' : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  have hU : IsUnf (T.U ((i : ℕ) + 1) σ) := hL.unf _ hj σ hσ'
  obtain ⟨hSp, hp, hpP, hM, -, -, -⟩ := id hS
  have hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p := isHeckePrime_of T.Q.l P p hSp.1 hp hpP hM
  obtain ⟨z₀, hz₀⟩ := hTot D.host.E T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) _ C
  obtain ⟨k', x', t', hB⟩ := hU.2.2.1 z₀
  obtain ⟨ψ, ψp, hI, hLie, -⟩ := id hz₀
  obtain ⟨gam, A', h1, h2, h3, h4, h5⟩ := similitude_tri_of_hkIsog _ hU P.asIdeal p k hP _ k' _ x' C.1 z₀ t' C.2 ψ ψp hI hLie hB
  obtain ⟨a, ha, hx', t, ht, hB'⟩ := GlobalTheory.T.hecke_point_eq_unipotent_frame_change_coset_rep D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLv hG hFam hMod hTh hTie i σ hσ hV hPin P p k α Rc
    hS h hx C z₀ hz₀ k' x' t' hB gam A' h1 h2 h3 h4 h5
  refine ⟨a, ha, fun z hz => ?_⟩
  have e := hFun D.host.E T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) _ C z₀ z hz₀ hz
  have e2 := (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id T.Q.c.F (CAt σ)) z₀).1 _ _ e
    (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id T.Q.c.F (CAt σ)) z₀).2.1
  subst e2
  exact ⟨hx', t, ht, hB'⟩

end GlobalTheory.HeckeExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeKernelCosetFramedPointStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernel_coset_framedPoint : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∃ a ∈ Rc, ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  first | exact @GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer | exact GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer | (intros; apply GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer <;> assumption)
end
end
end
