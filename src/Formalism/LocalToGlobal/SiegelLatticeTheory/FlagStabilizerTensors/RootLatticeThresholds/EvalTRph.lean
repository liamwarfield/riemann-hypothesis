module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPinG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MemPerpMapFlag
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsFinal
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaLUniq

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.ProjRows
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTRph

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem isFdeg_dv (v : InfinitePlace X.B.I.F) :
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.dv v) := by
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (X.B.lam v) (X.B.σ v) (X.ds v)
  have hw : X.B.w v ≠ 0 := by
    intro h0
    have h1 := (X.low v).1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have e : X.dv v = d := Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegOf_eq hd hw
  rw [e]
  exact hd

theorem inner_tens_orbit (g : X.B.I.Ginf) :
    ⟪X.B.tens X.B.w, X.B.σs g (X.B.tens X.B.w)⟫_ℂ = mInf X.B.I X.B.σ X.B.w g := by
  rw [Formalism.L2.SG.Pf.orbit_eq X.B.I X.B.σ X.B.σs X.B.tens X.B.tens_spec X.B.w g, X.B.tens_spec.1]
  rfl

theorem inner_tens_self : ⟪X.B.tens X.B.w, X.B.tens X.B.w⟫_ℂ = 1 := by
  rw [X.B.tens_spec.1]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [inner_self_eq_norm_sq_to_K, (X.low v).1]
  simp

theorem integral_ph_m
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v))) :
    Integrable (fun g => X.ph g * mInf X.B.I X.B.σ X.B.w g) (muInf X.B.I) ∧
      ∫ g, X.ph g * mInf X.B.I X.B.σ X.B.w g ∂(muInf X.B.I) = 1 := by
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hs := Formalism.L2.SG.Pf.glob_schur X.B.I X.B.σ X.dv X.B.w hU (isFdeg_dv X) hw hL X.B.σs X.B.tens
    X.B.tens_spec (X.B.tens X.B.w)
  simp_rw [inner_tens_orbit X] at hs
  rw [inner_tens_self X] at hs
  exact hs

theorem rph_isRowProj
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v))) :
    IsRowProj (fun g => X.B.R (g, 1)) (mInf X.B.I X.B.σ X.B.w) X.Rph :=
  Formalism.L2.SG.Closed.ProjRowsR_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.H X.B.σ X.dv X.B.w
    (fun v => (X.ds v).2.2.1) (isFdeg_dv X) (fun v => (X.low v).1) hL X.Rph X.Rph_spec

theorem rph_fix_of_coef
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)))
    (f : X.B.I.L2 X.B.μf X.B.fund)
    (hc : ∀ g : X.B.I.Ginf, ⟪f, X.B.R (g, 1) f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) * mInf X.B.I X.B.σ X.B.w g) :
    X.Rph f = f := by
  have hP := rph_isRowProj X hL
  have h1 : ⟪f, X.Rph f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [X.Rph_spec f f]
    have e : ∀ g, Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w
        (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) g * ⟪f, X.B.R (g, 1) f⟫_ℂ =
        ((‖f‖ ^ 2 : ℝ) : ℂ) * (X.ph g * mInf X.B.I X.B.σ X.B.w g) := by
      intro g
      rw [hc g]
      show X.ph g * _ = _
      ring
    simp_rw [e]
    rw [integral_const_mul, (integral_ph_m X hL).2, mul_one]
  have h2 : ⟪X.Rph f, X.Rph f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ := by
    rw [hP.1 f (X.Rph f)]
    congr 1
    exact congrArg (fun L : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund => L f) hP.2.1
  have h3 : ⟪X.Rph f, f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ := hP.1 f f
  have h0 : ⟪f - X.Rph f, f - X.Rph f⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, h2, h3, h1, inner_self_eq_norm_sq_to_K]
    simp
  exact (sub_eq_zero.1 (inner_self_eq_zero.1 h0)).symm

end Formalism.L2.SG.EvalTRph

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish
open Matrix

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

theorem rk1_smul_right (v : V) (b : ℂ) (B : V' ≃ₗᵢ[ℂ] V') (w : V') :
    rk1 v (b • B w) = conj b • (rk1 v w).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V') := by
  ext ξ
  rw [_root_.smul_apply, ContinuousLinearMap.comp_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply,
    Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_left, LinearIsometryEquiv.inner_map_eq_flip, smul_smul]
  rfl

variable {G : Type*} [Group G] [MeasurableSpace G]

theorem OO_right [CompleteSpace V] (μ : Measure G) (Ω : Set G) (Ph : G → V) (Ph' : G → V') (γ t : G) (b : ℂ)
    (B : V' ≃ₗᵢ[ℂ] V') (hB : ∀ x, Ph' (t⁻¹ * x) = b • B (Ph' x)) :
    OO μ Ω Ph Ph' (γ * t) = conj b • (OO μ Ω Ph Ph' γ).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V') := by
  have hx : ∀ x, rk1 (Ph x) (Ph' ((γ * t)⁻¹ * x)) =
      conj b • (ContinuousLinearEquiv.arrowCongr B.toContinuousLinearEquiv
        (ContinuousLinearEquiv.refl ℂ V)) (rk1 (Ph x) (Ph' (γ⁻¹ * x))) := by
    intro x
    rw [_root_.mul_inv_rev, mul_assoc, hB, rk1_smul_right]
    rfl
  unfold Formalism.L2.SG.TermOp.OO
  simp_rw [hx]
  rw [integral_smul, ContinuousLinearEquiv.integral_comp_comm]
  rfl

theorem OO_empty [CompleteSpace V] (μ : Measure G) (Ph : G → V) (Ph' : G → V') (γ : G) :
    OO μ ∅ Ph Ph' γ = 0 := by
  unfold Formalism.L2.SG.TermOp.OO
  simp

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']

theorem norm_hsEmb_sq' (A : V' →L[ℂ] V) : ‖Formalism.L2.SG.PackageTie.hsEmb A‖ ^ 2 = Formalism.L2.SG.RealObj.hs2 A := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem norm_hsEmb_right (A : V' →L[ℂ] V) (b : ℂ) (hb : ‖b‖ = 1) (B : V' ≃ₗᵢ[ℂ] V') :
    ‖Formalism.L2.SG.PackageTie.hsEmb (b • A.comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))‖ =
      ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
  rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_hsEmb_sq', norm_hsEmb_sq',
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_smul, hb, one_pow, one_mul]
  exact Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_right A B.symm

theorem norm_hsEmb_smul (A : V' →L[ℂ] V) (b : ℂ) (hb : ‖b‖ = 1) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (b • A)‖ = ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
  rw [map_smul, norm_smul, hb, one_mul]

end Gen

section Amp

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem ratLink_congr {x : X.B.I.GA} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x a) (e : a = b) :
    RatLink X x b := by
  subst e
  exact h

theorem roset_congr {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ₁ Λ₂ Λ₁' Λ₂' : Submodule (𝓞 D.host.E) (VS D).V}
    {γ₁ γ₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h1 : Λ₁ = Λ₂) (h2 : Λ₁' = Λ₂') (h3 : γ₁ = γ₂) :
    ROset X F0 F0' Λ₁ Λ₁' γ₁ = ROset X F0 F0' Λ₂ Λ₂' γ₂ := by
  subst h1 h2 h3
  rfl

theorem isSFund_congr {S S' Ω : Set X.B.I.Ginf} (h : S = S') (hS : IsSFund X.B.I S Ω) : IsSFund X.B.I S' Ω := by
  subst h
  exact hS

theorem roset_c {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hA : IsAutLam (VS D) Λ' c)
    (hfix : ∀ a, c (F0'.fvec a) = F0'.fvec a) :
    ROset X F0 F0' Λ Λ' (γ * c) = ROset X F0 F0' Λ Λ' γ := by
  have hF : ∀ a, frame (lf D F0') a = c (frame (lf D F0') a) := fun a => by
    rw [frame_lf, hfix a]
  have hF' : ∀ a, frame (lf D F0') a = c⁻¹ (frame (lf D F0') a) := fun a => by
    rw [frame_lf, inv_fix F0' hfix a]
  have hA' : IsAutLam (VS D) Λ' c⁻¹ := ⟨inv_mem hA.1, gmap_inv_of hA.2⟩
  ext y
  simp only [Formalism.L2.SG.TermOp.ROset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, n, hx, rfl, hn, hn'⟩
    refine ⟨x, n, hx, rfl, hn, ?_⟩
    have := Formalism.L2.SG.Pf.nlam_conj hA hF hn'
    convert this using 1
    group
  · rintro ⟨x, n, hx, rfl, hn, hn'⟩
    refine ⟨x, n, hx, rfl, hn, ?_⟩
    have := Formalism.L2.SG.Pf.nlam_conj hA' hF' hn'
    convert this using 1
    group

theorem sinf_of_fix {x : X.B.I.GA} {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x c)
    (hfix : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) : x.1 ∈ X.SinfU u' := by
  obtain ⟨M, -, hM1, -, hM3⟩ := hx
  have hce : ∀ a, c (X.eX a) = X.eX a := fun a => by
    have := hfix (Fin.castSucc a)
    rwa [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, X.Fu_e] at this
  have hcz : c (X.zu u') = X.zu u' := by
    have := hfix (Fin.last _)
    rwa [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, X.flagZVector] at this
  have hfixM : ∀ y, c y = y →
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y = X.crd y := fun y hy => by
    rw [← hM3, hy]
  intro v
  have key : ∀ w, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ w = w →
      (uMat (x.1 v) - 1) *ᵥ rv X.B.I v w = 0 := by
    intro w hw
    have hP : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)
    have hφ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *ᵥ
        (fun i => X.B.I.φ v (w i)) = fun i => X.B.I.φ v (w i) := by
      funext i
      have hi := RingHom.map_mulVec (X.B.I.φ v) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) w i
      rw [hw] at hi
      exact hi.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hM1 v, Formalism.L2.SG.HidaSetting.rv, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one, ← Matrix.mulVec_mulVec, hφ, sub_self]
  refine ⟨fun a => ?_, ?_⟩
  · rw [key (X.eR a) (hfixM _ (hce a))]
    exact zero_mem _
  · rw [key (X.zR u') (hfixM _ hcz)]
    exact zero_mem _

theorem norm_chiN (κ : X.B.I.Gf) : ‖chiN X κ‖ = 1 := by
  exact Formalism.L2.SG.TermOp.KExpCut.psiUnit X _

set_option maxHeartbeats 1000000 in
private theorem exists_isSFund_ROinf_of_toTerm_eq (hR : RatPt) {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm)
    (hs : ∃ Ω, IsSFund X.B.I (ROinf s) Ω) : ∃ Ω, IsSFund X.B.I (ROinf s') Ω := by
  obtain ⟨c, hcI, hcg, hcfix, n, hn, ν, hν, hlin⟩ := fib_c h
  obtain ⟨hl, -⟩ := fib_dec h
  have hl' := lam'_eq h
  obtain ⟨xn, hxn⟩ := hR D X n (nlam_isom hn)
  obtain ⟨Ω, hΩ⟩ := hs
  have e1 : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν) := by
    have hr := roset_c (X := X) (F0 := X.Fu u) (Λ := s.lam) (n * s.lin * ν) ⟨hcI, hcg⟩ hcfix
    rw [← hlin] at hr
    exact (roset_congr (F0 := X.Fu u) (F0' := X.Fu u') (γ₁ := s'.lin) hl.symm hl'.symm rfl).trans hr
  have hS : ∀ σ, σ ∈ ROinf s' ↔ xn.1⁻¹ * σ * xn.1 ∈ ROinf s := by
    intro σ
    rw [e1]
    have hc := Formalism.L2.SG.TermOp.Vanish.roset_conj (X := X) (γ := s.lin) hn hν hxn (xn.1⁻¹ * σ * xn.1)
    have hsimp : xn.1 * (xn.1⁻¹ * σ * xn.1) * xn.1⁻¹ = σ := by group
    rw [hsimp] at hc
    exact hc.symm
  exact ⟨_, Formalism.L2.SG.TermOp.Vanish.isSF_image_mul xn.1 hS hΩ⟩

private theorem norm_hsEmb_OOt_eq_of_toTerm_eq (hR : RatPt) (hC : ChiTrivialC) {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm)
    (hs : ∃ Ω, IsSFund X.B.I (ROinf s) Ω) (hs' : ∃ Ω, IsSFund X.B.I (ROinf s') Ω) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s')‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s)‖ := by
  obtain ⟨c, hcI, hcg, hcfix, n, hn, ν, hν, hlin⟩ := fib_c h
  obtain ⟨hl, -⟩ := fib_dec h
  have hl' := lam'_eq h
  obtain ⟨xn, hxn⟩ := hR D X n (nlam_isom hn)
  obtain ⟨xν, hxν⟩ := hR D X ν (nlam_isom hν)
  obtain ⟨xc, hxc⟩ := hR D X c hcI
  have hl2 : RatLink X (xn * s.rep.1.1 * xν * xc) s'.lin := by
    rw [hlin]
    exact Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X)
      (Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X)
        (Formalism.L2.SG.TermOp.Vanish.ratLink_mul (X := X) hxn s.rep.2.1) hxν) hxc
  have hpt : s'.pt = xn * s.rep.1.1 * xν * xc :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_unique (X := X) s'.rep.2.1 hl2
  have hsinv : xc.1⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (sinf_of_fix hxc hcfix)
  have hΩp : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.rep.1.2) (FundOf s) := by
    unfold Formalism.L2.SG.TermOp.FundOf
    rw [dite_eq_left hs]
    exact hs.choose_spec
  have e1 : ROinf s' = ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.lin * ν) := by
    have hr := roset_c (X := X) (F0 := X.Fu u) (Λ := s.lam) (n * s.lin * ν) ⟨hcI, hcg⟩ hcfix
    rw [← hlin] at hr
    exact (roset_congr (F0 := X.Fu u) (F0' := X.Fu u') (γ₁ := s'.lin) hl.symm hl'.symm rfl).trans hr
  have hΩq : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') s.lam s.lam' (n * s.rep.1.2 * ν)) (FundOf s') := by
    have h2 : IsSFund X.B.I (ROinf s') (FundOf s') := by
      unfold Formalism.L2.SG.TermOp.FundOf
      rw [dite_eq_left hs']
      exact hs'.choose_spec
    exact isSFund_congr e1 h2
  have key := Formalism.L2.SG.TermOp.Vanish.oo_rel Formalism.L2.SG.Pf.nLamNinf_holds hC Y s.mem s.mem' s.rep
    hn hν hxn hxν hΩp hΩq
  have hOO : OOt s' = conj (X.psiInfU u' xc.1⁻¹) •
      ((X.psiInfU u xn.1 * X.psiInfU u' xν.1) • OOt s).comp
        ((Formalism.L2.SG.RealObj.InfCut.piIso X u' xc.1⁻¹ hsinv).symm.toContinuousLinearEquiv :
          X.Vpi u' →L[ℂ] X.Vpi u') := by
    have := FiniteDimensional.complete ℂ (X.Vpi u)
    show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf s') (X.Wu u) (X.Wu u') s'.pt.1 = _
    rw [hpt, Prod.fst_mul, OO_right _ _ _ _ _ xc.1 _ _ (fun x => by
      rw [Formalism.L2.SG.RealObj.InfCut.piIso_apply]
      exact (X.Wu_spec u').1 _ hsinv x), key]
    rfl
  have hb : ‖conj (X.psiInfU u' xc.1⁻¹)‖ = 1 :=
    (Complex.norm_conj _).trans (Formalism.L2.SG.TermOp.Vanish.psiInfU_norm X u' _)
  have hk : ‖X.psiInfU u xn.1 * X.psiInfU u' xν.1‖ = 1 := by
    rw [norm_mul, Formalism.L2.SG.TermOp.Vanish.psiInfU_norm, Formalism.L2.SG.TermOp.Vanish.psiInfU_norm, one_mul]
  rw [hOO, norm_hsEmb_right _ _ hb, norm_hsEmb_smul _ _ hk]

theorem oot_norm (hR : RatPt) (hC : ChiTrivialC) {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s')‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (OOt s)‖ := by
  by_cases hs : ∃ Ω, IsSFund X.B.I (ROinf s) Ω
  · exact norm_hsEmb_OOt_eq_of_toTerm_eq hR hC h hs (exists_isSFund_ROinf_of_toTerm_eq hR h hs)
  · by_cases hs' : ∃ Ω, IsSFund X.B.I (ROinf s') Ω
    · exact absurd (exists_isSFund_ROinf_of_toTerm_eq hR h.symm hs') hs
    · have e : ∀ t : Formalism.L2.SG.PackageTie2.TT Y u u', ¬ (∃ Ω, IsSFund X.B.I (ROinf t) Ω) → OOt t = 0 := fun t ht => by
        have := FiniteDimensional.complete ℂ (X.Vpi u)
        show OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u') t.pt.1 = 0
        unfold Formalism.L2.SG.TermOp.FundOf
        rw [dite_eq_right ht]
        exact OO_empty _ _ _ _
      rw [e s hs, e s' hs']

theorem ampFibreConst_of (hR : RatPt) (hC : ChiTrivialC) (Y : Full X) : Formalism.L2.SG.LoopTieOf.AmpFibreConst Y := by
  unfold Formalism.L2.SG.LoopTieOf.AmpFibreConst
  intro u u' t s s'
  simp only [Formalism.L2.SG.LoopTieOf.ampL, Formalism.L2.SG.TermOp.ampN, map_smul, norm_smul, norm_chiN, one_mul]
  rw [oot_norm hR hC (s'.2.trans s.2.symm)]

end Amp

end Formalism.L2.SG.Pf.FibreCounting
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NeatTies
noncomputable section
open scoped Classical InnerProductSpace ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf

section FinXN

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} (Y : Full X)

theorem sharp_bij_of_neat (u : D.what₂.Word) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Function.Bijective (sharp Y.hK (Y.cs u)) := by
  have hst : Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u Y.hK) := hN
  let cls : (Y.cs u).Cl → Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) :=
    fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)
  have hcls : Function.Bijective cls := by
    refine ⟨fun ρ ρ' h => ?_, fun c => ?_⟩
    · obtain ⟨a, ⟨γ, rfl⟩, κ, hκ, hab⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
      obtain ⟨ρ0, _, huniq⟩ := Y.colReps u ((Y.cs u).h ρ')
      have h1 := huniq ρ ⟨γ, ⟨κ, hκ⟩, hab⟩
      have h2 := huniq ρ' ⟨1, 1, by simp⟩
      exact h1.trans h2.symm
    · induction c using Quotient.inductionOn' with
      | h g =>
        obtain ⟨ρ, ⟨γ, κ, hg⟩, _⟩ := Y.colReps u g
        refine ⟨ρ, ?_⟩
        show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ g
        rw [DoubleCoset.eq]
        exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hg⟩
  let ec := Equiv.ofBijective cls hcls
  let s : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Hfin X u := fun c => (Y.cs u).h (ec.symm c)
  have hs : ∀ c, DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (s c) = c := fun c => ec.apply_symm_apply c
  obtain ⟨e, he⟩ := Formalism.L2.SG.ColsDim.columns_decomposition (Gam X u) (Hinf X u) (Hfin X u) ℂ (X.Vpi u) (iotaI X u)
    (iotaF X u) (Ku X u Y.hK) (psiK X u Y.hK) (piRep X u) s hs hst
  have key : ∀ T ρ, (sharp Y.hK (Y.cs u) T) ρ =
      (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (e T (cls ρ))) := by
    intro T ρ
    have hsρ : s (cls ρ) = (Y.cs u).h ρ := by
      show (Y.cs u).h (ec.symm (ec ρ)) = _
      rw [ec.symm_apply_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm
      (LinearMap.toContinuousLinearMap ((LinearMap.proj ((1 : Hinf X u), (Y.cs u).h ρ)).comp T.1)) = _
    congr 2
    refine LinearMap.ext fun ξ => ?_
    refine Eq.trans ?_ (he T (cls ρ) ξ).symm
    rw [hsρ]
    rfl
  refine ⟨fun T T' h => ?_, fun x => ?_⟩
  · apply e.injective
    funext c
    obtain ⟨ρ, rfl⟩ := hcls.2 c
    have h1 : (sharp Y.hK (Y.cs u) T) ρ = (sharp Y.hK (Y.cs u) T') ρ := by rw [h]
    rw [key T ρ, key T' ρ] at h1
    exact LinearMap.toContinuousLinearMap.injective ((InnerProductSpace.toDual ℂ (X.Vpi u)).symm.injective h1)
  · let d : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Module.Dual ℂ (X.Vpi u) :=
      fun c => LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm c)))
    refine ⟨e.symm d, ?_⟩
    ext ρ
    refine (key (e.symm d) ρ).trans ?_
    rw [e.apply_symm_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm (ec ρ)))))) = x ρ
    rw [LinearEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply, ec.symm_apply_apply]

theorem finX_of_neat (hN : ∀ u, Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) (hin : ∀ u, InHH X u Y.hK) (hfin : FiniteDimensional ℂ (HHX X))
    (hfib : ∀ u u' (t : RT Y u u'), Finite (fib Y t))
    (hpi : ∀ u u' (s₁ s₂ s₁' s₂' : Formalism.L2.SG.PackageTie2.TT Y u u'), s₁.toTerm = s₁'.toTerm → s₂.toTerm = s₂'.toTerm →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁' = rowOf Y.TR (Y.cs u) (Y.cs u') s₂' →
      s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂')) (hG : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F)
    (hvol : VolPosC) : FinX Y :=
  { shInj := fun u => (sharp_bij_of_neat Y u (hN u)).1
    shSurj := fun u => (sharp_bij_of_neat Y u (hN u)).2
    inHH := hin
    puLin := fun u => Formalism.L2.SG.PoincareInHH.Cut.puLinear_holds X u Y.hK (Y.Dt u)
    finHH := hfin
    fibFin := hfib
    pairIndep := hpi
    Greal := hG
    cdEx := fun n ε => cd_haar_scaling D.cd n ε
    volPos := fun u => hvol D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X) }

end FinXN

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsFinal
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WRowPinHolds
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem WRowPin_holds {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} (hF : FinX Y)
    (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (W : Formalism.L2.SG.TermTieOf.WittDat X) (H : Formalism.L2.SG.TermTieOf.TieHyp W hI)
    (A : Formalism.L2.SG.TermTieOf.AmpDat X) (hV : Formalism.L2.SG.TermTieOf.PvalForm W hI A) :
    Formalism.L2.SG.LoopTieOf.WRowPin hF hI (Formalism.L2.SG.TermTieOf.termTieOf W hI H A hV) := by
  intro u u' p s hs
  have h2 : (Formalism.L2.SG.TermTieOf.tc hI (D.s.pfst p)).lam = s.lam :=
    (congrArg (fun t => t.lam) hs).symm
  show Formalism.MainNotions.S.wRow D (Formalism.L2.SG.TermTieOf.FlagOfWord W u) (Formalism.L2.SG.TermTieOf.lamOf W hI (D.s.pfst p)) = _
  unfold Formalism.L2.SG.TermTieOf.lamOf
  rw [h2]
  exact WRowIso_holds D (W.δ u) (W.isom u) (X.Fu u) s.lam

end Formalism.L2.SG.Pf.WittFlags
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf

namespace Formalism.L2.SG.LoopsFinal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section admitted

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)

variable (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)

end admitted

section AtOne

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF))
  (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A)

theorem jtPin_of (hA : AmpFibreConst Y) : JtPin hF hI (termTieOf W hI H A hV) := by
  intro u u' t s hs
  have h : ∃ s' : Formalism.L2.SG.PackageTie2.TT Y u u', s'.toTerm = tc hI t := ⟨s, hs⟩
  show hsNormSq (JtOf hI t) = ampL s ^ 2
  unfold JtOf
  rw [dite_eq_left h, ← Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  have e := hA u u' (tc hI t) ⟨h.choose, h.choose_spec⟩ ⟨s, hs⟩
  unfold ampL at e ⊢
  rw [e]

def FrameChangeAt : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)),
    (∀ a b, b < a → ξ a b = 0) → (∀ a, ξ a a = 1) →
      ∃ m ∈ NLam (lamOf W hI t) (fl'Of W hI t), ∀ b, m (frame (fl'Of W hI t) b) = frameAct (frame (fl'Of W hI t)) ξ b

theorem frameEqvInj_of (hFC : FrameChangeAt W hI) (u u' : D.what₂.Word) :
    FrameEqvInj (termTieOf W hI H A hV) (u' := u') (FlagOfWord W u) := by
  intro t t' hL hE
  obtain ⟨n, hn, ξ, hl, hd, hfr⟩ := hE
  obtain ⟨m, hm, hmf⟩ := hFC u u' t ξ hl hd
  refine term_injC W hI t t' hL ⟨n, hn, m, hm, fun b => ?_⟩
  have e1 : frame (fl'Of W hI t') b = frameAct (fun a => n (frame (fl'Of W hI t) a)) ξ b := congrFun hfr b
  rw [e1, hmf b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frameAct, map_sum, map_smul]

end AtOne

section Ev

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

end Ev

section Summ

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)}


end Summ

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (Formalism.L2.SG.PackageTie2.sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

def AtF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i) :=
  fun x hx i => termTieOf (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i)

variable (hFC : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FrameChangeAt (W x hx i) (hI x hx i))
  (B : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' C1)
  (M : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTermDat (Fm.D x i) (Fm.L x i) (AtF Fm X Y hF hI W H A hV x hx i) u u' C1 (B x hx i u u'))

variable (hAF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpFibreConst (Y x hx i))
  (hRF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.SG.Pf.FibreCounting.RowFree (Y x hx i))
  (gam : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GamPin (Y x hx i))

end Fam

section Closed

def NormTieC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairNormRelation (termTieOf W hI H A hV) u u'

def GramDeterminantCount : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D (termTieOf W hI H A hV) u u'

def EntryLatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairEntriesInLattice (termTieOf W hI H A hV) u u'

def FrameChangeC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X), FrameChangeAt W hI

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (Formalism.L2.SG.PackageTie2.sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

end Closed

end Formalism.L2.SG.LoopsFinal
end
end
