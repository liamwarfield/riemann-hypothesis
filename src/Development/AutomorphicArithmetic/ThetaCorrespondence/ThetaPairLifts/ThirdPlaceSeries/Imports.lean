module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoTLift
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoTLift
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.IoTop
theorem omT_weil_chr {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    (hc : W.Q.Rl.Char3 W.Q.F) (t : W.P.T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2 (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX t) e) := by
    rintro n rfl
    exact hc.chain.ωX t
  exact key (j + 1) (idx_top h)
end GlobalTheory.Fam.IoTop
set_option maxHeartbeats 1000000 in
open GlobalTheory.Fam.IoTop in
theorem GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j (h : j + 2 * 0 + 2 = D.R.m) (F : (f.t t).CT) P v, liftS ((f.t t).omT j h) f.c.volT.μ f.c.volT.𝓕 (F.1 v) ((f.t t).ptT j h P) = (f.t t).cI (j + 1) • ((f.t t).ioT j h F).1 (f.c.ItT j h P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j h F P v
  have hc := hP.bot.hyp.2.2.2.1
  obtain ⟨h', -, hL⟩ := _root_.GlobalTheory.T.extra_column_range_membership_alt W u hP f.g t j h F
  have key := hL ((f.row t).vT j h) ((hR.row t).vT j h) P v
  obtain ⟨h'', hio⟩ := (hR.row t).ioT j h F
  have hm := hR.meas.volT t
  rw [show D.R.m - 1 = j + 1 by omega, show f.g.κ D.R.m = f.g.κ (j + 1 + 1) from congrArg f.g.κ (by omega)] at hm
  have hom := _root_.GlobalTheory.Fam.IoTop.omT_weil_chr W hc t j h
  have hth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row t).vT j h) P) := by
    obtain ⟨cY, hcY⟩ := hc.lev.βY (j + 1) (by omega)
    obtain ⟨cX', hcX⟩ := hc.lev.βX
    have hf := (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcY) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcX) hcY.1 hcX.1
      ((hR.row t).vT j h)
    have e0 : ∀ (V : HSp D) (ρ : D.what₂.Tau), compAt (_root_.GlobalTheory.Fam.pk_z W).θ ρ (Formalism.L2.Theta.mt V 1) = 1 := fun V ρ => by
      have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this]
      exact Matrix.map_one _ (by simp) (by simp)
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hom hc.models.inf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) 1 1
      (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) _ hf P).1
  have hκ := hR.meas.κ (j + 1 + 1)
  have hvl : 0 ≤ volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1) := by unfold volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : ENNReal.ofReal (f.g.κ (j + 1 + 1) * volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1)) ≠ 0 := by
    have := (hR.meas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) (by omega))
    unfold cIOf at this
    intro h0
    rw [ENNReal.ofReal_eq_zero] at h0
    refine this ?_
    have : f.g.κ (j + 1 + 1) * volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1) = 0 := le_antisymm h0 (mul_nonneg hκ.le hvl)
    rw [mul_assoc, ← Complex.ofReal_mul, this, Complex.ofReal_zero, mul_zero]
  have hfd := (hc.models.νX t).2
  show liftS (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) f.g.volT.μ f.g.volT.𝓕 (F.1 v) _ = cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t (j + 1) • _
  funext x
  have e1 := liftS_smul_domain (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) ((_root_.GlobalTheory.Fam.pk_z W).νX t) f.g.volT.μ _ hc0 hm f.g.volT.haar f.g.volT.fund hfd
    (F.1 v) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row t).vT j h) P) x (fun γ hγ y => by
        have a1 : (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (x, γ * y) = (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (1, γ) * (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (x, y) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        rw [a1, Module.End.mul_apply, hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres _ _ hth),
          GlobalTheory.ChainLiftEquiv.multT_left _ _ _ _ F.1 F.2 v γ hγ y])
  have hio' : (((f.t t).ioT j h) F).1 = ((ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h) ⟨F.1, h'⟩).1 := hio
  have e2 : (((f.t t).ioT j h) F).1 (((f.c.ItT j h) P) v) x = ((ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h) ⟨F.1, h'⟩).1 (((f.c.ItT j h) P) v) x :=
    congrFun (LinearMap.congr_fun hio' _) x
  have e3 := congrFun key x
  rw [Pi.smul_apply] at e3
  exact e1.trans ((congrArg _ e3).trans ((smul_const _ _ _ _ (mul_nonneg hκ.le hvl)).trans (congrArg _ e2.symm)))
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoTLiftStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_s_last_eq_ci_succ_smul_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j (h : j + 2 * 0 + 2 = D.R.m) (F : (f.t t).CT) P v, liftS ((f.t t).omT j h) f.c.volT.μ f.c.volT.𝓕 (F.1 v) ((f.t t).ptT j h P) = (f.t t).cI (j + 1) • ((f.t t).ioT j h F).1 (f.c.ItT j h P v) := by
  first | exact @_root_.GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT | exact _root_.GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT | (intros; apply _root_.GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftEqCIIo
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftEqCIIo
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.LiftVol
set_option maxHeartbeats 1000000 in
theorem lift_levelP_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ (F : CP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1)) (hF : F.1 ∈ (_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)), ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v → ∀ Q x, liftS ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (F.1 x) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q) = (Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H : ℂ) • ((_root_.GlobalTheory.Fam.pk_z W).ioY t j ⟨F.1, hF⟩).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j Q x) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF v hv Q x
  have hio : Lift.IsIo ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j)
      ((_root_.GlobalTheory.Fam.pk_z W).ItY j) ((_root_.GlobalTheory.Fam.pk_z W).CC t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).CC t j) ((_root_.GlobalTheory.Fam.pk_z W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := _root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt W hW t j hj
  funext g
  unfold liftS Lift.liftInt
  rw [hsum v hv Q]
  simp_rw [thetaKO_sum_translates]
  have hint : ∀ p ∈ (Finset.univ : Finset (_root_.GlobalTheory.Fam.complexLevelStructure W).H), IntegrableOn (fun h => (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ * thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ p) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) * F.1 x h) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ hint]
  have e : ∀ p ∈ (Finset.univ : Finset (_root_.GlobalTheory.Fam.complexLevelStructure W).H), ∫ h in (_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1), (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ * thetaKO ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) (g * κ p) h ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) * F.1 x h ∂(_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) =
      ((_root_.GlobalTheory.Fam.pk_z W).ioY t j ⟨F.1, hF⟩).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j Q x) g := by
    intro p _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have h1 := hio.eq ⟨F.1, hF⟩ Q x (g * κ p)
    simp only [Lift.liftInt] at h1
    rw [h1, _root_.GlobalTheory.T.chain_projection_level_character_alt W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]
    rw [← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p)), one_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul, Pi.smul_apply, smul_eq_mul]
set_option maxHeartbeats 800000 in
theorem liftS_pt_eq_cI_smul_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j, j + 1 < D.R.m → ∀ (G : (f.t t).CC (j + 1)) P v, liftS ((f.t t).om j) (f.c.vol (j + 1)).μ (f.c.vol (j + 1)).𝓕 (G.1 v) ((f.t t).pt j P) = (f.t t).cI j • ((f.t t).io j G).1 (f.c.It j P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j hj G P v
  have h3 := hP.bot.hyp.2.2.2.1
  have hch : (_root_.GlobalTheory.Fam.pk_z W).IsChain := h3.chain
  have hmod : (_root_.GlobalTheory.Fam.pk_z W).IsModels := h3.models
  obtain ⟨h, hio⟩ := (hR.row t).io j hj G
  have hstep := (hR.row t).vP j hj
  have hk := _root_.GlobalTheory.Fam.LiftVol.lift_levelP_alt W hP t j hj G h
  have hk' := hk _ hstep P v
  have hω := hch.ωY t j hj
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hmod.inf
  have hpt := GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j))
    (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (GlobalTheory.VecTheta.isThetaFunO_stepVec hstep) P
  have hvol := hR.meas.vol t j hj
  have hκ := hR.meas.κ (j + 1)
  have hHF : ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1)) := by
    by_cases h2 : j + 1 + 1 < D.R.m
    · have h4 := hmod.νY t (j + 1) h2
      exact ⟨h4.1.1, h4.2⟩
    · have h4 := hmod.νY' t
      have e : D.R.m - 1 = j + 1 := by omega
      rw [e] at h4
      exact ⟨h4.1.1, h4.2⟩
  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 G.2)
  have hleft : ∀ (w : SmT ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))), ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, G.1 w (γ * x) = G.1 w x := by
    intro w γ hγ x
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (hm.aut w).left γ hγ x
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add (f := _), Pi.add_apply, ha, ha']
  have hthL : ∀ g, ∀ γ ∈ GQ (Yc D (j + 1)), ∀ x, (_root_.GlobalTheory.Fam.pk_z W).ωY t j (g, γ * x) ((f.t t).pt j P) 0 =
      (_root_.GlobalTheory.Fam.pk_z W).ωY t j (g, x) ((f.t t).pt j P) 0 := by
    intro g γ hγ x
    have e : ((g, γ * x) : GA D (Yc D j) × GA D (Yc D (j + 1))) = (1, γ) * (g, x) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have : IsTopologicalGroup (GA D (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D (Yc D (j + 1))) := ⟨rfl⟩
  have : Countable (GQ (Yc D (j + 1))) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Yc D (j + 1)).gram
  have hvol' : (f.c.vol (j + 1)).μ = ENNReal.ofReal (f.g.κ (j + 1) * GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j) • (_root_.GlobalTheory.Fam.pk_z W).νY t (j + 1) := hvol
  have : (f.c.vol (j + 1)).μ.IsHaarMeasure := (f.c.vol (j + 1)).haar
  have hF₁ := (f.c.vol (j + 1)).fund
  have hF₂ : IsFundamentalDomain (GQ (Yc D (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).fdY t (j + 1)) (f.c.vol (j + 1)).μ :=
    hHF.2.mono (by rw [hvol']; exact Measure.smul_absolutelyContinuous)
  funext g
  rw [liftS_apply, hF₁.setIntegral_eq hF₂ (fun γ x => by
    show (_root_.GlobalTheory.Fam.pk_z W).ωY t j (g, (γ : GA D (Yc D (j + 1))) * x) ((f.t t).pt j P) 0 * G.1 v ((γ : GA D (Yc D (j + 1))) * x) = _
    rw [hthL g γ γ.2 x, hleft v γ γ.2 x])]
  rw [hvol', Measure.restrict_smul, integral_smul_measure]
  have hk2 := congrFun hk' g
  rw [liftS_apply] at hk2
  have hv0 : 0 ≤ GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j := by
    unfold GlobalTheory.Fam.volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : 0 ≤ f.g.κ (j + 1) * GlobalTheory.Fam.volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t j := mul_nonneg hκ.le hv0
  rw [ENNReal.toReal_ofReal hc0]
  erw [hk2]
  show _ = (cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t j • ((f.row t).io j G).1 ((_root_.GlobalTheory.Fam.pk_z W).ItY j P v)) g
  rw [hio]
  simp only [Pi.smul_apply, cIOf, Complex.real_smul, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring
end GlobalTheory.Fam.LiftVol
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftEqCIIoStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_s_eq_ci_smul_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j, j + 1 < D.R.m → ∀ (G : (f.t t).CC (j + 1)) P v, liftS ((f.t t).om j) (f.c.vol (j + 1)).μ (f.c.vol (j + 1)).𝓕 (G.1 v) ((f.t t).pt j P) = (f.t t).cI j • ((f.t t).io j G).1 (f.c.It j P v) := by
  first | exact @_root_.GlobalTheory.Fam.LiftVol.liftS_pt_eq_cI_smul_io | exact _root_.GlobalTheory.Fam.LiftVol.liftS_pt_eq_cI_smul_io | (intros; apply _root_.GlobalTheory.Fam.LiftVol.liftS_pt_eq_cI_smul_io <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkStatement
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.Mi.SpanY
theorem itSpans_pk_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP j hj
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  obtain ⟨hw, hv⟩ := hok.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).vY W.P.A3.A.μ0 j) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) hC.models.inf hw hv (hC.chain.ItY W.P.A3.A.μ0 j hj)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((_root_.GlobalTheory.Fam.pk_z W).ItY j P) (Submodule.span ℂ
      {x | ∃ (P : PolF D (Yc D (j + 1)).rank (Yc D j).rank) (y : ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)).Vec), KVecP ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) y ∧
        x = (_root_.GlobalTheory.Fam.pk_z W).ItY j P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'
end GlobalTheory.Core.Mi.SpanY
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.itSpans_MY_succ : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY j) ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ItY j) := by
  first | exact @_root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt | exact _root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt | (intros; apply _root_.GlobalTheory.Core.Mi.SpanY.itSpans_pk_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IteratesSpanLastStep
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ItSpansPkAltAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Core.Mi.SpanX
theorem itSpans_pk_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ItX := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  have hm : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  obtain ⟨hw, hv⟩ := hok.2 W.P.A3.A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).θ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).vX W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).ItX hC.models.inf hw hv (hC.chain.ItX W.P.A3.A.μ0)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((_root_.GlobalTheory.Fam.pk_z W).ItX P) (Submodule.span ℂ
      {x | ∃ (P : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (y : (_root_.GlobalTheory.Fam.pk_z W).MX.Vec), KVecP (_root_.GlobalTheory.Fam.pk_z W).MX y ∧
        x = (_root_.GlobalTheory.Fam.pk_z W).ItX P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'
end GlobalTheory.Core.Mi.SpanX
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.itSpans_MY_last_MX : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY (D.R.m - 1)) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ItX := by
  first | exact @_root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt | exact _root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt | (intros; apply _root_.GlobalTheory.Core.Mi.SpanX.itSpans_pk_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Imports
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.IsFam
theorem main_alt_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hP f hR
  have hC := hP.bot.hyp.2.2.2.1
  have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := (hC.chain.ωX W.P.A3.A.μ0).std
  have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hC.models.inf
  have spanT : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((_root_.GlobalTheory.Fam.pk_z W).MY n) (_root_.GlobalTheory.Fam.pk_z W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] SmT ((_root_.GlobalTheory.Fam.pk_z W).MY n)) (_root_.GlobalTheory.Fam.pk_z W).ItX e) := by
    intro n e
    subst e
    exact _root_.GlobalTheory.T.itSpans_MY_last_MX hDS hHC W hP
  refine ⟨⟨hstd, hinf, hR.x, (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D D.sp.X').2 GlobalTheory.Hk3.StepX.gram_posDef_X,
    hR.meas.μf, hR.meas.ρJ, hR.meas.ρB, fun j hj => _root_.GlobalTheory.T.itSpans_MY_succ hDS hHC W hP j hj, fun j h => spanT _ (idx_top h)⟩, fun hCol t => ?_⟩
  exact
    { sBF := fun j ρ h => ⟨((hR.row t).sBF j ρ h).1, ((hR.row t).sBF j ρ h).2.1⟩
      sFB := fun j σ h => ⟨((hR.row t).sFB j σ h).1, ((hR.row t).sFB j σ h).2.1⟩
      pt := fun j hj P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vP j hj)) P
      ptT := fun j h P => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hinf _ _ _ _
        (GlobalTheory.VecTheta.isThetaFunO_stepVec ((hR.row t).vT j h)) P
      CC := fun j _ => ⟨_, _, le_rfl⟩
      CT := ⟨_, _, le_rfl⟩
      io := _root_.GlobalTheory.T.lift_s_eq_ci_smul_io W u hP f hR t
      ioT := _root_.GlobalTheory.T.lift_s_last_eq_ci_succ_smul_io W u hP f hR t
      cI := fun j hj => hR.meas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) t j hj
      ker := hCol.ker t
      e := hCol.e t
      eT := hCol.eT t
      stabK := hCol.stabK t
      stabS := hCol.stabS t }
end GlobalTheory.Fam.IsFam
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  exact @_root_.GlobalTheory.Fam.IsFam.main_alt_alt
end
end
