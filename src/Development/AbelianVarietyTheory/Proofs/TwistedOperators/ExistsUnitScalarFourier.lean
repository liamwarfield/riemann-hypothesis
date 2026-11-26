module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappa

theorem fock_jets_moved : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt →
    ∀ f, IsVacO ψ θ S T sS sT (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f →
    ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt ∧ Θ ≠ 0 ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ Ls Lt hLs hLt f hf
  have hsS := GlobalTheory.FockPos.cart_one frS hS hcS
  have hsT := GlobalTheory.FockPos.cart_one frT hT hcT
  subst hsS hsT
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
  have hTh := GlobalTheory.T.unitVacuumEntireFactor_isTheta_movedLattices ψ θ S T frS frT hS hT δ hC hδ Ls Lt hLs hLt f hf Φ hΦd hreal
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hTh
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  refine ⟨Θ, hTh, ?_, fun k => ?_⟩
  · intro h0
    obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ f hf
    apply hfw
    have h1 : Φ (GlobalTheory.FockPos.zCo θ frS frT w) = 0 := by
      rw [hΦeq]
      exact congrFun h0 _
    rw [hreal w hw, h1, mul_zero]
  · have hdiff : Differentiable ℂ Θ := hTh.1
    have hj := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hf.2.inf hS hT f Φ hΦd hreal k
    change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f
      (MvPolynomial.monomial k 1) 0 = _
    rw [hj, hΦeq, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial',
      GlobalTheory.FockPos.taylor_comp_smul' D _ hdiff]
    have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ =
        δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
      intro τ
      rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
    have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
        (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
      simp only [hper, Finsupp.prod, Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprod, mul_pow]
    ring

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) {G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (hG : Differentiable ℂ G) (a : ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (fun z => a * G z) =
      a * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G := by
  rw [GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.ProdThetaConj.taylor_const_mul hG]
  ring

theorem intertwining_mem_ne_zero {D : D7} {δ t0 : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ)
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0) {N N' : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (he0 : Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : Formalism.MainNotions.StandardLatticesGL3.SD D L) (hL' : Formalism.MainNotions.StandardLatticesGL3.SD D L') {Θ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (hΘ : Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') (hΘ0 : Θ ≠ 0) :
    ∃ κ : ℂ, Θ = (fun z => κ * Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0 z) ∧
      Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0) := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') 0 = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK δ t0 hC ht) hn.symm
  have hK1 : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D N, GlobalTheory.NormSum.VacInt.sd_std D N', rfl⟩
  have hK2 : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') :=
    Or.inr ⟨L, L', hL, hL', rfl⟩
  have hne : ∃ z, Θ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΘ0 (funext h)
  have hS := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.semiChar_of_ne_zero _ hΘ hne
  have hI := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Iop_mem_ThSp _ hS he0.1
  have hI0 : Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0 ≠ 0 := by
    intro h0
    obtain ⟨-, -, hself, htrip⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK δ hC N N'
    obtain ⟨μ, hμ⟩ := htrip _ _ _ hK1 hK2 hK1 e0 he0.1 he0ne
    have h1 := hμ.2.2.2.2.2.2.2.2.2
    have hμ8 := hμ.2.2.2.2.2.2.2.2.1
    rw [h0, GlobalTheory.NormSum.VacMove.iop_zero, hself _ hK1 e0 he0.1] at h1
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      norm_num at hμ8
    apply he0ne
    funext z
    have := congrFun h1 z
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hμ0
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG D.host.ccK δ hC N N' _ hK2).1 Θ hΘ _ hI hI0
  exact ⟨c, hc, hI.1⟩

end GlobalTheory.MovedKappa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransfer
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.R3.DatCopy

noncomputable section

namespace GlobalTheory.Twist

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
theorem multEq_rowTest_of_copy :
    ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px)
      (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b)
      (z : Dat a.st I hX Tw Wt),
      let z' := GlobalTheory.Mem.R3.DatCopy.copy b s z
      (GlobalTheory.CuspMult.MultEq z'.R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧
        (Formalism.IndefR.Rat.RowTest (z'.R.toCx3 z'.F) →
          Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) := by
  intro B C a b px I hX Tw Wt s z
  have e := twice_eq b (iK := z.alg) z.R
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := multEq_tr (a := b) a (iK := alg b z.alg) (R := real b z.R.toRealDat)
      (by with_unfolding_all exact h)
    rw [e]
    with_unfolding_all exact h2
  · have h2 := rowTest_tr (a := b) a (iK := alg b z.alg) (R := real3 b z.R) (F := face3 b z.F)
      (by with_unfolding_all exact h)
    rw [e]
    with_unfolding_all exact h2

end GlobalTheory.Twist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransferStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
theorem _root_.GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer :
    ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px)
      (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b)
      (z : Dat a.st I hX Tw Wt),
      let z' := GlobalTheory.Mem.R3.DatCopy.copy b s z
      (GlobalTheory.CuspMult.MultEq z'.R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧
        (Formalism.IndefR.Rat.RowTest (z'.R.toCx3 z'.F) →
          Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) :=
  GlobalTheory.Twist.multEq_rowTest_of_copy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSpanFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSpanFiniteDimensional
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.FockVac

theorem span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  by_cases h : ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧ g ≠ 0
  · obtain ⟨g, hg, hg0⟩ := h
    have hle : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} ≤ Submodule.span ℂ {g} := by
      refine Submodule.span_le.2 fun f hf => ?_
      obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M B.ψ B.emb hP.base.cm hP.base.std
        (fun w => (hP.herm.cartan w).1) (fun w => (hP.skew.cartan w).1) f g hg hg0 hf
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    exact Submodule.finiteDimensional_of_le hle
  · push_neg at h
    have hb : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} = ⊥ :=
      Submodule.span_eq_bot.2 fun f hf => by_contra fun h0 => h0 (h f hf)
    rw [hb]
    infer_instance

end GlobalTheory.FockVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSpanFiniteDimensionalStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  first | exact @GlobalTheory.FockVac.span_finiteDimensional | exact GlobalTheory.FockVac.span_finiteDimensional | (intros; apply GlobalTheory.FockVac.span_finiteDimensional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Chain (ptOf)
open GlobalTheory.Chain.RealIt (glue)

namespace GlobalTheory.EvenOntoRealZeta


open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction in
theorem realZeta : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, RealZeta D := by
  intro hDS hHC D c hc k hk s s' hs hs' p hp m X hmX
  have hvac := hp.pre.vac
  have hW := hp.pre.weil
  have hArch := fun τ =>
    (GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions hDS hHC D c.t (s.par τ) (s'.par τ) (c.a k τ) (c.a k τ) (hp.pre.par τ)).1 τ s.V s'.V
  have hfock : ∀ τ, IsFockAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f :=
    fun τ => ⟨hc.inf, isAdapted_model s.M τ, isAdapted_model s'.M τ, hvac.theta, hvac.ne, hvac.vac τ⟩
  have hLL := fun τ => (hArch τ).1 c.ψ c.θ (c.χ k) (c.χ k) p.ω hW (hc.exp k hk τ) (hc.exp k hk τ)
    s.par s'.par s.M s'.M rfl rfl _ _ p.f (hfock τ)
  have hZL := fun τ => (hArch τ).2 c.ψ c.θ (c.χ k) (c.χ k) p.ω hW (hc.exp k hk τ) (hc.exp k hk τ)
    s.par s'.par s.M s'.M rfl rfl _ _ p.f (hfock τ) m X hmX.1 hmX.2.1
  choose Φ hΦ using fun τ => (hLL τ).joint_ex
  choose w hwsm hwk hwhi using fun τ => GlobalTheory.T.exists_smooth_kFinite_unit_highestWeight_vector hHC D s.V s.par s.M τ
  refine ⟨glue Φ, fun τ => ⟨w τ, hwsm τ⟩, fun τ => hwk τ, ?_⟩
  intro mR hmR z
  have hfac := GlobalTheory.T.thetaInner_fockProduct_eq_prod_realPlaces D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.χ k) (c.χ k) p.ω hc.inf hW m X hmX p.f hvac
  obtain ⟨cst, hcst, hhaar⟩ := GlobalTheory.T.integral_realUnitary_haar_eq_prod_Upq_haar D s.V s.par s.M c.θ hc.inf mR (fun τ => Formalism.REAL.muG (s.M.ε τ)) hmR
    (fun τ => inferInstance)
  have hZ := fun τ => hZL τ (Φ τ) (hΦ τ) ⟨w τ, hwk τ⟩ (hwhi τ) (Formalism.REAL.muG (s.M.ε τ)) inferInstance
  set i0 := ipTh m X p.f p.f with hi0
  set F : D.what₂.Tau → Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ → ℂ := fun τ h =>
    ipTh m X (p.ω (atTau c.θ s.V τ h, 1) (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
      (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) / i0 *
      conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ with hF
  have hrep : ∀ τ (Y : Matrix (Fin s.V.rank) (Fin s.V.rank) ℂ), s.M.rep τ (ofFr s.M τ Y) = s.M.σ τ Y := by
    intro τ Y
    have h1 : s.M.fr τ * (s.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (s.M.fr_unit τ))
    have : s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹ = Y := by
      calc s.M.fr τ * ((s.M.fr τ)⁻¹ * Y * s.M.fr τ) * (s.M.fr τ)⁻¹
          = (s.M.fr τ * (s.M.fr τ)⁻¹) * Y * (s.M.fr τ * (s.M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [h1]; simp
    simp only [DSModel.rep, ofFr, this]
  have hFu : ∀ τ (u : Formalism.REAL.UJ (s.M.ε τ)), F τ (ofFr s.M τ (umat u)) =
      ipTh m X (actSrc c.θ p.ω τ (ofFr s.M τ (umat u))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)))
        (ptAt c.ψ c.θ s.V s'.V τ (cart s.M τ) (cart s'.M τ) (onb s.M τ) (onb s'.M τ) p.f (Φ τ)) *
        star (coefOn (s.M.σ τ) (w τ) (w τ) u) / i0 := by
    intro τ u
    simp only [hF, hrep, actSrc, coefOn, starRingEnd_apply]
    ring
  have hFint : ∀ τ, Integrable (fun u : Formalism.REAL.UJ (s.M.ε τ) => F τ (ofFr s.M τ (umat u))) (Formalism.REAL.muG (s.M.ε τ)) := by
    intro τ; simp_rw [hFu]; exact (hZ τ).2.1.div_const _
  have hFval : ∀ τ, ∃ r : ℝ, 0 < r ∧ ∫ u, F τ (ofFr s.M τ (umat u)) ∂(Formalism.REAL.muG (s.M.ε τ)) = (r : ℂ) / i0 := by
    intro τ
    obtain ⟨r, hr, hrI⟩ := (hZ τ).2.2.1
    refine ⟨r, hr, ?_⟩
    simp_rw [hFu]; rw [integral_div, hrI]
  choose r hr hrI using hFval
  have hi0 : i0 ≠ 0 := hfac.1
  have hz : ∀ g : GinfC s.V, z g = i0 * ∏ τ, F τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) := by
    intro g
    have h := hfac.2 Φ g g.2
    change ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
      conj (∏ τ, ⟪(w τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) = _
    rw [h, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  obtain ⟨hIint, hIval⟩ := hhaar F hFint
  have hintz : ∫ g, z g ∂mR = i0 * ((cst : ℂ) * ∏ τ, ((r τ : ℂ) / i0)) := by
    simp_rw [hz]; rw [integral_const_mul, hIval]; simp_rw [hrI]
  refine ⟨?_, ?_⟩
  · rw [hintz]
    exact mul_ne_zero hi0 (mul_ne_zero (by exact_mod_cast hcst.ne')
      (Finset.prod_ne_zero_iff.2 fun τ _ => div_ne_zero (by exact_mod_cast (hr τ).ne') hi0))
  · intro a ha hfr
    have htpos : 0 < c.t := by have := hc.step; omega
    refine ⟨0, div_pos (by exact_mod_cast htpos) two_pos, ?_⟩
    obtain ⟨C, hC⟩ := GlobalTheory.T.realMatrixCoeff_fockVectors_le_doublingHeight_pow D s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ (c.χ k) (c.χ k) p.ω hc.inf hW m X hmX p.f hvac
      a ha hfr (glue Φ) (glue Φ)
    set mf : GinfC s.V → ℂ := fun g => conj (∏ τ, ⟪(w τ : s.M.H τ),
      s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (w τ)⟫_ℂ) with hmf
    have hmint : Integrable mf mR := by
      obtain ⟨hI2, -⟩ := hhaar (fun τ h => conj ⟪(w τ : s.M.H τ), s.M.rep τ h (w τ)⟫_ℂ) (fun τ => by
        simp only [hrep]
        exact (hZ τ).1.norm.mono' (hZ τ).1.1.star (Filter.Eventually.of_forall fun x => (RCLike.norm_conj _).le))
      simpa [hmf, map_prod] using hI2
    set Hf : GinfC s.V → ℝ := fun g => ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w
      (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (g : GA D s.V)) with hHf
    have hHc : Continuous Hf := continuous_finsetProd _ fun w _ =>
      (GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).1.comp ((GlobalTheory.AdelicU.continuous_projArch _ _ w).comp continuous_subtype_val)
    have hHpos : ∀ g, 0 < Hf g ∧ Hf g ≤ 1 := fun g =>
      ⟨Finset.prod_pos fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1,
        Finset.prod_le_one₀ (fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).1.le)
          fun w _ => ((GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one D s.V a ha w).2 _).2⟩
    have hzint : Integrable z mR :=
      (hIint.const_mul i0).congr (Filter.Eventually.of_forall fun g => (hz g).symm)
    have htb : c.t ≤ s'.V.rank := by
      rw [hs'.rank]; nlinarith
    have hbd : ∀ g, ‖z g‖ ≤ C * Hf g ^ ((s'.V.rank : ℝ) / 2) * ‖mf g‖ := by
      intro g
      change ‖ipTh m X (p.ω ((g : GA D s.V), 1) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ))) (ptOf c.ψ c.θ s.M s'.M p.f (glue Φ)) *
        mf g‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC g g.2) (norm_nonneg _)
    exact GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor mR z mf Hf C s'.V.rank c.t hzint hmint hHc hHpos htb hbd

end GlobalTheory.EvenOntoRealZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaStep_realZeta_nonvanishing : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, RealZeta D := by
  first | exact @GlobalTheory.EvenOntoRealZeta.realZeta | exact GlobalTheory.EvenOntoRealZeta.realZeta | (intros; apply GlobalTheory.EvenOntoRealZeta.realZeta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.RowEx.DatTw

open Formalism.L2.Host

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have e := congrArg (Int.cast : ℤ → R) huv
  push_cast at e
  rw [← e]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v)
    (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, one_mul]

theorem unrAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt v := fun _ _ => rfl

variable {R : Ranks} (H : Host R)

theorem unrAt_of_isTwist {S : Set ℕ} (hS : GlobalTheory.EX.DC.q0H H ∈ S) {ψ : HChar H.E} (hψ : Chr.IsTwist H S ψ)
    {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) : ψ.UnrAt v := by
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := hψ.2.2.2 v h
  by_cases e : Ideal.absNorm v.asIdeal = GlobalTheory.EX.DC.q0H H
  · exact hnot (e ▸ hS)
  · exact not_two_primes v.asIdeal hpr (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 e (Ideal.absNorm_mem _) hv

theorem not_overP_pde {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) :
    ¬ OverP H H.pde v ∧ ¬ OverP H H.pde' v :=
  ⟨fun h => not_two_primes v.asIdeal H.pde_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).1.symm h hv,
    fun h => not_two_primes v.asIdeal H.pde'_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).2.symm h hv⟩

theorem unrAt_of_mem_set {B : Base} {f : Fr B.toPre} {T : TwDat B} {ξ : HChar B.host.E} (h : ξ ∈ T.set f)
    {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : ((GlobalTheory.EX.DC.q0H B.host : ℕ) : 𝓞 B.host.E) ∈ v.asIdeal) : ξ.UnrAt v := by
  have hd := not_overP_pde B.host hv
  have hdel : f.del.UnrAt v := f.isDel.unr v hd.1
  have hdel' : f.del'.UnrAt v := f.isDel'.unr v hd.2
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at h
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact unrAt_one v
  · exact hdel
  · exact hdel'
  · unfold TwDat.xiTw
    refine unrAt_mul ?_ (unrAt_of_isTwist B.host ?_ (T.psi_tw w) hv)
    · split_ifs
      · exact hdel'
      · exact hdel
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end GlobalTheory.RowEx.DatTw

theorem GlobalTheory.RowEx.twisted_data_off_base_level : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GlobalTheory.RowEx.TwistPlacesOffPrimeQZero z.R.toLevCh ∧ z.R.C = Fr.at (w.st Z) f ∧
      (T.set f).Finite ∧ ∀ t, z.R.xiH t ∈ T.set f := by
  intro B f T w Z hX Wt z
  have hmem : ∀ t, z.R.xiH t ∈ T.set f := fun t => by
    rw [z.lev.xiH t, ← w.xi_range]
    exact ⟨_, rfl⟩
  refine ⟨fun t PP hPP hq => ?_, ?_, ?_, hmem⟩
  · exact (z.lev.is.Q_ram t PP).2 (Or.inl hPP) (GlobalTheory.RowEx.DatTw.unrAt_of_mem_set (hmem t) hq)
  · rw [z.lev.C, w.C_eq]
  · rw [← w.xi_range]
    exact Set.finite_range _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpCuspApprox

theorem val_aut_cusp {D : D7} {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {F : N.Maps} (hF : F ∈ N.Cusp θ)
    (v : SmT N.M) : IsAutFunSm θ N.V (F v) ∧ IsCuspFun N.V (F v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 _).1 ((Formalism.IndefR.Mult.mem_multT θ N.M ∅ 1 F).1 hF)
  have e : F = PiTensorProduct.lift (PiTensorProduct.lift.symm F) := (LinearEquiv.apply_symm_apply _ F).symm
  rw [e]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul c (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

end GlobalTheory.UpCuspApprox

namespace GlobalTheory.UpCuspApprox

end GlobalTheory.UpCuspApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairListProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LineDerivSplit

theorem pure_add₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_listSum {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (l : List ι)
    (h : ι → SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (l.map h).sum φ = (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (h i) φ).sum := by
  induction l with
  | nil => funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  | cons a l ih => simp [pure_add₀, ih]

theorem sum_listSum {α ι : Type} [AddCommMonoid α] {m : ℕ} (l : List ι) (a : Fin m → ι → α) :
    ∑ j, (l.map (a j)).sum = (l.map fun i => ∑ j, a j i).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Finset.sum_add_distrib, ih]

end GlobalTheory.LineDerivSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspLiftFiniteSumApproximation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnFormApprox

variable {D : D7}

theorem autSm_cusp_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFunSm θ N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have h0 : IsCuspFun N.V (0 : GA D N.V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
  have hz : IsAutFunSm θ N.V (0 : GA D N.V → ℂ) := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ N.V
  have hU' : ∀ w, IsAutFunSm θ N.V (U w) ∧ IsCuspFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨hx.aut w, hx.cusp w⟩
    | zero => exact fun w => ⟨hz, h0⟩
    | add x y _ _ hx hy => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_add (hx w).1 (hy w).1,
        GlobalTheory.MultMem.isCuspFun_add (hx w).1.toIsAutFun (hy w).1.toIsAutFun (hx w).2 (hy w).2⟩
    | smul c x _ hx => exact fun w => ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hx w).1, GlobalTheory.MultMem.isCuspFun_smul c (hx w).2⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hU' f).1, GlobalTheory.MultMem.isCuspFun_smul r (hU' f).2⟩
  | add x y hx hy => simpa using ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem autSm_cusp_sum {V : HSp D} {θ : InfFam D} (K : Finset ℕ) (u : ℕ → GA D V → ℂ)
    (hu : ∀ k ∈ K, IsAutFunSm θ V (u k) ∧ IsCuspFun V (u k)) :
    IsAutFunSm θ V (∑ k ∈ K, u k) ∧ IsCuspFun V (∑ k ∈ K, u k) := by
  induction K using Finset.induction_on with
  | empty =>
    have h0 : IsCuspFun V (0 : GA D V → ℂ) := fun r C hC μ 𝓕 hμ h𝓕 g => by simp
    rw [Finset.sum_empty]
    exact ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, h0⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hA := hu a (Finset.mem_insert_self a s)
    have hB := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hA.1 hB.1, GlobalTheory.MultMem.isCuspFun_add hA.1.toIsAutFun hB.1.toIsAutFun hA.2 hB.2⟩

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox

namespace GlobalTheory.DnFormApprox

end GlobalTheory.DnFormApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalSmoothVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Size

variable {D : D7}

theorem thetaKO_le_unif {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    {K : Set (GA D W)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h f‖ ≤ C * GlobalTheory.Grow.height V g ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact W hK
  have hs : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal := mul_nonneg hC0 ENNReal.toReal_nonneg
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A, A, mul_nonneg hs (pow_nonneg (by positivity) _),
    fun h hh g => ?_⟩
  have h1 := (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h
  have hW : GlobalTheory.Grow.height W h ≤ max B 1 := (hB h hh).trans (le_max_left _ _)
  have hW0 : 0 ≤ GlobalTheory.Grow.height W h := (GlobalTheory.Grow.height_pos W h).le
  have hV0 : 0 ≤ GlobalTheory.Grow.height V g := (GlobalTheory.Grow.height_pos V g).le
  calc ‖thetaKO ω g h f‖ = ‖ω (g, h) f 0‖ := rfl
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A := h1
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * max B 1) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hV0 hW0)
          (mul_le_mul_of_nonneg_left hW hV0) _) hs
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A * GlobalTheory.Grow.height V g ^ A := by ring

theorem thetaKO_le_quotHeight {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε S) T Φ) {K : Set (GA D T)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.quotHeight S g ^ A := by
  have e : ∀ g h, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((GlobalTheory.Grid.ofSgn ε S).symm g) h Φ := fun g h => by
    show ω (g, h) Φ 0 = ω (GlobalTheory.Grid.ofSgn ε S ((GlobalTheory.Grid.ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  obtain ⟨C, A, hC0, hC⟩ := thetaKO_le_unif hθ hω hΦ hK
  have hC' : ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.height S g ^ A := fun h hh g => by
    simp only [e]
    exact hC h hh _
  exact ⟨C * 2 ^ A, A, by positivity, fun h hh g => GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) (hC' h hh) g⟩

end GlobalTheory.DownApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem GlobalTheory.PoinAut.partialSum_bdd : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  intro D θ hθ V S M Λ 𝔪 hΛ v hv _ c a Kc hK
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hKdef
  set N := 2 * V.rank ^ 2 + 1 with hN
  obtain ⟨C₀, A₀, hI⟩ := GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c
  obtain ⟨C, hC, hCb⟩ := GlobalTheory.PoinAut.coefR_le_majorant D θ hθ V S M v (fun τ => (a τ : M.H τ)) N
    (fun τ => (hv τ).2 _ (a τ).2)
  obtain ⟨H, hH⟩ := hK.exists_bound_of_continuousOn (GlobalTheory.Grow.continuous_height V).continuousOn
  set P : ℝ := ∏ τ, (1 + hsn (cmp θ τ (1 : GA D V)⁻¹)) ^ N with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg fun τ _ =>
    pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _
  have hKtop : ∀ y, y ∈ K → y ∈ congLev D.sp.cm V.gram Λ ⊤ := fun y hy => by
    rw [congLev_top]; exact ⟨hy.1, hy.2.1⟩
  refine ⟨C * P * (max C₀ 0 * H ^ A₀), fun x hx s => ?_⟩
  have hterm : ∀ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
      ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ ≤
        C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by
    intro γ hγ
    unfold coef
    rw [if_pos (Finset.mem_filter.1 hγ).2]
    have := hCb (c * (γ : GA D V) * x) 1
    rwa [mul_one] at this
  have hx0 : 0 ≤ height V x := (height_pos V x).le
  have hxH : height V x ≤ H := by
    have := hH x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg hx0] at this
  calc ∑ γ ∈ s, ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖
      = ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ := by
        refine (Finset.sum_filter_of_ne fun γ _ h => ?_).symm
        by_contra hn
        exact h (by unfold coef; rw [if_neg hn, norm_zero])
    _ ≤ ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := Finset.sum_le_sum hterm
    _ = C * P * ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ C * P * (C₀ * height V x ^ A₀) :=
        mul_le_mul_of_nonneg_left (hI x _ fun γ hγ => hKtop _ (Finset.mem_filter.1 hγ).2) (mul_nonneg hC hP)
    _ ≤ C * P * (max C₀ 0 * H ^ A₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hP)
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hx0 hxH _) (pow_nonneg hx0 _) (le_max_right _ _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_partialSums_bounded_compact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  first | exact @GlobalTheory.PoinAut.partialSum_bdd | exact GlobalTheory.PoinAut.partialSum_bdd | (intros; apply GlobalTheory.PoinAut.partialSum_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensorLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensorLeft
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

namespace GlobalTheory.SphGlobX

theorem loc_mem_KAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hK : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idem F v) (GlobalTheory.FinDecomp.idem_mul_self v) K ∈ GlobalTheory.InertSph.KAt σ W v := by
  have hfix : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.FinDecomp.idem F v • z = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, y, -, rfl⟩ := hz
      rw [smul_smul, GlobalTheory.FinDecomp.idem_mul_of_at ha]
    | zero => simp
    | add z z' _ _ h h' => rw [smul_add, h, h']
    | neg z _ h => rw [smul_neg, h]
  have hphi : ∀ (M : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idem F v) M *ᵥ z = M *ᵥ z := by
    intro M z hz
    have h1 : (1 - GlobalTheory.FinDecomp.idem F v) • z = 0 := by rw [sub_smul, one_smul, hfix z hz, sub_self]
    rw [GlobalTheory.FinDecomp.phi, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add,
      ← Matrix.mulVec_smul, hfix z hz]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · show u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc _ _ K) - 1) = 0
    rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.phi_sub_one, smul_smul, GlobalTheory.FinDecomp.mul_idem_of_evFin hu, zero_smul]
  · rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.mat_loc_inv, hphi _ z hz, hphi _ z hz]
    exact hK z hz


open scoped Classical in
theorem ev_mem_adm' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, GlobalTheory.WeilM.pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem fixes_pure_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    (∀ v ∉ S, ∀ k ∈ GlobalTheory.InertSph.KAt σ X v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP S hAct k hinf hS hlat f φ hSB hφ
  have hM := hP.good
  have hw := hP.weil
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hM.std, S.finite_toSet.eventually_cofinite_notMem] with w hw hwS
    rw [hφ w hwS, hw]
  set Φ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ with hΦ
  have hloc : ∀ v, v ∉ S → ∀ h ∈ GlobalTheory.InertSph.KAt σ X v, om (h, 1) Φ = Φ := by
    intro v hv h hh
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have e1 : Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r := by rw [hΦ, hrt, Function.update_eq_self]
    have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (φ v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hA := hAct v hv h hh
    rw [← hφ v hv] at hA
    rw [e1, hA r hRest]
  have hcut : ∀ v, v ∉ S → loc (idem F v) (idem_mul_self v) k ∈ GlobalTheory.InertSph.KAt σ X v :=
    fun v hv => loc_mem_KAt' σ X v k (hlat v hv)
  have hcutS : ∀ v ∈ S, loc (idem F v) (idem_mul_self v) k = 1 := by
    intro v hv
    apply ua_ext
    rw [mat_loc, mat_one, ← sub_eq_zero, phi_sub_one]
    exact hS v hv _ fun u hu => by rw [smul_eq_mul, mul_idem_of_evFin hu]
  have hone : ∀ v, om (loc (idem F v) (idem_mul_self v) k, 1) Φ = Φ := by
    intro v
    by_cases hv : v ∈ S
    · rw [hcutS v hv]; show om 1 Φ = Φ; rw [map_one]; rfl
    · exact hloc v hv _ (hcut v hv)
  have hlist : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
      om ((l.map fun v => loc (idem F v) (idem_mul_self v) k).prod, 1) Φ = Φ := by
    intro l
    induction l with
    | nil => show om 1 Φ = Φ; rw [map_one]; rfl
    | cons v t ih =>
      rw [List.map_cons, List.prod_cons]
      have : (loc (idem F v) (idem_mul_self v) k * (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod,
          (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) =
          (loc (idem F v) (idem_mul_self v) k, 1) * ((t.map fun v => loc (idem F v) (idem_mul_self v) k).prod, 1) := by
        simp
      rw [this, map_mul, Module.End.mul_apply, ih, hone]
  have hT : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ = Φ := by
    intro T
    have e : loc (idemS F T) (idemS_mul_self T) k = (T.toList.map fun v => loc (idem F v) (idem_mul_self v) k).prod := by
      apply ua_ext
      rw [mat_prod_loc k _ T.nodup_toList, Finset.toList_toFinset, mat_loc]
    rw [e]; exact hlist _
  have hcont := hw.2.2
  have hΦA : Φ ∈ (GlobalTheory.WeilM.adeleClass F).sp (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  funext x
  have hc := hcont _ (ev_mem_adm' x) Φ hΦA
  have ht : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (loc (idemS F T) (idemS_mul_self T) k, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J))) Filter.atTop (nhds (k, 1)) :=
    (GlobalTheory.T.tendsto_unitaryGroupIdempotentLocalization_finiteSets F E σ n X.J k hinf).prodMk_nhds tendsto_const_nhds
  have hlim : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ))
      Filter.atTop (nhds ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (k, 1) Φ))) :=
    (hc.tendsto _).comp ht
  have hconst : (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ)) =
      fun _ => Φ x := by
    funext T; rw [hT T]; rfl
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end GlobalTheory.SphGlobX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeStabilizersFixVacuaFixesPureTensorLeftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    (∀ v ∉ S, ∀ k ∈ GlobalTheory.InertSph.KAt σ X v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  first | exact @GlobalTheory.SphGlobX.fixes_pure_left | exact GlobalTheory.SphGlobX.fixes_pure_left | (intros; apply GlobalTheory.SphGlobX.fixes_pure_left <;> assumption)
end
end
