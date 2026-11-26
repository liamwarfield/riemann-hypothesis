module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqUnitMulCentralTranslateLiftVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotSameRig

open GlobalTheory.Grid

variable {D : D7}

theorem heisO_smul {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaAt_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f f' : WO S T → ℂ} (ζ : ℂ) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h' : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) Φ f') : f' = ζ • f := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (ζ • f₀) (ζ • Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul]
      vac := by rw [LinearMap.smul_apply, hT.vac] }
  rw [h'.2 _ hT', hall Tm hT, LinearMap.smul_apply]

theorem isVacO_fixSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) :
    IsVacO ψ θ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, ⟨h.2.theta.quasi, h.2.theta.level, h.2.theta.cont, h.2.theta.smooth⟩, h.2.lat, h.2.fock, h.2.norm⟩

theorem setIntegral_eq_mul {V : HSp D} (ν₁ ν₂ : Measure (GA D V)) (fd₁ fd₂ : Set (GA D V)) (h₁ : ν₁.IsHaarMeasure)
    (h₂ : ν₂.IsHaarMeasure) (hfd₁ : IsFundamentalDomain (GQ V) fd₁ ν₁) (hfd₂ : IsFundamentalDomain (GQ V) fd₂ ν₂) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) →
      (IntegrableOn f fd₁ ν₁ ↔ IntegrableOn f fd₂ ν₂) ∧ ∫ g in fd₁, f g ∂ν₁ = c * ∫ g in fd₂, f g ∂ν₂ := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hc := Measure.isMulLeftInvariant_eq_smul ν₁ ν₂
  set c₀ : NNReal := Measure.haarScalarFactor ν₁ ν₂ with hc₀
  have hpos : 0 < c₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν₁ ν₂
  have hc0 : (c₀ : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hctop : (c₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsm : (c₀ • ν₂ : Measure (GA D V)) = (c₀ : ENNReal) • ν₂ := rfl
  have hfd₂' : IsFundamentalDomain (GQ V) fd₂ ν₁ := hfd₂.mono (by rw [hc, hsm]; exact Measure.smul_absolutelyContinuous)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hpos.ne', fun f hf => ?_⟩
  have hf' : ∀ (g : GQ V) (x : GA D V), f (g • x) = f x := fun g x => hf g g.2 x
  constructor
  · rw [hfd₁.integrableOn_iff hfd₂' hf', hc, hsm, IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hctop]
    rfl
  · rw [hfd₁.setIntegral_eq hfd₂' hf', hc, hsm, Measure.restrict_smul, integral_smul_measure]
    simp [Complex.real_smul]


set_option maxHeartbeats 1000000 in
theorem const_of_sameRig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  intro D T L sc G W i j A A' WW X Y hX hY hA hA' hW c hc

  have hvX := hX.is.isVac
  have hvY := hY.is.isVac
  rw [← hA, ← hW] at hvY
  have hvX' := hX.is.isVac'
  have hvY' := hY.is.isVac'
  rw [← hA', ← hW] at hvY'
  have hψ : IsStdChar D W.ψ (-1) := hvX.1
  have hθ : IsInfFam W.θ := hvX.2.inf
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hcS' : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hX.is.rigA'.2.2 τ).1
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig (neg A))
    (Formalism.L2.Fam.ThC.fixSig WW) (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS hcT X.rA.Λ X.rW.Λ (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) hX.is.rigW.1 X.vac Y.vac (isVacO_fixSig hvX)
    (isVacO_fixSig hvY)
  obtain ⟨ζ', hζ1', hζ'⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hψ hθ (Formalism.L2.Fam.ThC.fixSig A')
    (Formalism.L2.Fam.ThC.fixSig WW) X.rA'.s X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _)
    hcS' hcT X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac' Y.vac' (isVacO_fixSig hvX') (isVacO_fixSig hvY')
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  have hζ0' : ζ' ≠ 0 := fun h => by rw [h, norm_zero] at hζ1'; exact zero_ne_one hζ1'

  have he : ∀ t, Y.e t = X.e t := fun t => GlobalTheory.BaseKernelUniq.idemSum_unique A (hY.is.idem t) (hX.is.idem t)
  have hid : ∀ t, Y.ideal (locPl G) t = X.ideal (locPl G) t := fun t => by
    unfold Tri.ideal
    exact Finset.prod_congr rfl fun w hw => by rw [(hY.is.expo t w hw).unique (hX.is.expo t w hw)]

  have hf : ∀ t, Y.f t = ζ • X.f t := fun t => by
    have h2 := hY.is.fst t
    rw [← hA, ← hW, he t, hid t, hζ] at h2
    exact thetaAt_smul (S := neg A) ζ (hX.is.fst t) h2
  have hf' : ∀ t, Y.f' t = ζ' • X.f' t := fun t => by
    have h2 := hY.is.snd t
    rw [← hA', ← hW, he t, hid t, hζ'] at h2
    exact thetaAt_smul ζ' (hX.is.snd t) h2

  have thX : ∀ t, IsThetaFunO W.ψ (neg A) WW (X.f t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.fst t) hvX.2.theta
  have thX' : ∀ t, IsThetaFunO W.ψ A' WW (X.f' t) := fun t =>
    GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ (hX.is.snd t) hvX'.2.theta

  have hk : ∀ t P h g, Y.ker W.ψ W.θ t P h g = ζ * X.ker W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have hWY : IsWeilDatumO W.ψ (neg A) WW _ _ ((Y.ω t).toSgn true) := hY.is.weil t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ (neg A) WW _ _ _ _ hWY hWX ((ofSgn true A).symm g, h) _ hF
    unfold Tri.ker
    rw [← hA, ← hW, hf t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show ((Y.ω t).toSgn true) ((ofSgn true A).symm g, h) (ζ • _) 0 =
      ζ * ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]
  have hk' : ∀ t P h g, Y.ker' W.ψ W.θ t P h g = ζ' * X.ker' W.ψ W.θ t P h g := by
    intro t P h g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have hWY : IsWeilDatumO W.ψ A' WW _ _ (Y.ω' t) := hY.is.weil' t
    have hu := GlobalTheory.WeilUniq.weilDatum_unique D W.ψ hψ A' WW _ _ _ _ hWY hWX (g, h) _ hF
    unfold Tri.ker'
    rw [← hA', ← hW, hf' t, Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul]
    show (Y.ω' t) (g, h) (ζ' • _) 0 = ζ' * (X.ω' t) (g, h) _ 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hu]

  have inv : ∀ t P h, ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) hψ hθ (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
      (thX t) P
    have hWX : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
    have e1 : (((ofSgn true A).symm (γ * g), h) : GA D (neg A) × GA D WW) =
        ((ofSgn true A).symm γ, 1) * ((ofSgn true A).symm g, h) := by simp
    show ((X.ω t).toSgn true) ((ofSgn true A).symm (γ * g), h) _ 0 = ((X.ω t).toSgn true) ((ofSgn true A).symm g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hWX.om_pres _ _ hF)
  have inv' : ∀ t P h, ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
    intro t P h γ hγ g
    have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := A') hψ hθ X.rA'.s X.rA'.B X.rW.s X.rW.B (thX' t) P
    have hWX : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
    have e1 : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
    show (X.ω' t) (γ * g, h) _ 0 = (X.ω' t) (g, h) _ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hWX.om_aut _ hγ 1 (one_mem _) _ (hWX.om_pres _ _ hF)

  obtain ⟨r, hr0, hr⟩ := setIntegral_eq_mul X.m Y.m X.fd Y.fd hX.is.meas.1 hY.is.meas.1 hX.is.meas.2 hY.is.meas.2
  obtain ⟨r', hr0', hr'⟩ := setIntegral_eq_mul X.m' Y.m' X.fd' Y.fd' hX.is.meas'.1 hY.is.meas'.1 hX.is.meas'.2
    hY.is.meas'.2
  have hYk : ∀ t P h, Y.ker W.ψ W.θ t P h = fun g => ζ * X.ker W.ψ W.θ t P h g := fun t P h => funext (hk t P h)
  have hYk' : ∀ t P h, Y.ker' W.ψ W.θ t P h = fun g => ζ' * X.ker' W.ψ W.θ t P h g := fun t P h => funext (hk' t P h)
  have hI : ∀ t P h, X.I W.ψ W.θ t P h = r * ζ⁻¹ * Y.I W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I, Tri.I, hYk, integral_const_mul, (hr _ (inv t P h)).2]
    field_simp
  have hI' : ∀ t P h, X.I' W.ψ W.θ t P h = r' * ζ'⁻¹ * Y.I' W.ψ W.θ t P h := fun t P h => by
    rw [Tri.I', Tri.I', hYk', integral_const_mul, (hr' _ (inv' t P h)).2]
    field_simp
  have hint : ∀ t P h, IntegrableOn (Y.ker W.ψ W.θ t P h) Y.fd Y.m → IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m :=
    fun t P h hi => by
      rw [hYk, IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0)] at hi
      exact (hr _ (inv t P h)).1.2 hi
  have hint' : ∀ t P h, IntegrableOn (Y.ker' W.ψ W.θ t P h) Y.fd' Y.m' →
      IntegrableOn (X.ker' W.ψ W.θ t P h) X.fd' X.m' := fun t P h hi => by
    rw [hYk', IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.2 hζ0')] at hi
    exact (hr' _ (inv' t P h)).1.2 hi

  set κ : ℂ := r * ζ⁻¹ * (r' * ζ'⁻¹)⁻¹ with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (mul_ne_zero hr0 (inv_ne_zero hζ0)) (inv_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')))
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := hc
  have hX1 : X.IsConst W.ψ W.θ fun t => κ * c t := by
    refine ⟨⟨t₁, mul_ne_zero hκ0 h₁⟩, P, P', fun t => ⟨fun h => ⟨hint t P h ((H t).1 h).1, hint' t P' h ((H t).1 h).2⟩,
      ?_, fun h => ?_⟩⟩
    · obtain ⟨h, hh⟩ := (H t).2.1
      refine ⟨h, ?_⟩
      rw [hI']
      exact mul_ne_zero (mul_ne_zero hr0' (inv_ne_zero hζ0')) hh
    · have e := (H t).2.2 h
      have e' : Y.I' W.ψ W.θ t P' h = (r' * ζ'⁻¹)⁻¹ * X.I' W.ψ W.θ t P' h := by
        rw [hI', ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hr0' (inv_ne_zero hζ0')), one_mul]
      rw [hI, e, e', hκ]
      ring
  have := GlobalTheory.BotTransfer.isConst_smul hX1 (inv_ne_zero hκ0)
  simpa only [← mul_assoc, inv_mul_cancel₀ hκ0, one_mul] using this

end GlobalTheory.BotSameRig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    X.rA = Y.rA → X.rA' = Y.rA' → X.rW = Y.rW → ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → X.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.BotSameRig.const_of_sameRig | exact GlobalTheory.BotSameRig.const_of_sameRig | (intros; apply GlobalTheory.BotSameRig.const_of_sameRig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePart
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.PartFlat

open GlobalTheory.BaseCmp GlobalTheory.OnCmp Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas

theorem idem_mul_of_subset {D : D7} {P Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) (h : P ⊆ Q) : idem Q * idem P = idem P := by
  have k : ∀ l ∈ Q, idemAt l * idem Q = idemAt l := fun l hl =>
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hl
  conv_lhs => rw [show idem P = ∑ PP ∈ P, idemAt PP from rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l hl => by rw [mul_comm, k l (h hl)]

theorem isHalf_mono {D : D7} {m n : ℕ} {a b : AE D} (hab : b * a = a) {u : Mx D m n} (hu : IsHalf a u) : IsHalf b u := by
  intro k l
  rw [← hu k l, ← mul_assoc, hab]

theorem suppAt_mono {D : D7} {V : HSp D} {a b : AE D} (hab : b * a = a) (ha : a * cA D a = 0) (hb : b * cA D b = 0)
    {g : GA D V} (hg : SuppAt a V g) : SuppAt b V g := by
  intro k l
  have hc : cA D b * cA D a = cA D a := by rw [← map_mul, hab]
  have h1 : b * cA D a = 0 := by rw [← hc, ← mul_assoc, hb, zero_mul]
  have h2 : cA D b * a = 0 := by rw [← hab, ← mul_assoc, mul_comm (cA D b), hb, zero_mul]
  have e : (b + cA D b) * (a + cA D a) = a + cA D a := by linear_combination hab + hc + h1 + h2
  rw [← hg k l, ← mul_assoc, e]


open GlobalTheory.ChiUnit GlobalTheory.DilChi in
theorem chi_unitOff_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (i : Fin D.R.m) (t : T0) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eQ : AE D) (heQ : IsIdemSum eQ Q) (ϖ : 𝓞 D.host.E)
    (hϖ0 : (ϖ : D.host.E) ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) (z : GA D (Vc D i))
    (hz : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ))) (x : (AE D)ˣ) (hx : IsDetAt (cA D eQ) (Vc D i) z x) :
    UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  have hchr := hK.chr
  have hfin := hK.fin
  have hpl := fun P (hP : P ∈ Q) => hK.pl P (hQ hP)
  generalize R.xi t = χ at hchr ⊢
  generalize R.xiH t = ξ at hchr hfin
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hs0 with hu
  have hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E) := by
    rw [detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]; rfl
  have hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ →
      ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank := by
    intro c ψ hc
    rw [GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
  have e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [e, hval _ _ (hlev.mu0 i), hval _ _ hchr, hval _ _ hlev.eta]
  have hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2 := fun P hP =>
    ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩
  have hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P) := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hpl P hP
    have hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
      rw [natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr (conjPl P) fun k hk =>
      not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk
  have hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E) := by rw [Formalism.L2.DIV.starO_coe]; rfl
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hfin
  refine unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)
    (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))
  · rw [locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    have h := LR ξ n hnx (conjPl P) u
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr (conjPl P)) (hNc P hP)

theorem splitSet_tuple {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (i : Fin D.R.m) (t : T0) : SplitSet (R.Q t) := by
  obtain ⟨-, e, he, -⟩ := (kerDat_tuple (i := i) hC.lev hC.thP t).vec
  exact SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)

theorem dil_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hQG : QGuard R) (i : Fin D.R.m) (t : T0) (hV : VStd D i) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ) (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ) (heg : IsIdemSum eg R.Pg)
    (heQ : IsIdemSum eQ Q) (hfg : IsTypeVec R i eg fg) (ϖ : 𝓞 D.host.E)
    (hϖ0 : (ϖ : D.host.E) ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) (z : GA D (Vc D i))
    (hz : mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) +
      (1 - eQ - cA D eQ))) :
    SuppAt eQ (Vc D i) z ∧ ∃ κ : ℂ, UnitOff N κ ∧ ∀ Tm, IsModel R i eQ fg Tm → ∀ Ψ : WO (Vc D i) (Wc D i) → ℂ,
      IsSBHalf eQ (lattice₂ R i) Ψ → R.ωP i t (z, 1) (Tm Ψ) = κ • Tm (fun x => Ψ (dil i (ϖ : D.host.E)⁻¹ x)) := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  have hsp := splitSet_tuple hC i t
  have hsub : idem (R.Q t) * eQ = eQ := by rw [← idem_eq heQ]; exact idem_mul_of_subset hsp hQ
  have hsubc : cA D (idem (R.Q t)) * cA D eQ = cA D eQ := by rw [← map_mul, hsub]
  obtain ⟨hSV, hSW, hθ, hfix0⟩ := GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed D G Pl0 T0 A Ks R F hC hQG i hV _ _ _ _ _ _ hK ⟨t, subset_rfl⟩ eg
    (idem (R.Q t)) fg heg hsp.isIdemSum hfg
  have hfix : ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) →
      heisO R.ψ (Vc D i) (Wc D i) u fg = fg := fun u hu h =>
    hfix0 u hu (h.imp (isHalf_mono hsub) (isHalf_mono hsubc))
  have hW := hK.weil
  obtain ⟨hsupp, ⟨x, hx⟩, hpull, hsb, hlat⟩ :=
    GlobalTheory.T.scalarDilationElement_support_det_pullback D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  obtain ⟨Rr, hR1, hR2, hR3, hRc⟩ :=
    GlobalTheory.T.exists_conjHalf_cosetReps_scalarDilation D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ N hN hNQ ϖ hϖ0 hϖ z hz
  have hchi := chi_unitOff_part hC i t Q hQ N hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  refine ⟨hsupp, (((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ), unitOff_mul' hchi hRc, fun Tm hTm Ψ hΨ => ?_⟩
  have hom := GlobalTheory.T.weilOperator_idempotentSum_vacuum_normalised_sum D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z x hsupp hx Rr hR1 hR2 hR3
    fg hθ hfix
  have hsum := GlobalTheory.T.sum_heisenbergTranslates_baseVector_eq_card_smul D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ z hlat Rr hR1 hR2 hR3 fg Tm hTm
  have hvac : R.ωP i t (z, 1) fg = (((((Lift.chrTh (Lift.tup R.mu0 (R.xi t)) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ *
      ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ)) •
      Tm (actPull (z, (1 : GA D (Wc D i))) (halfInd eQ (latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i)))) := by
    rw [hom, hsum, smul_smul]
    congr 1
    have hs : ((Rr.card : ℕ) : ℂ) = ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    rw [hs]
    simp only [splitFacO, map_one, mul_one, Circle.coe_mul, Circle.coe_inv]
    by_cases h0 : ((Real.sqrt (Rr.card : ℝ) : ℝ) : ℂ) = 0
    · rw [h0]; simp
    · field_simp
  have h := GlobalTheory.T.weilRep_apply_eq_smul_of_halfIndicator_base D R.ψ (Vc D i) (Wc D i) _ _ _ hW (R.ΛV i) (R.ΛW i) hSV hSW Q eQ heQ fg hθ hfix Tm hTm (z, 1) _ hsb hvac
    Ψ hΨ
  rw [h, hpull Ψ hΨ.1]

theorem lift_part {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hG : QGuard R) (i : Fin D.R.m) (t : T0) (hV : VStd D i) (Q : Finset (Pl D.host.E)) (hQ : Q ⊆ R.Q t) (N : ℕ) (hN : N ≠ 0)
    (hNQ : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) (eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ)
    (hq : IsIdemSum eQ Q) (ϖ : 𝓞 D.host.E) (hϖ0 : ϖ ≠ 0) (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) ∧
      ∀ Tm, IsModel R i eQ fg Tm → ∀ φ, ThAt R i (cA D eQ) fg (adjDat R i Q (R.xiR t) (cA D eQ)) φ →
        φ = Tm (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) := by
  have hK := kerDat_tuple (i := i) hC.lev hC.thP t
  obtain ⟨Y, a, Gc, hU, hY, hΦ, hS⟩ := GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum D G Pl0 T0 A Ks R F hC hG i hV (R.xiR t) Q ⟨t, hQ⟩
    (fun PP hP => kerDat_xiR_ne D G Pl0 T0 A Ks R F hC i _ _ _ _ _ _ hK PP (hQ hP)) N hN hNQ eQ hq ϖ hϖ0 hϖ
  refine ⟨Gc, hU, GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel D G Pl0 T0 A Ks R F hC hG i hV (R.xiR t) Q ⟨t, hQ⟩ eQ hq ϖ hϖ0 hϖ Gc, fun Tm hTm φ hθ => ?_⟩
  have h1 := GlobalTheory.DatumFourier.thetaAt_eq_sum (fun q : Y => q.1) (fun q : Y => a q.1) hθ
    (fun q => by rw [GlobalTheory.LatVac.cA_cA]; exact hY q.1 q.2)
    (fun s => by
      refine (hΦ s).trans ?_
      congr 1; exact (Finset.sum_coe_sort Y fun y => a y * R.ψ (symplO (Vc D i) (Wc D i) s y)).symm)
  have h2 : (fun x => Gc * flatDat R i Q (R.xiR t) eQ (dil i (ϖ : D.host.E) x)) =
      ∑ y ∈ Y, a y • fun s => halfInd eQ (lattice₂ R i) (s + y) := by
    funext s
    rw [← hS s, Finset.sum_apply]
    rfl
  have hvac : Tm (halfInd eQ (lattice₂ R i)) = fg := by simpa using hTm.vac
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, h2, map_sum, ← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.trans _ (GlobalTheory.isSBHalf_halfInd eQ (lattice₂ R i)) _ (hY q.1 q.2), hvac]

theorem flat_eq_unit_smul_om_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa : Finset (Pl D.host.E)), Sa ⊆ R.Q t → ∀ (eg ea : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt ea (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ h g, ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i Sa (R.xiR t) ea) h → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) g → h = c • R.ωP i t (z⁻¹, 1) g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV Sa hSa eg ea fg heg hea hfg
  obtain ⟨ϖ, hϖ0, hϖ⟩ := GlobalTheory.FlatLift.exists_unif D.host.E Sa
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, -, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i Sa ea hea (ϖ : D.host.E) hϖE
  have hN : GlobalTheory.TwistField.tupPrime R t ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact GlobalTheory.TupDil.card_ne_zero PP
  have hNQ : ∀ PP ∈ Sa, ((GlobalTheory.TwistField.tupPrime R t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨c, hc⟩ : Nat.card (kP PP) ∣ GlobalTheory.TwistField.tupPrime R t :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) (hSa hPP))
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.TupDil.card_mem PP)
  obtain ⟨hsupp, κ, hκ, hact⟩ := dil_part hC hQG i t hV Sa hSa _ hN hNQ eg ea fg heg hea hfg ϖ hϖE hϖ z hzm
  obtain ⟨Gc, hG, hSB, hvP⟩ := lift_part hC hQG i t hV Sa hSa _ hN hNQ ea fg hea ϖ hϖ0 hϖ
  have hsp := splitSet_tuple hC i t
  have hsub : idem (R.Q t) * ea = ea := by rw [← idem_eq hea]; exact idem_mul_of_subset hsp hSa
  have hsi := GlobalTheory.SplitHecke.Stab.suppAt_inv hsupp
  refine ⟨z⁻¹, (κ * Gc)⁻¹, hsi, suppAt_mono hsub hea.2 hsp.isIdemSum.2 hsi, GlobalTheory.FlatLift.unitOff_inv_mul hκ hG,
    fun h g hh hg => ?_⟩
  obtain ⟨Tm, hTm⟩ := hh.1
  have hfT := hh.2 Tm hTm
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    ext a b
    simp only [dil, Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  rw [inv_inv, hvP Tm hTm g hg, hact Tm hTm _ hSB]
  simp only [hcomp]
  have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * flatDat R i Sa (R.xiR t) ea x) = Gc • flatDat R i Sa (R.xiR t) ea := rfl
  rw [hsm, map_smul, ← hfT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.PartFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePartStatement
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatVector_eq_unit_smul_centralTranslate_placePart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa : Finset (Pl D.host.E)), Sa ⊆ R.Q t → ∀ (eg ea : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt ea (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ h g, ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i Sa (R.xiR t) ea) h → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) g → h = c • R.ωP i t (z⁻¹, 1) g := by
  first | exact @GlobalTheory.PartFlat.flat_eq_unit_smul_om_part | exact GlobalTheory.PartFlat.flat_eq_unit_smul_om_part | (intros; apply GlobalTheory.PartFlat.flat_eq_unit_smul_om_part <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMemSchwartzBruhatOfConductorExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMemSchwartzBruhatOfConductorExponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.StdPairSBDepth

open GlobalTheory.StdPairSB GlobalTheory.StdPairCone ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gfun_eq_mul (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c : ℕ) {m r : ℕ} (A : Matrix (Fin m) (Fin m) k)
    (B : Matrix (Fin m) (Fin r) k) :
    gfun ν ϖ c A B = gfun ν ϖ n A (0 : Matrix (Fin m) (Fin r) k) * gfun 1 ϖ c A B := by
  have h0 : ∀ (i : Fin m) (j : Fin r),
      (0 : Matrix (Fin m) (Fin r) k) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ n) := by
    intro i j
    simp [GlobalTheory.SplitWeil.cball]
  unfold gfun
  by_cases h : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left ⟨h.1, h.2.1, h0⟩]
    simp
  · rw [dite_eq_right h, dite_eq_right h, mul_zero]

theorem isLocallyConstant_gfun' {ν : kˣ →* ℂˣ} {ϖ : kˣ} {n : ℕ} (c : ℕ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  have h1 := (isLocallyConstant_gfun hϖ hν m r).comp_continuous
    (f := fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
      (q.1, (0 : Matrix (Fin m) (Fin r) k))) (continuous_fst.prodMk continuous_const)
  have h2 := isLocallyConstant_gfun (ν := (1 : kˣ →* ℂˣ)) (c := c) hϖ (fun _ _ => rfl) m r
  have h3 := h1.mul h2
  convert h3 using 1
  funext q
  exact gfun_eq_mul ν ϖ n c q.1 q.2

end GlobalTheory.StdPairSBDepth


open GlobalTheory.StdPairCone ValuativeRel in
theorem GlobalTheory.StdPairSBDepth.stdPair_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c a a' : ℕ), IsUnif ϖ → CondLE ϖ n ν →
      GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ n c a a' hϖ hν
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSBDepth.isLocallyConstant_gfun' c hϖ hν a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSBDepth.isLocallyConstant_gfun' c hϖ hν a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMemSchwartzBruhatOfConductorExponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPair_mem_schwartzBruhat_of_conductorExponentLE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c a a' : ℕ), IsUnif ϖ → CondLE ϖ n ν →
      GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  first | exact @GlobalTheory.StdPairSBDepth.stdPair_mem_SB | exact GlobalTheory.StdPairSBDepth.stdPair_mem_SB | (intros; apply GlobalTheory.StdPairSBDepth.stdPair_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuaScalarMultiplesReferenceTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuaScalarMultiplesReferenceTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotScal

open GlobalTheory.KappaArith (AwayIm)

variable {D : D7} {T : Type} {Lc : LevCh D T}

theorem xi_awayIm_of_infPart {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ)
    (hu : infPart D (u : AE D) = 1) : AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3)
    (Lc.xi t) (Lc.xiH t) (hL.xi t)
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom u)
  rw [hprod u hu S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact AwayIm.prod _ _ fun P _ => GlobalTheory.KappaArith.awayIm_val hL hx m P (Formalism.L2.Host.atFin P (k P))

theorem xi_awayIm {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ) :
    AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨v, hv1, hv2, hv3⟩ := GlobalTheory.TameFinitePart.exists_lift D (Units.map (finPart D).toMonoidHom u)
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have h1 : Lc.xi t (u * v⁻¹) = 1 := GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (by
    rw [Units.val_mul, map_mul, hv3]
    exact Units.mul_inv (Units.map (finPart D).toMonoidHom u))
  have h2 : Lc.xi t u = Lc.xi t v := by
    have := congrArg (· * Lc.xi t v) h1
    simpa [map_mul, map_inv] using this
  rw [h2]
  exact xi_awayIm_of_infPart hL hx m v hv1

end GlobalTheory.BotScal

namespace GlobalTheory.BotScal

theorem moved_vacua_scal : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (Y : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    ∃ r r' : T → ℂ, (∀ t, r t ≠ 0 ∧ r' t ≠ 0) ∧ (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω μ₀ (g, h) Y.vac) ∧
      (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' μ₀ (g', h) Y.vac') ∧
      ∀ t, ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ r' t / r t = D.what₂.embLL ζ * (r' μ₀ / r μ₀) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW Y hY g hg g' hg' h hh
  have hI := hY.2.2.2.2.2.2.2
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (GlobalTheory.Grid.neg A) ((GlobalTheory.Grid.ofSgn true A).symm g)
  obtain ⟨x', hx'⟩ := GlobalTheory.RecDict.exists_isDetRoot D A' g'
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D WW h
  have hvac : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW Y.vac := hI.isVac.2.theta
  have hvac' : IsThetaFunO W.ψ A' WW Y.vac' := hI.isVac'.2.theta
  have e := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ (GlobalTheory.Grid.neg A) WW _ _ _ _ _ _ (hI.weil μ₀) (hI.weil t) _ h x y hx hy _ hvac
  have e' := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ A' WW _ _ _ _ _ _ (hI.weil' μ₀) (hI.weil' t) g' h x' y hx' hy _ hvac'
  let a : T → (AE D)ˣ →* Circle := fun t => Lc.mu t (↑j + 1) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  let b : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - ↑i) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  refine ⟨fun t => ((splitFacO b (b / a t) x y : Circle) : ℂ) * ((splitFacO b (b / a μ₀) x y : Circle) : ℂ)⁻¹,
    fun t => ((splitFacO (a t) (a t / b) x' y : Circle) : ℂ) * ((splitFacO (a μ₀) (a μ₀ / b) x' y : Circle) : ℂ)⁻¹,
    fun t => ⟨?_, ?_⟩, fun t => ?_, fun t => ?_, ?_⟩
  rotate_left 2
  · have := e t
    simp only [GlobalTheory.Grid.WRep.toSgn, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MonoidHom.id_apply] at this
    exact this
  · exact e' t
  · intro t
    have hb : Lc.xi μ₀ = 1 := MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ₀))
    obtain ⟨ζ, hζ, hζe⟩ := xi_awayIm hL (hN.chars.xi t) (Qn G t) (x'⁻¹ * y * x⁻¹)
    refine ⟨ζ, hζ, ?_⟩
    rw [hζe]
    simp only [splitFacO, a, b, LevCh.mu, Formalism.IndefR.Lift.tup, hb, Circle.coe_mul, Circle.coe_inv, MonoidHom.div_apply,
      MonoidHom.mul_apply, MonoidHom.one_apply, map_mul, map_inv, Circle.coe_div, mul_one]
    field_simp [Circle.coe_ne_zero]
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

end GlobalTheory.BotScal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuaScalarMultiplesReferenceTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_vacua_scalar_multiples_reference_tuple : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (Y : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    ∃ r r' : T → ℂ, (∀ t, r t ≠ 0 ∧ r' t ≠ 0) ∧ (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω μ₀ (g, h) Y.vac) ∧
      (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' μ₀ (g', h) Y.vac') ∧
      ∀ t, ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ r' t / r t = D.what₂.embLL ζ * (r' μ₀ / r μ₀) := by
  first | exact @GlobalTheory.BotScal.moved_vacua_scal | exact GlobalTheory.BotScal.moved_vacua_scal | (intros; apply GlobalTheory.BotScal.moved_vacua_scal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossLeAddCharNegUnfoldingPhase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossLeAddCharNegUnfoldingPhase
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem isOfFinOrder_of_hasConductor {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) (a : k) : IsOfFinOrder (ψ a) := by
  have hn : ∀ n : ℕ, valuation k (n : k) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (valuation k).map_add_le ih (by simp)

  have hc : ∀ y : k, valuation k y ≤ valuation k (c : k) → ψ y = 1 := (h c).2 le_rfl
  have hc0 : valuation k (c : k) ≠ 0 := by simp
  set γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hc0 with hγ

  obtain ⟨t, -, ht⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k a)).elim_nhds_subcover
    (fun x => {z | valuation k (z - x) < γ}) (fun x _ => by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨γ, subset_rfl⟩)
  have hmem : ∀ n : ℕ, ∃ x : t, valuation k ((n : k) * a - x) < γ := by
    intro n
    have : (n : k) * a ∈ {x | valuation k x ≤ valuation k a} := by
      simp only [Set.mem_ofPred_eq, map_mul]
      calc valuation k (n : k) * valuation k a ≤ 1 * valuation k a := by gcongr; exact hn n
        _ = valuation k a := one_mul _
    obtain ⟨x, hx⟩ := Set.mem_iUnion₂.mp (ht this)
    exact ⟨⟨x, hx.1⟩, hx.2⟩
  choose f hf using hmem

  obtain ⟨n, m, hnm, hfnm⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hdiff : valuation k ((n : k) * a - (m : k) * a) ≤ valuation k (c : k) := by
    have h1 := hf n
    have h2 := hf m
    rw [hfnm] at h1
    have : (n : k) * a - (m : k) * a = ((n : k) * a - (f m : k)) - ((m : k) * a - (f m : k)) := by ring
    rw [this]
    refine le_of_lt ?_
    calc valuation k (((n : k) * a - (f m : k)) - ((m : k) * a - (f m : k)))
        ≤ max (valuation k ((n : k) * a - (f m : k))) (valuation k ((m : k) * a - (f m : k))) :=
          (valuation k).map_sub _ _
      _ < γ := max_lt h1 h2
  have hpow : ψ a ^ n = ψ a ^ m := by
    have := hc _ hdiff
    rw [AddChar.map_sub_eq_div, div_eq_one, ← nsmul_eq_mul, ← nsmul_eq_mul,
      AddChar.map_nsmul_eq_pow, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [isOfFinOrder_iff_pow_eq_one]
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hlt
  · refine ⟨m - n, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [pow_sub _ hlt.le, ← hpow, mul_inv_cancel]
  · refine ⟨n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [pow_sub _ hlt.le, hpow, mul_inv_cancel]

theorem lossLe_psi_neg_phase : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t), ∀ X Y (e : Vars (locGrid ch.G t P)),
    (ch.S.term t Φ β P).datum X Y ≠ 0 →
    moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) (fill one_le_sLen X Y e) ≠ 0 →
    ∀ w : PlL D, LossLe w ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) 0 := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hIs _ hF t Φ β hβ P X Y e hd hm w

  obtain ⟨y, hy⟩ := hF.phases t Φ β hβ P X Y e hd hm

  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    GlobalTheory.FunObj.Good.hasConductor_psiAt ch.W
      (GlobalTheory.FunObj.Good.badInt_notMem hS.core.lev (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS) (hIs.guard t) P.2)
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_hasConductor hcond (-phase X e))
  have hneg : ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) = D.what₂.embLL y⁻¹ := by
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv, map_inv₀, hy]
  refine ⟨y⁻¹, hneg.symm, Or.inr ?_⟩
  have hroot : y⁻¹ ^ n = 1 := by
    apply D.what₂.embLL.injective
    rw [map_pow, ← hneg, ← Circle.coe_pow, hpow, Circle.coe_one, map_one]
  have h0 : (n : ℤ) * Formalism.DivisionValues.vw w y⁻¹ = 0 := by
    unfold Formalism.DivisionValues.vw
    rw [← FractionalIdeal.count_pow, FractionalIdeal.spanSingleton_pow, hroot,
      FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  have hv : Formalism.DivisionValues.vw w y⁻¹ = 0 := (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hn.ne')
  simp [hv]

end GlobalTheory.UnfoldLoss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossLeAddCharNegUnfoldingPhaseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffValuationLossLe_addChar_neg_unfoldingPhase : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t), ∀ X Y (e : Vars (locGrid ch.G t P)),
    (ch.S.term t Φ β P).datum X Y ≠ 0 →
    moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) (fill one_le_sLen X Y e) ≠ 0 →
    ∀ w : PlL D, LossLe w ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) 0 := by
  first | exact @GlobalTheory.UnfoldLoss.lossLe_psi_neg_phase | exact GlobalTheory.UnfoldLoss.lossLe_psi_neg_phase | (intros; apply GlobalTheory.UnfoldLoss.lossLe_psi_neg_phase <;> assumption)
end
end
