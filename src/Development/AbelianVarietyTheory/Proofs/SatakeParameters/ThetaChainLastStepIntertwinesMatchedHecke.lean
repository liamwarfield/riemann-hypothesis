module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.Hk3.StepX

variable {D : D7}

theorem gram_posDef_X (τ : D.what₂.Tau) : (gramAt D D.sp.X' τ).PosDef := by
  have := D.sp.X'_sig (tauE D τ)
  rw [D7.X'_posDef D] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem lift_symm_comp {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (x : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) :
    PiTensorProduct.lift.symm (L ∘ₗ x) = postOn M L (PiTensorProduct.lift.symm x) := by
  refine MultilinearMap.ext fun v => ?_
  rw [postOn_apply]
  simp [PiTensorProduct.lift_symm]

theorem integ_X {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {f : WO S D.sp.X' → ℂ} (hf : IsThetaFunO ψ S D.sp.X' f)
    (Φ : GA D D.sp.X' → ℂ) (hΦc : Continuous Φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ h, Φ (γ * h) = Φ h)
    (ν : Measure (GA D D.sp.X')) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D D.sp.X'))
    (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (g : GA D S) (y : GA D D.sp.X') :
    IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν := by
  have : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  have : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact D.sp.X' gram_posDef_X
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ D.sp.X') C hC (fun h => ?_) ν hν 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · exact ((hW.om_cont f hf 0).comp (Continuous.prodMk_right g)).mul (hΦc.comp (continuous_mul_const y))
  · intro γ hγ h
    have h1 := (GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S D.sp.X' χS χT om hW f hf).1 1 (one_mem _) γ hγ g h
    rw [one_mul] at h1
    show thetaKO om g (γ * h) f * Φ (γ * h * y) = thetaKO om g h f * Φ (h * y)
    rw [h1, mul_assoc, hl γ hγ]

theorem hyp_inv {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) :
    ∀ k ∈ hyp V P, ∀ h, c.ext f (h * k) = c.ext f h := by
  obtain ⟨n, hB⟩ := hβ
  have hlev := (GlobalTheory.LevOp.level_operators V β Λ _ (flag1L L) hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP).1
  exact fun k hk h => GlobalTheory.DefLiftHecke.ext_level c hc hf (hlev k hk).1 (hlev k hk).2 h

theorem mult_stable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsSDFrame V β Λ N) {L : LevDat D.host.E ℂ V.rank} {P : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) (c : List ℤ →₀ ℂ) {U : MMap M}
    (hU : U ∈ Mult θ M (levS V β L) (levChi V β L)) : postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  obtain ⟨n, hB⟩ := hβ
  have hN' : ((N ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
    hN (P.isPrime.mem_of_pow_mem n (by rwa [Nat.cast_pow] at h'))
  exact (GlobalTheory.LevOp.level_operators V β Λ _ L hB P hN' hP).2.2.2.2 S θ M c hθ U hU

theorem toMap_hkF {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (P : Pl D.host.E) (z : List ℤ →₀ ℂ) (f : Bridge.Gf V → c.W) (w : Dm) :
    c.toMap pr (hkF V P z f) w = hk V P z (c.toMap pr f w) := by
  funext h
  show pr (c.ext (hkF V P z f) h) w = _
  rw [GlobalTheory.DefLiftHecke.ext_hkF c hc, GlobalTheory.ThetaIntHecke.hk_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl


set_option maxHeartbeats 2000000 in
theorem liftInt_toMap_hk {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)} {P : Pl D.host.E}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {ν : Measure (GA D D.sp.X')} {𝓕 : Set (GA D D.sp.X')}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (hfix : VacFix ψ om P)
    (cS cX : List ℤ →₀ ℂ) (hM : Match ψ om P cS (dualC cX)) {f0 : WO S D.sp.X' → ℂ} (hf0 : IsVacAt ψ S D.sp.X' P f0)
    (c : CoefA D.sp.X') (hc : c.Is) {β : GL (Fin D.sp.X'.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (hβ : IsSDFrame D.sp.X' β Λ 1)
    {L : LevDat D.host.E ℂ D.sp.X'.rank} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) {f : Bridge.Gf D.sp.X' → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') c.coef.ρ (levEnv _ β L).J (levEnv _ β L).χ) (w : Dm) :
    Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr (hkF D.sp.X' P cX f) w) =
      hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr f w)) := by
  have he : c.toMap pr f w = (pr.flip w) ∘ c.ext f := rfl
  have hlev := hyp_inv c hc hβ hP hf
  have hcont : Continuous (c.toMap pr f w) := by
    rw [he]
    exact (LinearMap.continuous_of_finiteDimensional (pr.flip w)).comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf)
  have hl : ∀ γ ∈ GQ D.sp.X', ∀ h, c.toMap pr f w (γ * h) = c.toMap pr f w h := fun γ hγ h => by
    rw [he, Function.comp_apply, Function.comp_apply, GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ h]
  have hr : ∀ k ∈ hyp D.sp.X' P, ∀ h, c.toMap pr f w (h * k) = c.toMap pr f w h := fun k hk h => by
    rw [he, Function.comp_apply, Function.comp_apply, hlev k hk h]
  rw [toMap_hkF c hc pr]
  exact GlobalTheory.ThetaIntHecke.liftInt_hk ψ S D.sp.X' χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cX hM f0 hf0 _ hl hr
    (fun g z _ => integ_X hW hf0.1 _ hcont hl ν hν 𝓕 h𝓕 g z)

theorem sub_comp_apply {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (x : M) (h : u' x = H (u x)) : (u' - H ∘ₗ u) x = 0 := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, h, sub_self]

theorem eq_of_sub_comp {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (h : u' - H ∘ₗ u = 0) (x : M) : u' x = H (u x) := by
  have := congrArg (fun L => L x) h
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 2000000 in
theorem at_It (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωX t) P) (cS cX : List ℤ →₀ ℂ) (hM : Match R.ψ (R.ωX t) P cS (dualC cX))
    (y y' : (R.HX t).H) (hy : (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y)) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank)
    (w : SmT R.MX) :
    (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) =
      hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w)) := by
  have hIo := hC.chain.ioX t
  have hν := hC.models.νX t
  have hmem : (R.HX t).e y ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ :=
    (hC.models.HX t).2.1.le (LinearMap.mem_range_self _ y)
  have k := liftInt_toMap_hk (hC.chain.ωX t) hν.1.1 hν.2 hfix cS cX hM ((GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hP).2.1 φ)
    R.cX hC.models.cX hC.lev.βX (L := R.datXt t) hP R.prX hmem w
  have e1 : (((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
      SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w = R.cX.toMap R.prX (hkF D.sp.X' P cX ((R.HX t).e y)) w :=
    congrArg (fun f => R.cX.toMap R.prX f w) hy
  have hyY : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ) (R.cX.toMap R.prX ((R.HX t).e y) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) φ w g'
  have hyY' : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)
      ((((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y') φ w g'
  exact hyY'.symm.trans ((congrArg (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)) e1).trans
    (k.trans (congrArg (hk _ P cS) hyY)))

end GlobalTheory.Hk3.StepX


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Hk3.StepX.stepX_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ t P, Good R t P → VacFix R.ψ (R.ωX t) P → ∀ cS cX, Match R.ψ (R.ωX t) P cS (dualC cX) → ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) → ∀ v, (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 v = hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t P hP hfix cS cX hM y y' hy
  have hm := D.R.two_le_m
  have hu : (hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1)) ∈ R.CC t (D.R.m - 1) := by
    rw [mem_multT, GlobalTheory.Hk3.StepX.lift_symm_comp]
    exact GlobalTheory.Hk3.StepX.mult_stable R.θ hC.models.inf (R.MY (D.R.m - 1)) (hC.lev.βY (D.R.m - 1) (by omega))
      (L := R.datYt t (D.R.m - 1) R.triv) ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).1 hP cS
      ((mem_multT _ _ _ _ _).1 (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).2)
  have hz := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY (D.R.m - 1)) _ _ (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1))
    hC.models.inf (hC.models.νY' t).1.1 (hC.models.νY' t).2 (hS.1 t (D.R.m - 1) (by omega))
    (((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1) - hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1))
    (sub_mem (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).2 hu)
  have hex : ∃ φ w, R.ItX φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact (hC.chain.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun w => hcon φ w)
  refine hex.elim fun φ0 hw0 => hw0.elim fun w0 hne => ?_
  have h0 := hz _ hne (GlobalTheory.Hk3.StepX.sub_comp_apply _ _ _ _ (GlobalTheory.Hk3.StepX.at_It R F hC t P hP hfix cS cX hM y y' hy φ0 w0))
  exact GlobalTheory.Hk3.StepX.eq_of_sub_comp _ _ _ h0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHeckeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ t P, Good R t P → VacFix R.ψ (R.ωX t) P → ∀ cS cX, Match R.ψ (R.ωX t) P cS (dualC cX) → ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) → ∀ v, (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 v = hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 v) := by
  first | exact @GlobalTheory.Hk3.StepX.stepX_hk | exact GlobalTheory.Hk3.StepX.stepX_hk | (intros; apply GlobalTheory.Hk3.StepX.stepX_hk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
namespace GlobalTheory.Cong.LevelExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_locU_iff {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) :
    x ∈ locU n w ↔ x ∈ finU (E := E) (n := n) ∧ ∀ u, Apart u w → cLoc u x = 1 := by
  unfold locU Apart
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem cLoc_conj_eq_one {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) (h1 : cLoc w x = 1) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_one, Matrix.one_mul] at hce
  exact Units.ext hce

theorem one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (x : UA E n) (h1 : cLoc w x = 1) :
    ∀ u, ¬ Apart u w → cLoc u x = 1 := by
  intro u hu
  have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    by_contra h
    exact hu h
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu' with rfl | rfl
  · exact h1
  · exact cLoc_conj_eq_one x h1

end GlobalTheory.Cong.LevelExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.SplitEigen

theorem exists_eigen_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible)
    (f : ι → U →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (c : G → ℂ) (φ : V) (h0 : φ ≠ 0)
    (hK : ∀ k ∈ K, ρ k φ = c k • φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - c k • v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add (f := _)] at h5
          have h6 : f i (σ k v - c k • v) = c k • x - ρ k x := by
            rw [map_sub, hf, map_smul]; rw [smul_add] at h5; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem (W.smul_mem _ hx) (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

theorem exists_locComp_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  classical
  intro E _ _ _ n U hU w hw J _ _ χ φ hφ h0 hχ
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨σ, -, hσ, -⟩ := GlobalTheory.DefU.exists_locComp_split E n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let p : locU n w →* GL (Fin n) (w.adicCompletion E) := (cLoc w).comp (locU n w).subtype
  have hp : p = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  let σ' : Representation ℂ (locU n w) σ.V := σ.ρ.comp p
  have hirr : σ'.IsIrreducible := by
    change Representation.IsIrreducible (σ.ρ.comp p); rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨-, f, hf0, hfm, hf⟩ := hσ
  let F : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hsup := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype
    σ' σ' π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
  let c : locU n w → ℂ := fun k => if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_mem_iSup (π.rep.comp (locU n w).subtype) σ' hirr
    (fun h : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
    (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
    {k | cLoc w (k : UA E n) ∈ J} c ⟨φ, hφ⟩
    (fun h => h0 (congrArg Subtype.val h))
    (fun k hk => Subtype.ext (by
      change RU E n (k : UA E n) φ = c k • φ
      show RU E n (k : UA E n) φ = (if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0) • φ
      have hk' : cLoc w (k : UA E n) ∈ J := hk
      rw [dif_pos hk']
      exact hχ _ k.2 hk'))
    (hsup ▸ Submodule.mem_top)
  refine ⟨v, hv0, fun g => ?_⟩
  have hk : cLoc w ((e.symm g : locU n w) : UA E n) ∈ J := by rw [hcl]; exact g.2
  have h1 := hv (e.symm g) hk
  have h2 : σ' (e.symm g) = σ.ρ g := by
    change σ.ρ (cLoc w ((e.symm g : locU n w) : UA E n)) = _
    rw [hcl]
  rw [h2] at h1
  rw [h1]
  simp only [c, dif_pos hk]
  congr 3
  exact Subtype.ext (hcl g)

end GlobalTheory.SplitEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlaceStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  first | (exact @GlobalTheory.SplitEigen.exists_locComp_eigen) | (exact GlobalTheory.SplitEigen.exists_locComp_eigen) | (intros; apply GlobalTheory.SplitEigen.exists_locComp_eigen  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlace
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.Cong

theorem exists_continuous_inv_cLoc {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ ι : GL (Fin n) (w₀.adicCompletion E) → GA E n, Continuous ι ∧ ι 1 = 1 ∧
      ∀ x : UA E n, x ∈ locU n w₀ → ι (cLoc w₀ x) = x.1 := by
  by_cases hsp : IsSplitAt w₀
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w₀ hsp
    refine ⟨fun h => ((e.symm h : locU n w₀) : UA E n).1,
      continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous), by simp, fun x hx => ?_⟩
    have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
      rw [← he ⟨x, hx⟩]
      exact e.symm_apply_apply _
    simp only [h1]
  · have hc0 : GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀ = w₀ := by
      by_contra hne
      exact hsp ⟨_, hne, GlobalTheory.DefU.LocRet.under_conjSrc w₀⟩
    have hw : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w₀ w₀ := by
      have h := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) w₀
      change GlobalTheory.Mem.Chr.ConjPl _ w₀ (GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀) at h
      rwa [hc0] at h
    refine ⟨fun h => finGL E n (locGL E n w₀ h),
      GlobalTheory.DefU.Inert.continuous_finGL.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w₀), by simp,
      fun x hx => GlobalTheory.DefU.Inert.finGL_cLoc hw ⟨x, hx⟩⟩

theorem exists_algForm_ofType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU (E := E) (n := n) → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  intro E _ _ _ n lam K U hK hU w₀
  classical
  let π : AutSub E n := ⟨U, hU.aut⟩
  set W := (AU.mk π).wt with hWdef
  have hWat : ∀ τ, W.at τ = lam τ := fun τ => by
    have h1 : (AU.mk π).HasWt τ (lam τ) := (AU.hasWt_mk π τ (lam τ)).2 (hU.wt τ)
    exact hasWeightAt_unique π τ ((AU.hasWt_mk π τ _).1 h1.wt) (hU.wt τ)
  let M := π.finPart W
  have hM0 : M ≠ ⊥ := AutSub.finPart_wt_ne_bot E n π
  have hV : π.V = Pairs.img (Pairs.jOf W M) := Pairs.V_eq_img π (Pairs.finPart_stable π W) hM0 le_rfl
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  haveI : Nontrivial W.Sp := (Pairs.nontrivial_of_ne_bot hM0).1
  let b := Module.finBasis ℂ W.Sp
  obtain ⟨c, hc⟩ : φ ∈ LinearMap.range (Pairs.total b (Pairs.jOf W M)) := by
    rw [Pairs.range_total, ← hV]
    exact hφU
  let Fx : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | ∀ k ∈ K, RU E n k ψ = ψ}
      add_mem' := fun {x y} hx hy k hk => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add (f := _), hx k hk, hy k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun r ψ h k hk => by
        simp only [Set.mem_setOf_eq] at h ⊢
        rw [map_smul, h k hk] }
  have hFx : ∀ x : infU E n, ∀ u ∈ Fx, RU E n x.1 u ∈ Fx := fun x u hu k hk => by
    change RU E n k (RU E n x.1 u) = RU E n x.1 u
    rw [RU_RU, fin_mul_inf (hK hk) x.2, ← RU_RU, hu k hk]
  have hcF : ∀ a v, Pairs.jOf W M (c a) v ∈ Fx := Pairs.coeff_mem (Pairs.span_rep W) (R := fun x => RU E n x.1)
    (Pairs.jOf_rep W M) hFx b (by rw [hc]; exact hφK)
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hφ0
    rw [← hc, Pairs.total_apply]
    simp [h]
  have hS : IsOpen {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} := isSmooth_algRep W (c a).1
  obtain ⟨ι, hι, hι1, hιx⟩ := exists_continuous_inv_cLoc n w₀
  have hS1 : {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} ∈ nhds (1 : finU (E := E) (n := n)) :=
    hS.mem_nhds (by
      show algRep W 1 (c a).1 = (c a).1
      rw [map_one]
      rfl)
  rw [nhds_subtype, Filter.mem_comap] at hS1
  obtain ⟨T1, hT1, hT1S⟩ := hS1
  rw [nhds_subtype, Filter.mem_comap] at hT1
  obtain ⟨T, hT, hTT1⟩ := hT1
  refine ⟨W, (c a).1, hWat, fun h => ha (Subtype.ext h), fun v => AutSub.mem_finPart.1 (c a).2 v,
    fun k hk v g => congrFun (hcF a v k hk) g, ι ⁻¹' T, hι.continuousAt.preimage_mem_nhds (by rw [hι1]; exact hT),
    fun x hx hxN v g => ?_⟩
  have hxfin : x ∈ finU (E := E) (n := n) := (Subgroup.mem_inf.1 hx).1
  have h2 : x.1 ∈ T := hιx x hx ▸ hxN
  have hk : (⟨x, hxfin⟩ : finU (E := E) (n := n)) ∈ {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} := hT1S (hTT1 h2)
  exact congrFun (LinearMap.congr_fun (congrArg Subtype.val hk) v) g

end GlobalTheory.Cong

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU (E := E) (n := n) → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  first | (exact @GlobalTheory.Cong.exists_algForm_ofType) | (exact GlobalTheory.Cong.exists_algForm_ofType) | (intros; apply GlobalTheory.Cong.exists_algForm_ofType  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPrimeHecke

open Formalism.L2.Host Formalism.L2.Col

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) :
    χ.locK Q k = χ.val Q := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [← hk]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : L)
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * (atFin Q (unif Q))⁻¹) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h1, h2, mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h4 := hu _ h3
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4

theorem exists_unif {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) :
    ∃ ϖ : 𝓞 L, ϖ ∈ Q.asIdeal ∧ ϖ ∉ Q.asIdeal ^ 2 ∧ Q.valuation L (ϖ : L) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, h⟩ := Q.intValuation_exists_uniformizer
  refine ⟨ϖ, ?_, ?_, ?_⟩
  · rw [← Q.intValuation_lt_one_iff_mem, h, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · rw [← Q.intValuation_le_pow_iff_mem, h, WithZero.exp_le_exp]; norm_num
  · rw [← h]; exact Q.valuation_of_algebraMap ϖ

theorem poly_id (q r t : ℕ) (u v : ℂ) (a : ℕ → ℂ) :
    heckePolyOf (r + t) q (fun k => ∑ j ∈ Finset.range (r + 1),
      (if j ≤ k then (q : ℂ) ^ ((r - j) * (k - j)) * (gaussBin q t (k - j) : ℂ) * u⁻¹ ^ k * v ^ j else 0) * a j) =
    (heckePolyOf r q a).comp (C (u⁻¹ * v) * X) * blockPoly (u⁻¹ * (q : ℂ) ^ r) q t := by
  have key := GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv.2 ℂ q r t (fun j => if j ≤ r then a j else 0) u⁻¹ (u⁻¹ * v)
    (fun j hj => if_neg (by omega))
  have h1 : heckePolyOf r q (fun j => if j ≤ r then a j else 0) = heckePolyOf r q a := by
    unfold heckePolyOf
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [if_pos (show j ≤ r by simpa [Nat.lt_succ_iff] using hj)]
  rw [h1] at key
  rw [← key]
  congr 1
  funext k
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr (by ext j; simp [Nat.lt_succ_iff, and_comm]) fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using (Finset.mem_filter.1 hj).1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left, pow_add, mul_pow]
  ring

variable {D : D7}

theorem not_isConjPl {P : Pl D.host.E} (h : conjPl P ≠ P) : ¬ Formalism.IndefR.Lev.IsConjPl P P := by
  intro hc
  apply h
  refine HeightOneSpectrum.ext ((conjPl P).isMaximal.eq_of_le P.isPrime.ne_top ?_)
  refine Ideal.map_le_iff_le_comap.2 fun c hcP => ?_
  obtain ⟨c', hc', he⟩ := hc c hcP
  have : Formalism.DivisionValues.cO D.host.E c = c' := RingOfIntegers.ext he.symm
  rw [Ideal.mem_comap, this]
  exact hc'

theorem unrPl_mul_inv {P : Pl D.host.E} {a b : (AE D)ˣ →* Circle} (ha : UnrPl P a) (hb : UnrPl P b) : UnrPl P (a * b⁻¹) := by
  intro e f h x h1 h2 h3
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha e f h x h1 h2 h3, hb e f h x h1 h2 h3, inv_one, mul_one]

theorem consts (μ η ηa q s : ℂ) (hμ : μ ≠ 0) (hη : η ≠ 0) (hs : s ≠ 0) (hq : s * s = q) (he : ηa = η * s⁻¹) (r t : ℕ)
    (hr : Odd r) (ht : Odd t) :
    (μ * η⁻¹ * s ^ r)⁻¹ * (μ * s ^ (r + t)) = ηa * q ^ ((t + 1) / 2) ∧
      (μ * η⁻¹ * s ^ r)⁻¹ * q ^ r = μ⁻¹ * ηa * q ^ ((r + 1) / 2) := by
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := ht
  rw [show (2 * a + 1 + 1) / 2 = a + 1 by omega, show (2 * b + 1 + 1) / 2 = b + 1 by omega, he, ← hq]
  constructor
  · field_simp
    ring
  · field_simp
    ring


set_option maxHeartbeats 1600000 in
theorem transfer_and_heckePoly : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc hS i t P
  obtain ⟨hQ0, hG, -, hF⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hc.lev
  obtain ⟨hgood, hsplit, hq⟩ := hF hc.fam t P P.2
  obtain ⟨hunη, hunμ⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hc.lev t _ hgood
  obtain ⟨gramR, c0R, c0L, tie⟩ := hc.fam.tie
  obtain ⟨-, hAr, hAt⟩ := tie.ranks
  have hP0 : (P : Pl0) ∈ A.ok A.μ0 := by
    have h := (tie.ok t P).1 P.2
    rw [tie.ok, hQ0]
    simp only [Finset.coe_empty, Set.union_empty]
    exact ⟨h.1, fun h' => h.2.1 (Or.inl h'), fun Q hQ => h.2.2 Q (Or.inl hQ)⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (not_isConjPl hsplit)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3⟩ := exists_unif (R.pl P)
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ3
    exact WithZero.exp_ne_zero hϖ3.symm
  have hpl : Formalism.L2.JoinChr.IsPlIdem D e (R.pl P) := by
    obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
    exact ⟨h1, ⟨v, ε, h3, Or.inl ⟨h2, h4⟩⟩, h5⟩
  let x : (AE D)ˣ := Formalism.L2.JoinChr.locU hpl.1 (Units.mk0 _ hϖ0)
  have hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (Units.mk0 _ hϖ0 : D.host.Eˣ) := rfl
  have hx' : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
    rw [hx, Formalism.L2.JoinChr.locE, Units.val_mk0]
    ring
  have hun1 := hunμ ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  obtain ⟨hfix, hM⟩ := GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace R.ψ _ _ _ _ _ (R.pl P) (hc.thP.ωP i t) hsplit hun1 (unrPl_mul_inv hun1 hunη)
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hV : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [hW]
    exact D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hM' := (hM e ϖ x D.R.t he hϖ1 hϖ2 hx').2 hV
  refine ⟨_, fun k hk => GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hc hS i t _ hgood hfix _ _ (hM' k hk), fun a => ?_⟩

  have hu0 : (R.C.mu0 i).UnrAt (R.pl P) := by
    refine (R.C.isMu0 i).unr _ fun k hk => (hG t _ hgood).1 ?_
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk
    · exact Ideal.mul_mem_left _ _ hk
  have huξ : (R.xiH t).UnrAt (R.pl P) := by
    by_contra h
    rcases (hc.lev.Q_ram t _).1 h with h | ⟨PP, h1, h2⟩
    · exact (hgood _ (Or.inr h)).1 rfl
    · exact (hgood _ (Or.inr h1)).2 h2
  have hη : ((R.eta x : Circle) : ℂ) = (R.C.eta.val (R.pl P) : ℂˣ) := by
    rw [hc.lev.eta.2 _ e hpl _ x hx, locK_eq_val _ _ (R.C.isEta.unr _) _ hϖ3]
  have hμ : ((R.toLevCh.mu t ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (A.muVal i t P : D.what₂.LL) := by
    rw [hc.fam.muVal i t P P.2, HChar.val_mul, Units.val_mul, ← locK_eq_val _ _ hu0 (Units.mk0 _ hϖ0) hϖ3,
      ← locK_eq_val _ _ huξ (Units.mk0 _ hϖ0) hϖ3, ← (hc.lev.mu0 i).2 _ e hpl _ x hx, ← (hc.lev.xi t).2 _ e hpl _ x hx,
      ← Circle.coe_mul]
    rfl
  have hN : (0 : ℝ) < (Ideal.absNorm (R.pl P).asIdeal : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hs0 : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hN).ne'
  have hss : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) = (Ideal.absNorm (R.pl P).asIdeal : ℕ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le, Complex.ofReal_natCast]
  have hηa : D.what₂.embLL (A.etaVal P : D.what₂.LL) =
      ((R.eta x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ)⁻¹ := by
    rw [hc.fam.etaVal P hP0, hη, etaAlg, HChar.valTw, Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow hN.le,
      Complex.ofReal_natCast]
  have hr : Odd (Wc D i).rank := by
    rw [hW]
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  obtain ⟨c1, c2⟩ := consts _ _ _ _ _ (Circle.coe_ne_zero (R.toLevCh.mu t ((i : ℕ) + 1) x)) (Circle.coe_ne_zero (R.eta x))
    hs0 hss hηa _ _ hr D.R.t_odd
  have hB : ((A.fam.L i t).blockProd P).map D.what₂.embLL =
      blockPoly (D.what₂.embLL (firstValA (A.muVal i t) A.etaVal A.q A.r P)) (A.q P) A.t := by
    rw [← map_blockPoly]
    simp [BlockDat.blockProd, FamIn.fam, liftDat]
  rw [hB, firstValA, map_mul D.what₂.embLL, map_mul D.what₂.embLL, Units.val_inv_eq_inv_val, map_inv₀, map_pow D.what₂.embLL, map_natCast D.what₂.embLL, ← hμ,
    hAr, hAt, hq, ← hW,
    ← c1, ← c2]
  simp only [Lift.chrTh, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [hV]
  exact poly_id _ _ _ _ _ a

end GlobalTheory.ThetaPrimeHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  first | exact @GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly | exact GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly | (intros; apply GlobalTheory.ThetaPrimeHecke.transfer_and_heckePoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartForm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartForm
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

open GlobalTheory.DefU

namespace GlobalTheory.Cong

theorem ofType_of_finPart_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n)
    (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) →
    OfType (fun τ => W.at τ) K π.V := by
  intro E _ _ _ n π W K f hf hf0 hK
  refine ⟨π.isAut, fun τ => ?_, ?_⟩
  · have h : (AU.mk π).HasWt (InfinitePlace.mk τ).embedding (W (InfinitePlace.mk τ)) :=
      hasWeightAt_of_finPart π W hf hf0 (InfinitePlace.mk τ)
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · have h' := h
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), e] at h'
      exact h'
    · have h2 := h.conjugate
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ] at h2
      exact h2
  · have hne : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (LinearMap.ext hc)
    refine ⟨f.1 v, AutSub.mem_finPart.1 hf v, hv, fun x hx => ?_⟩
    funext g
    rw [RU_apply]
    exact hK x hx v g

end GlobalTheory.Cong

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartFormStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAutomorphicOfWeight_of_nonzero_fixed_finPart_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) → OfType (fun τ => W.at τ) K π.V := by
  first | (exact @GlobalTheory.Cong.ofType_of_finPart_fixed) | (exact GlobalTheory.Cong.ofType_of_finPart_fixed) | (intros; apply GlobalTheory.Cong.ofType_of_finPart_fixed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicCharacterUnitary
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

namespace GlobalTheory.LadicInf

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l) :
    ∃ (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l),
      ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ Continuous j ∧ j.comp (algebraMap E (u.adicCompletion E)) = τ := by
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l τ u hu
  refine ⟨u, j, ?_, hj, hjE⟩
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have h1 : ‖τ ((((l : ℕ) : 𝓞 E)) : E)‖ < 1 := by
    have : τ ((((l : ℕ) : 𝓞 E)) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this]
    have := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [this]
    first | exact Padic.norm_p_lt_one | exact padicNormE.norm_p_lt_one
  have := (hu (((l : ℕ) : 𝓞 E) : E)).2 h1
  simpa using this

end GlobalTheory.LadicInf

namespace GlobalTheory.LadicInf

end GlobalTheory.LadicInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariant
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open GlobalTheory.DefU

namespace GlobalTheory.AlgMul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RU_mul (x : UA E n) (a b : UA E n → ℂ) : RU E n x (a * b) = RU E n x a * RU E n x b := rfl

theorem isOpen_fix_of {ψ : UA E n → ℂ} (U : Set (finU (E := E) (n := n))) (hU : IsOpen U) (h1 : (1 : finU (E := E) (n := n)) ∈ U)
    (hs : ∀ k ∈ U, RU E n k ψ = ψ) : IsOpen {k : finU (E := E) (n := n) | RU E n k ψ = ψ} := by
  let St : Subgroup (finU (E := E) (n := n)) :=
    { carrier := {k | RU E n k ψ = ψ}
      mul_mem' := fun {a b} ha hb => by
        change RU E n ((a : UA E n) * b) ψ = ψ
        rw [← RU_RU]
        change RU E n a (RU E n b ψ) = ψ
        rw [hb]; exact ha
      one_mem' := by
        change RU E n ((1 : finU (E := E) (n := n)) : UA E n) ψ = ψ
        simp
      inv_mem' := fun {a} ha => by
        change RU E n ((a : UA E n)⁻¹) ψ = ψ
        conv_lhs => rw [← (show RU E n (a : UA E n) ψ = ψ from ha)]
        rw [RU_RU, inv_mul_cancel, map_one, Module.End.one_apply] }
  have : (St : Set (finU (E := E) (n := n))) ∈ nhds (1 : finU (E := E) (n := n)) :=
    Filter.mem_of_superset (hU.mem_nhds h1) hs
  exact Subgroup.isOpen_of_mem_nhds St this

theorem isAutFormU_mul {e φ : UA E n → ℂ} (he : IsAutFormU e) (hinv : ∀ g, ∀ x ∈ infU E n, e (g * x) = e g)
    (hφ : IsAutFormU φ) : IsAutFormU (e * φ) := by
  refine ⟨he.cont.mul hφ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · simp only [Pi.mul_apply, he.left γ hγ g, hφ.left γ hγ g]
  · refine isOpen_fix_of _ (he.level.inter hφ.level) ⟨by simp, by simp⟩ ?_
    rintro k ⟨hk1, hk2⟩
    rw [RU_mul, show RU E n k e = e from hk1, show RU E n k φ = φ from hk2]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map (LinearMap.mulLeft ℂ e))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨RU E n k φ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    show e * RU E n k φ = RU E n k (e * φ)
    rw [RU_mul]
    congr 1
    funext g
    exact (hinv g k k.2).symm

end GlobalTheory.AlgMul

theorem GlobalTheory.AlgMul.exists_mul_algForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (f : algForms W) (e : UA E n → ℂ), IsAutFormU e → (∀ g, ∀ x ∈ infU E n, e (g * x) = e g) → ∃ f' : algForms W, ∀ v g, f'.1 v g = e g * f.1 v g := by
  intro E _ _ _ n W f e he hinv
  have hmem : (LinearMap.mulLeft ℂ e).comp f.1 ∈ algForms W := by
    refine ⟨fun v => GlobalTheory.AlgMul.isAutFormU_mul he hinv (f.2.1 v), fun x v => ?_⟩
    change e * f.1 (W.rep x v) = RU E n x (e * f.1 v)
    rw [f.2.2 x v, GlobalTheory.AlgMul.RU_mul]
    congr 1
    funext g
    exact (hinv g x x.2).symm
  exact ⟨⟨_, hmem⟩, fun v g => rfl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariantStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (f : algForms W) (e : UA E n → ℂ), IsAutFormU e → (∀ g, ∀ x ∈ infU E n, e (g * x) = e g) → ∃ f' : algForms W, ∀ v g, f'.1 v g = e g * f.1 v g := by
  first | (exact @GlobalTheory.AlgMul.exists_mul_algForms) | (exact GlobalTheory.AlgMul.exists_mul_algForms) | (intros; apply GlobalTheory.AlgMul.exists_mul_algForms  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem intOff_finset_prod {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IntOff.one : IntOff S 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem xiCpl1_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ al p₀ p Yb x
  have hm : t.m2 < D.R.m := by have := (t.idx_ok μ).hm; omega
  unfold XiCpl1
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · rw [map_one]; exact IntOff.one
    · rw [map_zero]; exact IntOff.zero
  · unfold PsiAt
    first
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ hQ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _
    | exact GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t h1 h2 u μ t.m2 hm P _ 1
        (fun hP => ⟨(t.idx_ok μ).stabG t.m2 al P hP, one_mem _⟩) _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.precedingStepDatum_integral_away_from_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  first | exact @GlobalTheory.xiCpl1_intOff | exact GlobalTheory.xiCpl1_intOff | (intros; apply GlobalTheory.xiCpl1_intOff <;> assumption)
end
end
