module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumUniqueness
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

variable {D : D7}

def TrivOnF (D : D7) (ξ : (AE D)ˣ →* Circle) : Prop := ∀ a : (AF D.host.F)ˣ, ξ (idF D a) = 1

def IsTildeDet (V : HSp D) (ξ : (AE D)ˣ →* Circle) (g : GA D V) (c : Circle) : Prop :=
  (∃ x, IsDetRoot V g x) ∧ ∀ x, IsDetRoot V g x → ξ x = c

def WeilDatumUnique (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' →
      ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → om' (g, h) f = om (g, h) f

def WeilDatumTwist (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT ξ ξ' : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    TrivOnF D ξ → TrivOnF D ξ' →
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T (χS * ξ) (χT * ξ') om' →
      ∀ (g : GA D S) (h : GA D T), ∃ a b : Circle, IsTildeDet S ξ' g a ∧ IsTildeDet T ξ h b ∧
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
          om' (g, h) f = ((a⁻¹ * b : Circle) : ℂ) • om (g, h) f

def WeilDatumDetermined (D : D7) : Prop := WeilDatumUnique D ∧ WeilDatumTwist D

theorem IsTildeDet.at_one {V : HSp D} {ξ : (AE D)ˣ →* Circle} {c : Circle} (h : IsTildeDet V ξ 1 c) : c = 1 := by
  have h1 : IsDetRoot V 1 1 := by simp [IsDetRoot]
  rw [← h.2 1 h1, map_one]

theorem WeilDatumTwist.unique (H : WeilDatumTwist D) : WeilDatumUnique D := by
  intro ψ S T χS χT om om' h h' g k f hf
  obtain ⟨a, b, ha, hb, e⟩ := H ψ S T χS χT 1 1 om om' (fun _ => rfl) (fun _ => rfl) h
    (by simpa using h') g k
  obtain ⟨x, hx⟩ := ha.1
  obtain ⟨y, hy⟩ := hb.1
  have ha1 : a = 1 := (ha.2 x hx).symm
  have hb1 : b = 1 := (hb.2 y hy).symm
  simpa [ha1, hb1] using e f hf

end GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDetermined

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

theorem agree_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

theorem hecke_of_mul {χ ξ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (h : IsHeckeChar D (χ * ξ)) :
    IsHeckeChar D ξ := by
  have := GlobalTheory.WeilChange.hecke_mul (GlobalTheory.WeilChange.hecke_inv hχ) h
  rwa [inv_mul_cancel_left] at this

theorem exists_isTildeDet (V : HSp D) {ξ : (AE D)ˣ →* Circle} (hξ : IsHeckeChar D ξ)
    (h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D ξ) (g : GA D V) :
    ∃ x, IsDetRoot V g x ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.IsTildeDet V ξ g (ξ x) := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V ξ hξ h0
  obtain ⟨x, hx⟩ := aval.1 g
  refine ⟨x, hx, ⟨x, hx⟩, fun y hy => Circle.ext ?_⟩
  rw [← aval.2 g x hx, ← aval.2 g y hy]

theorem weilDatumTwist (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumTwist D := by
  intro ψ S T χS χT ξ ξ' om om' h0 h0' H H' g h
  have hξ := hecke_of_mul H.hecS H'.hecS
  have hξ' := hecke_of_mul H.hecT H'.hecT
  obtain ⟨om'', H'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H.std S T χS χT ξ ξ' om H hξ hξ'
    ⟨H.resS.1, fun η _ a => by rw [h0 a, pow_zero]⟩ ⟨H.resS.1, fun η _ a => by rw [h0' a, pow_zero]⟩
  obtain ⟨x, hx, ha⟩ := exists_isTildeDet S hξ' h0' g
  obtain ⟨y, hy, hb⟩ := exists_isTildeDet T hξ h0 h
  refine ⟨ξ' x, ξ y, ha, hb, fun f hf => ?_⟩
  rw [agree_on_theta D ψ H.std S T _ _ om' om'' H' H'' (g, h) f hf, hv g h x y hx hy, LinearMap.smul_apply]

theorem weilDatumDetermined (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumDetermined D :=
  ⟨(weilDatumTwist D).unique, weilDatumTwist D⟩

end GlobalTheory.WeilDetermined
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAAPartition

theorem host_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h0
    have h1 := D.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hc : D.host.ccE ≠ ⊥ := by
    unfold Formalism.BasicNotions.Host.ccE
    rw [Ne, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]
    exact D.host.ccK_ne_bot
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  exact mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb))

theorem host_AA_partition : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  intro D
  set I := D.host.AA with hI
  have hne : I ≠ 0 := host_AA_ne_zero D
  have h1 : (1 : D.host.E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hne]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ z ∈ I * I⁻¹, ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ I) ∧
      (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = z := by
    intro z hz
    refine FractionalIdeal.mul_induction_on (C := fun z => ∃ (m : ℕ) (a c : Fin m → D.host.E),
      (∀ i, a i ∈ I) ∧ (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧
        ∑ i, a i * c i = z) hz ?_ ?_
    · intro u hu v hv
      refine ⟨1, fun _ => u, fun _ => v, fun _ => hu, ?_, by simp⟩
      intro _ x hx
      have hvx : v * x ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hv hx
      rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_one_iff] at hvx
      obtain ⟨b, hb⟩ := hvx
      exact ⟨b, hb⟩
    · rintro u v ⟨m, a, c, ha, hc, rfl⟩ ⟨n, a', c', ha', hc', rfl⟩
      refine ⟨m + n, Fin.append a a', Fin.append c c', ?_, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using ha j
        · simpa using ha' j
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using hc j
        · simpa using hc' j
      · rw [Fin.sum_univ_add]
        simp
  exact key 1 h1

end GlobalTheory.HostAAPartition
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  first | exact @GlobalTheory.HostAAPartition.host_AA_partition | exact GlobalTheory.HostAAPartition.host_AA_partition | (intros; apply GlobalTheory.HostAAPartition.host_AA_partition <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetEqOfColsUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open Finset
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramJacobi

theorem det_eq_of_cols_unit {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (h : ∀ i j, ¬ p j → M i j = (1 : Matrix n n R) i j) :
    M.det = (M.toSquareBlockProp p).det := by
  rw [← Matrix.det_transpose, Matrix.twoBlockTriangular_det (Matrix.transpose M) p]
  · have h1 : ((Matrix.transpose M).toSquareBlockProp fun i => ¬ p i) = 1 := by
      ext i j
      simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.transpose_apply,
        Matrix.submatrix_apply]
      rw [h _ _ i.2, Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e.symm))]
    rw [h1, Matrix.det_one, mul_one, ← Matrix.det_transpose]
    rfl
  · intro i hi j hj
    rw [Matrix.transpose_apply, h _ _ hi, Matrix.one_apply_ne]
    rintro rfl
    exact hi hj

theorem jacobi_minor {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (G H : Matrix n n R) (hHG : H * G = 1) (p : n → Prop) [DecidablePred p] :
    (H.toSquareBlockProp fun i => ¬ p i).det * G.det = (G.toSquareBlockProp p).det := by
  have hGH : G * H = 1 := mul_eq_one_comm.mp hHG
  let N : Matrix n n R := Matrix.of fun i j => if p j then (1 : Matrix n n R) i j else H i j
  have hN : N.det = (H.toSquareBlockProp fun i => ¬ p i).det := by
    rw [Matrix.twoBlockTriangular_det N p]
    · have h1 : N.toSquareBlockProp p = 1 := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_pos j.2]
        rw [Matrix.one_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (fun e => hij (Subtype.ext e))]
      have h2 : (N.toSquareBlockProp fun i => ¬ p i) = H.toSquareBlockProp fun i => ¬ p i := by
        ext i j
        simp only [N, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.of_apply, if_neg j.2]
      rw [h1, h2, Matrix.det_one, one_mul]
    · intro i hi j hj
      simp only [N, Matrix.of_apply, if_pos hj]
      rw [Matrix.one_apply_ne]
      rintro rfl
      exact hi hj
  have hGN : (G * N).det = (G.toSquareBlockProp p).det := by
    rw [det_eq_of_cols_unit (G * N) p]
    · have : (G * N).toSquareBlockProp p = G.toSquareBlockProp p := by
        ext i j
        simp only [Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply,
          Matrix.mul_apply, N, Matrix.of_apply, if_pos j.2, Matrix.one_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
    · intro i j hj
      rw [← hGH]
      simp only [Matrix.mul_apply, N, Matrix.of_apply, if_neg hj]
  rw [← hN, mul_comm, ← Matrix.det_mul, hGN]

end GlobalTheory.GramJacobi

namespace GlobalTheory.GramJacobi

end GlobalTheory.GramJacobi

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvalNormTransfer

theorem castGA_mem_GFset {I I' : AutInst} (h : I = I') (x : I.GA) :
    castGA h x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst h; exact Iff.rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ (iotaX X h).toMulEquiv g ∈ X.B.I.GFset := by
  rw [Formalism.IndefR.RationalEmbedding.iota_rat D g]
  exact (castGA_mem_GFset h.symm _).symm

theorem borel_inst {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : BorelSpace X.B.I.GA := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  infer_instance

theorem exists_map_eq_smul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ν : Measure (GA D (D.sp.Y 0))) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • ν := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ga_facts D (D.sp.Y 0)
  haveI := X.B.haar
  haveI := X.B.sf
  haveI : BorelSpace X.B.I.GA := inferInstance
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  set μ' := Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) with hμ'
  haveI hH : μ'.IsHaarMeasure :=
    (iotaX X h).toMulEquiv.symm.isHaarMeasure_map _ (iotaX X h).symm.continuous (iotaX X h).continuous
  refine ⟨(Measure.haarScalarFactor μ' ν : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ' ν
  · rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def]
    exact Measure.isMulLeftInvariant_eq_smul μ' ν

theorem evalTranslate_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ t ∈ GfC (Yc D 0), ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ EP R F, MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X) ∧ ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t ht
  haveI hνH : R.ν0.IsHaarMeasure := hM.ν0.1.1
  obtain ⟨c, hc, hmap⟩ := @exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hM.ν0.2 (iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hI := GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel R hM
  have hS' : S ∈ R.EEat (R.levR F true) := hS
  have hMult : S ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) := hS'.1
  have hcl := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := _) (χ := _) hMult v₀
  have hip := hI.2.2 _ S hS' S hS'
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : MemLp (S v₀) 2 (R.ν0.restrict R.fd0) := by
    refine (memLp_two_iff_integrable_sq_norm hcl.1.measurable.aestronglyMeasurable).2
      (((hip v₀ v₀).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) hcl.1 hcl.2 hL2
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq ⟨_, hip⟩ hv).symm), ?_⟩
  intro h0
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 (hI.2.1 _ hS')
  have hx : inner ℂ x x = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x) := hM.HE.2.2 x x
  have hre : ‖x‖ ^ 2 = (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x)).re := by
    rw [← hx]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have h00 : ‖x‖ ^ 2 = 0 := hre.trans h0
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h00
  rw [h00]
  exact map_zero R.HE.e

end GlobalTheory.EvalNormTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ t ∈ GfC (Yc D 0), ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ EP R F, MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X) ∧ ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  first | exact @GlobalTheory.EvalNormTransfer.evalTranslate_norm | exact GlobalTheory.EvalNormTransfer.evalTranslate_norm | (intros; apply GlobalTheory.EvalNormTransfer.evalTranslate_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) hspan h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

end Zero

end GlobalTheory.NoExcl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientModelEqConjTraceFormulaDiscreteSer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDsModelOfInstData
open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isEnum_parA_zero (D : D7) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    IsEnum (parA (tparRec D) 0 τ) (fun i : Fin n => lamS D.R (D.hc τ) (Fin.cast hn i))
      (fun i => epsS D.R (Fin.cast hn i)) := by
  subst hn
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  simp only [Fin.cast_eq_self]
  refine ⟨?_, fun i => if h : i.val < D.R.k - 1 then (D.hc τ).v ⟨i.val, h⟩
    else if h' : i.val - (D.R.k - 1) < D.R.m then -(D.hc τ).b ⟨i.val - (D.R.k - 1), h'⟩ else 0, ?_, ?_⟩
  · have h := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
    intro a b hab
    have := h (a := Fin.cast (dimS_eq D.R).symm a) (b := Fin.cast (dimS_eq D.R).symm b) hab
    simpa [lamSH] using this
  · intro a
    simp only [lamS]
    split_ifs <;> simp
  · have hpar : ∀ a : ℕ, decide (a ≤ 0 ∨ Even (a - 0)) = decide (a % 2 = 0) := by
      intro a
      rw [decide_eq_decide, Nat.sub_zero, Nat.even_iff]
      omega
    ext x
    simp only [parA, TPar.Dpar, tparRec, tparHC, hpar, Nat.not_odd_zero, if_false, add_zero,
      Nat.not_lt_zero, Finset.filter_false, Finset.biUnion_empty, Finset.union_empty, Prod.mk.eta,
      Finset.image_id', Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨⟨i.val, by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
      · refine ⟨⟨i.val + (D.R.k - 1), by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
    · rintro ⟨a, rfl⟩
      by_cases h : a.val < D.R.k - 1
      · exact Or.inl ⟨⟨a.val, h⟩, by simp [epsS, h]⟩
      · have h' : a.val - (D.R.k - 1) < D.R.m := by have := a.2; omega
        exact Or.inr ⟨⟨_, h'⟩, by simp [epsS, h, h']⟩

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientModelEqConjTraceFormulaDiscreteSer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeInt

section Frame

open Formalism.L2.SG.InstExistsPf

def frP (D : D7) (τ : D.what₂.Tau) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
  (instOf D).P (Formalism.L2.Host.tauPl D τ)

theorem frP_unit (D : D7) (τ : D.what₂.Tau) : IsUnit (frP D τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((instOf D).P_unit _)

theorem fr_gram (D : D7) (τ : D.what₂.Tau) :
    ((frP D τ)⁻¹)ᴴ * Formalism.REAL.Jm (epsV D) * (frP D τ)⁻¹ = gramAt D (D.sp.Y 0) τ := by
  have h : (frP D τ)ᴴ * gramAt D (D.sp.Y 0) τ * frP D τ = Formalism.REAL.Jm (epsV D) := by
    have h0 := (instOf D).P_spec (Formalism.L2.Host.tauPl D τ)
    have hJ : (instOf D).J.map ((instOf D).φ (Formalism.L2.Host.tauPl D τ)) = gramAt D (D.sp.Y 0) τ := by
      show (Jv D).map (embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D τ))) = _
      rw [Equiv.symm_apply_apply]; rfl
    rw [hJ] at h0
    exact h0
  rw [← h]
  have h1 := Matrix.mul_nonsing_inv (frP D τ) (frP_unit D τ)
  have h2 : ((frP D τ)⁻¹)ᴴ * (frP D τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc _ (frP D τ), h1, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem exists_conj_intertwiner (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) (hmult : GlobalTheory.Dec.LowKMultOne)
    (hstrict : GlobalTheory.DSId.StrictLow) {D : D7} (I : AutInst) (hI : I = instOf D)
    (pl : InfinitePlace I.F ≃ D.what₂.Tau) (n_eq : I.n = D.R.r)
    (eps_eq : ∀ v (i : Fin I.n), I.ε v i = epsS D.R (Fin.cast n_eq i))
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (lam_eq : ∀ v (i : Fin I.n), lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i))
    (ds : ∀ v, IsDS (I.ε v) (lam v) (σ v)) (low : ∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v))
    (N : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) :
    ∃ c : ∀ τ, N.H τ ≃ₗᵢ⋆[ℂ] H (pl.symm τ),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ m : Matrix (Fin I.n) (Fin I.n) ℂ,
        HEq m ((frP D τ)⁻¹ * g * frP D τ) → ∀ x, c τ (N.rep τ g x) = σ (pl.symm τ) m (c τ x)) ∧
      ∀ τ, (c τ).symm (w (pl.symm τ)) ∈ N.sm τ := by
  subst hI
  let M0 : DSModel (D.sp.Y 0) (parA (tparRec D) 0) :=
    { H := fun τ => H (pl.symm τ)
      σ := fun τ => σ (pl.symm τ)
      lam := fun τ => lam (pl.symm τ)
      ε := fun τ => (instOf D).ε (pl.symm τ)
      fr := fun τ => (frP D τ)⁻¹
      enum := fun τ => by
        have e1 : lam (pl.symm τ) = fun i => lamS D.R (D.hc τ) (Fin.cast n_eq i) :=
          funext fun i => by rw [lam_eq, Equiv.apply_symm_apply]
        have e2 : (instOf D).ε (pl.symm τ) = fun i => epsS D.R (Fin.cast n_eq i) := funext fun i => eps_eq _ i
        rw [e1, e2]
        exact GlobalTheory.RowLev.isEnum_parA_zero D n_eq τ
      ds := fun τ => ds _
      fr_unit := fun τ => Matrix.isUnit_nonsing_inv_iff.mpr ((instOf D).P_unit _)
      fr_gram := fun τ => fr_gram D τ }
  obtain ⟨M', c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M0
  obtain ⟨U, hUi⟩ := hU.exists_intertwiner (M := (M' : DSModel (D.sp.Y 0) (parB (tparRec D) 0))) (M' := N)
  have key : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ x,
      c τ (U τ (N.rep τ g x)) = M0.rep τ g (c τ (U τ x)) := by
    intro τ g hg x
    exact (congrArg (c τ) (hUi τ g hg x)).trans (hc τ g hg _)
  refine ⟨fun τ => (U τ).trans (c τ), ?_, ?_⟩
  · intro τ g hg m hm x
    have hm' : m = (frP D τ)⁻¹ * g * frP D τ := eq_of_heq hm
    show c τ (U τ (N.rep τ g x)) = σ (pl.symm τ) m (c τ (U τ x))
    rw [key τ g hg x, hm']
    show σ (pl.symm τ) ((frP D τ)⁻¹ * g * ((frP D τ)⁻¹)⁻¹) _ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ (frP_unit D τ)]
  · intro τ
    have hw : w (pl.symm τ) ∈ M0.sm τ := by
      obtain ⟨S, hS, hSle⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D _ _ M0 τ
      have hHC := GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M0.enum τ).1 (M0.ds τ)
      have : CompleteSpace (H (pl.symm τ)) := (ds _).1
      have h1 := (hstrict _ _ _ hHC (H (pl.symm τ)) (σ (pl.symm τ)) (ds _)).1
      have h2 := hmult _ _ _ _ (σ (pl.symm τ)) hHC (ds _) _ _ h1 hS
      exact hSle (h2 ▸ (low _).2)
    set e := (U τ).trans (c τ) with he
    have hint : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ y,
        e.symm (M0.rep τ g y) = N.rep τ g (e.symm y) := by
      intro g hg y
      apply e.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      have := key τ g hg (e.symm y)
      change e (N.rep τ g (e.symm y)) = M0.rep τ g (e (e.symm y)) at this
      rw [this, LinearIsometryEquiv.apply_symm_apply]
    exact GlobalTheory.ConjMult.span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit _ τ) e.symm hint hw

end Frame

theorem conjModel_of_setting : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  intro hcl D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod _hhost hιE
  obtain ⟨-, hreal, -⟩ := GlobalTheory.T.adelicIdentification_respects_real_finite R F X h hlev hgrp hmod hιE
  obtain ⟨-, -, -, -, hmult, -, hstrict⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hcl
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_of_classification hcl
  obtain ⟨c, hc1, hc2⟩ := exists_conj_intertwiner hU hmult hstrict X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ X.B.w
    X.B.lam X.lam_eq X.ds X.low (MP R)
  exact ⟨c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x, hc2⟩

end GlobalTheory.SeeInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientModelEqConjTraceFormulaDiscreteSerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  first | exact @GlobalTheory.SeeInt.conjModel_of_setting | exact GlobalTheory.SeeInt.conjModel_of_setting | (intros; apply GlobalTheory.SeeInt.conjModel_of_setting <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFormsOrth

variable {D : D7}

theorem hO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    hO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.rat_conjTranspose]
  have hz : GlobalTheory.MixModel.rat R * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ) = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, ← Matrix.mul_assoc, h,
      GlobalTheory.MixModel.rat_zero]
  have e : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.rat Qᴴ * GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * (a * GlobalTheory.MixModel.rat R)))
      = GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ * (GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * a)) * GlobalTheory.MixModel.rat R := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero]

theorem symplO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    symplO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.symplO_eq, hO_mul_rat_eq_zero V W a b R Q h, mul_zero, map_zero]

theorem frame_pair (V : HSp D) {r s : ℕ} (C₁ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (C₂ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    adj D C₁ * V.gram * V.gram⁻¹ * (adj D C₂ * V.gram)ᴴ = adj D C₁ * V.gram * C₂ := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]

theorem frame_mid (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (h : adj D C * V.gram * B = 0) :
    adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig] at h ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    GlobalTheory.MixModel.gramInv_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  intro D V V' W r C B hs C' _ hC' hC'B
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  refine ⟨fun a b => ?_, fun a x => ?_, fun a x => ?_, fun a b => ?_⟩
  · exact symplO_mul_rat_eq_zero V W a b (adj D C * V.gram) (adj D C * V.gram) ((frame_pair V C C).trans hC)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C B hs.orth)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C' * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C' B hC'B)
  · exact symplO_mul_rat_eq_zero V W a b (adj D C' * V.gram) (adj D C' * V.gram) ((frame_pair V C' C').trans hC')

end GlobalTheory.TwistFormsOrth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  first | exact @GlobalTheory.TwistFormsOrth.orthogonal | exact GlobalTheory.TwistFormsOrth.orthogonal | (intros; apply GlobalTheory.TwistFormsOrth.orthogonal <;> assumption)
end
end
