module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdFromConj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem invTOp_invTOp (o : Op L a) : invTOp (invTOp o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (Units.ext (Matrix.transpose_transpose k.val))
  | cpt k =>
    refine congrArg Op.cpt (Subtype.ext ?_)
    ext i j : 1
    simp [barK, Matrix.star_apply]
  | lie X =>
    refine congrArg Op.lie ?_
    funext i j
    simp [toL, Function.swap, Pi.neg_apply]

theorem invT_map {R : Type} [CommRing R] (c : R →+* R) (g : GL (Fin a) R) :
    invT a R (GeneralLinearGroup.map c g) = GeneralLinearGroup.map c (invT a R g) :=
  Units.ext (by rw [show (invT a R (GeneralLinearGroup.map c g)).val = ((GeneralLinearGroup.map c g)⁻¹).valᵀ from rfl,
    ← map_inv]; rfl)


omit [NumberField L] [IsCMField L] in
theorem barK_barK (k : Kinf L a) : barK (barK k) = k := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [barK, Matrix.star_apply]

def phiG (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : GA L a :=
  finGL L a (PhiU a (Af L)) * infGL L a (Unitary.toUnits (PhiK L a))

theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

theorem act_thetaOp (o : Op L a) :
    act (thetaOp o) * rt L a (phiG L a) = rt L a (phiG L a) * act (conjOp (invTOp o)) := by
  cases o with
  | fin k =>
    change rt L a (finGL L a _) * rt L a (phiG L a) = rt L a (phiG L a) * rt L a (finGL L a _)
    rw [← map_mul, ← map_mul]
    congr 1
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul]
    · simp only [phiG, map_mul, pFin_finGL, pFin_infGL, mul_one]
      rw [thetaGL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, invT_map]
      simp [mul_assoc]
  | cpt k =>
    change rt L a (infGL L a (Unitary.toUnits _)) * rt L a (phiG L a) =
      rt L a (phiG L a) * rt L a (infGL L a (Unitary.toUnits _))
    rw [← map_mul, ← map_mul]
    congr 1
    rw [barK_barK]
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul, map_inv]
    · simp [phiG, map_mul]
  | lie X =>
    have hY : (fun i j => star (toL (-(Matrix.of X)ᵀ) i j) : Lie L a) = toL (-(Matrix.of X)ᴴ) := by
      funext i j
      simp [toL, Matrix.conjTranspose_apply]
    have hR := GlobalTheory.CapAdInv.rt_lie (PhiU a (Cinf L)) (-(Matrix.of X)ᴴ)
    have e : (PhiU a (Cinf L)).val * -(Matrix.of X)ᴴ * ((PhiU a (Cinf L))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]; rfl
    rw [e] at hR
    change lie L a _ * rt L a (phiG L a) = rt L a (phiG L a) * lie L a (fun i j => star (toL (-(Matrix.of X)ᵀ) i j))
    rw [hY, phiG, map_mul, toUnits_PhiK, mul_assoc (rt L a (finGL L a _)), hR, ← mul_assoc (rt L a (finGL L a _)),
      ← lie_rt_fin, mul_assoc (lie L a _)]

theorem rt_phiG : rt L a (phiG L a) = act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a)) := map_mul _ _ _

theorem act_fin_inv (k : GL (Fin a) (Af L)) : act (.fin k) * act (.fin k⁻¹) = 1 := by
  change finRep L a k * finRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

theorem act_fin_inv' (k : GL (Fin a) (Af L)) : act (.fin k⁻¹) * act (.fin k) = 1 := by
  change finRep L a k⁻¹ * finRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

theorem act_cpt_inv (k : Kinf L a) : act (.cpt k) * act (.cpt k⁻¹) = 1 := by
  change cptRep L a k * cptRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

theorem act_cpt_inv' (k : Kinf L a) : act (.cpt k⁻¹) * act (.cpt k) = 1 := by
  change cptRep L a k⁻¹ * cptRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

def phiEquiv (π : CuspSub L a) : π.V ≃ₗ[ℂ] π.V :=
  LinearEquiv.ofLinear (π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a)))
    (π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹))
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (.cpt (PhiK L a)⁻¹)
        (act (.fin (PhiU a (Af L))⁻¹) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.cpt (PhiK L a))), act_cpt_inv, Module.End.one_apply,
        ← Module.End.mul_apply, act_fin_inv, Module.End.one_apply])
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.cpt (PhiK L a)⁻¹) (act (.fin (PhiU a (Af L))⁻¹) (act (.fin (PhiU a (Af L)))
        (act (.cpt (PhiK L a)) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.fin (PhiU a (Af L))⁻¹)), act_fin_inv', Module.End.one_apply,
        ← Module.End.mul_apply, act_cpt_inv', Module.End.one_apply])

theorem op_thetaOp_phiEquiv (π : CuspSub L a) (o : Op L a) (φ : π.V) :
    π.op (thetaOp o) (phiEquiv π φ) = phiEquiv π (π.op (conjOp (invTOp o)) φ) := Subtype.ext <| by
  change act (thetaOp o) (act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) φ.1)) =
    act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (conjOp (invTOp o)) φ.1))
  have h := LinearMap.congr_fun (act_thetaOp (L := L) (a := a) o) φ.1
  rw [rt_phiG] at h
  exact h

theorem isCsd_of_invT_conj (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (S : π.V ≃ₗ[ℂ] π.V) (hS : ∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) : π.IsCsd := by
  refine ⟨(phiEquiv π).symm.trans S.symm, fun o φ => ?_⟩
  obtain ⟨χ, rfl⟩ := (phiEquiv π).surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective χ
  have h := hS (invTOp o) ψ
  rw [invTOp_invTOp] at h
  simp only [LinearEquiv.trans_apply, op_thetaOp_phiEquiv, LinearEquiv.symm_apply_apply, ← h]

end GlobalTheory.CsdFromConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConjStatement
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (S : π.V ≃ₗ[ℂ] π.V), (∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) → π.IsCsd := by
  first | exact @GlobalTheory.CsdFromConj.isCsd_of_invT_conj | exact GlobalTheory.CsdFromConj.isCsd_of_invT_conj | (intros; apply GlobalTheory.CsdFromConj.isCsd_of_invT_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrime
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ConjMatch

variable {D : D7}

theorem conj_eq_cP (P : Pl D.host.E) : Formalism.DivisionValues.conjPl P = GlobalTheory.IdemSupport.cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.SplitHeckeAdj.isConjPl_conj P)

theorem conj_conj (P : Pl D.host.E) : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := by
  rw [conj_eq_cP, conj_eq_cP]
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem isPrimeIdem_conj {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    IsPrimeIdem (Formalism.DivisionValues.conjPl P) (cA D e) f := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have h1 : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) := by
      rw [conj_eq_cP]
      obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
      exact ⟨⟨by rw [← RingHom.map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
        by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩, GlobalTheory.IdemSupport.Comparison₂.conj ht⟩
    exact Or.inl ⟨h1, by rw [Formalism.L2.Theta.cA_cA, add_comm]⟩
  · have hc := GlobalTheory.IdemSupport.cA_algebraMap (D := D) ε
    have ht' := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [← conj_eq_cP] at ht'
    rw [hc] at ht' ⊢
    exact Or.inr ⟨rfl, ⟨v, ε, hε, rfl⟩, ht'⟩

theorem isVacAt_conj (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ)
    (h : IsVacAt ψ S T P f) : IsVacAt ψ S T (Formalism.DivisionValues.conjPl P) f := by
  refine ⟨h.1, fun e f' hP u hu hh => h.2 (cA D e) f' ?_ u hu ?_⟩
  · have := isPrimeIdem_conj hP
    rwa [conj_conj] at this
  · rw [Formalism.L2.Theta.cA_cA]
    exact hh.symm

theorem one_mem_hyp (V : HSp D) (P : Pl D.host.E) : (1 : GA D V) ∈ hyp V P := by
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.IdemSupport.exists_comp D).choose_spec P
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, h,
    (GlobalTheory.IdemSupport.suppGroup V f).one_mem⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem match_conj : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → (∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f) ∧ (VacFix ψ om P → VacFix ψ om (conjPl P) ∧ ∀ cS cT, Match ψ om (conjPl P) cS cT ↔ Match ψ om P (dualC cS) (dualC cT)) := by
  intro D ψ S T χS χT om P _
  have hv : ∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f := fun f =>
    ⟨fun h => by have := isVacAt_conj ψ S T _ f h; rwa [conj_conj] at this, isVacAt_conj ψ S T P f⟩
  refine ⟨hv, fun hF => ?_⟩
  have hS := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel S P
  have hT := GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel T P
  refine ⟨fun f hf k hk k' hk' => hF f ((hv f).1 hf) k (hS.1 ▸ hk) k' (hT.1 ▸ hk'), fun cS cT => ?_⟩
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inl _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inl _ _)) P (dualC c) f := fun f hf c =>
    hS.2.2 c _ (om.comp (MonoidHom.inl _ _)) f fun k hk => hF f hf k hk 1 (one_mem_hyp T P)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ c, opOf (om.comp (MonoidHom.inr _ _)) (conjPl P) c f =
      opOf (om.comp (MonoidHom.inr _ _)) P (dualC c) f := fun f hf c =>
    hT.2.2 c _ (om.comp (MonoidHom.inr _ _)) f fun k hk => hF f hf 1 (one_mem_hyp S P) k hk
  constructor
  · intro h f hf
    rw [← eS f hf, ← eT f hf]
    exact h f ((hv f).2 hf)
  · intro h f hf
    have hf' := (hv f).1 hf
    rw [eS f hf', eT f hf']
    exact h f hf'

end GlobalTheory.Hk3.ConjMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacua_matching_conjugatePrime : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → (∀ f, IsVacAt ψ S T (conjPl P) f ↔ IsVacAt ψ S T P f) ∧ (VacFix ψ om P → VacFix ψ om (conjPl P) ∧ ∀ cS cT, Match ψ om (conjPl P) cS cT ↔ Match ψ om P (dualC cS) (dualC cT)) := by
  first | exact @GlobalTheory.Hk3.ConjMatch.match_conj | exact GlobalTheory.Hk3.ConjMatch.match_conj | (intros; apply GlobalTheory.Hk3.ConjMatch.match_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLowerBlockFlag
namespace GlobalTheory.LowerBlockFlag

def f0 {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) × Fin (d i) ≃ Fin a) (c : Fin s) :
    Submodule k (Fin a → k) where
  carrier := {v | ∀ p : Fin a, c < GlobalTheory.SmGL.blk e p → v p = 0}
  add_mem' {u v} hu hv p hp := by
    rw [Pi.add_apply, hu p hp, hv p hp, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r {v} hv p hp := by
    rw [Pi.smul_apply, hv p hp, smul_zero]

end GlobalTheory.LowerBlockFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizer
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.UnipFlag

open Matrix

variable {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ}

def lowSpan (e : (Σ i, Fin (d i)) ≃ Fin a) (c : Fin s) : Submodule k (Fin a → k) :=
  GlobalTheory.LowerBlockFlag.f0 e c

theorem exists_sub (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a)
    (hne : GlobalTheory.SmGL.unipRad k e ≠ ⊥) :
    ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k,
      (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) →
      (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  have hex : ∃ u ∈ GlobalTheory.SmGL.unipRad k e, u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne ((Subgroup.eq_bot_iff_forall _).2 h)
  obtain ⟨u, hu, hu1⟩ := hex
  have hij : ∃ i j, (u : Matrix (Fin a) (Fin a) k) i j ≠ (1 : Matrix (Fin a) (Fin a) k) i j := by
    by_contra h
    push_neg at h
    exact hu1 (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hij
  obtain ⟨hp, hd⟩ := GlobalTheory.SmGL.mem_unipRad.1 hu
  have hlt : GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := by
    rcases lt_trichotomy (GlobalTheory.SmGL.blk e i) (GlobalTheory.SmGL.blk e j) with h | h | h
    · exact h
    · exfalso
      obtain ⟨⟨b, i'⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b', j'⟩, rfl⟩ := e.surjective j
      simp only [GlobalTheory.SmGL.blk_apply] at h
      subst h
      apply hij
      rw [hd]
      simp [Matrix.one_apply]
    · exfalso
      apply hij
      rw [GlobalTheory.SmGL.mem_parab.1 hp i j h, one_apply_ne (by rintro rfl; exact lt_irrefl _ h)]
  refine ⟨lowSpan e (GlobalTheory.SmGL.blk e i), ?_, ?_, ?_⟩
  · intro hb
    have hm : Pi.single i (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := fun p hp' =>
      Pi.single_eq_of_ne (by rintro rfl; exact lt_irrefl _ hp') _
    rw [hb] at hm
    simpa using congrFun ((Submodule.mem_bot k).1 hm) i
  · intro ht
    have hm : Pi.single j (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := ht ▸ Submodule.mem_top
    have := hm j hlt
    simp at this
  · intro g h1 h2
    have key : ∀ p q, ¬ (GlobalTheory.SmGL.blk e p < GlobalTheory.SmGL.blk e q) →
        ((g : Matrix (Fin a) (Fin a) k) - 1) p q = 0 := by
      intro p q hpq
      have hcol : ((g : Matrix (Fin a) (Fin a) k) - 1) p q =
          (((g : Matrix (Fin a) (Fin a) k) - 1) *ᵥ Pi.single q 1) p := by
        simp [Matrix.mulVec_single_one]
      rw [hcol]
      by_cases hq : GlobalTheory.SmGL.blk e q ≤ GlobalTheory.SmGL.blk e i
      · rw [h2 _ (fun r hr => Pi.single_eq_of_ne (by rintro rfl; exact absurd hq (not_le.2 hr)) _)]
        rfl
      · exact h1 _ p (lt_of_lt_of_le (not_le.1 hq) (not_lt.1 hpq))
    have hg : ∀ p q, (g : Matrix (Fin a) (Fin a) k) p q =
        (1 : Matrix (Fin a) (Fin a) k) p q + ((g : Matrix (Fin a) (Fin a) k) - 1) p q := by
      intro p q
      simp
    refine GlobalTheory.SmGL.mem_unipRad.2 ⟨GlobalTheory.SmGL.mem_parab.2 fun p q hqp => ?_, fun b p q => ?_⟩
    · rw [hg, key p q (not_lt.2 hqp.le), one_apply_ne (by rintro rfl; exact lt_irrefl _ hqp), add_zero]
    · rw [hg, key _ _ (by simp), add_zero]
      simp [Matrix.one_apply]

end GlobalTheory.UnipFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentRadicalFlagStabilizerStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_flag_stabilizer : ∀ (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a), GlobalTheory.SmGL.unipRad k e ≠ ⊥ → ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k, (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) → (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  first | exact @GlobalTheory.UnipFlag.exists_sub | exact GlobalTheory.UnipFlag.exists_sub | (intros; apply GlobalTheory.UnipFlag.exists_sub; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenform
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenform
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

open GlobalTheory.SmGL.EmptyBlocks GlobalTheory.SmGL.Exponents

namespace GlobalTheory.EigenSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jac_mk {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (a : α) × m a ≃ n) (π : Representation ℂ (GL n k) V) (g : Levi k m) (v : V) :
    SmGL.jac e π g (Submodule.Quotient.mk v) =
      (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk (π (leviEmb k e g) v) : Jacquet π (unipRad k e)) := rfl

theorem jacB_mk {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (t : n → kˣ) (v : V) :
    jacB π t (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun _ : n => Unit) (leviTorus k n t))⁻¹ : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (π (leviEmb k (points n) (leviTorus k n t)) v) : Jacquet π (unipB k n)) := rfl

theorem leviTorus_eq {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] (t : n → kˣ) :
    leviTorus k n t = torusToLevi k (points n) t := by
  funext j; ext a b
  rw [val_torusToLevi]
  simp [leviTorus, points, Matrix.diagonal]

theorem eq_torusToLevi (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    g = torusToLevi k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
  funext j; ext a b
  rw [val_torusToLevi]
  fin_cases a; fin_cases b
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

theorem deltaHalf_eq (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    deltaHalf k (fun _ : Fin n => Fin 1) g =
      deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (fun j => Matrix.GeneralLinearGroup.det (g j))) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => by simp), modExp_fin (fun _ : Fin n => Unit) (fun _ => by simp)]
  exact congrArg _ (congrFun ((leviTorus k (Fin n)).symm_apply_apply (fun j => Matrix.GeneralLinearGroup.det (g j))) a).symm

theorem inSupport_of_eigenform (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ)
    (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t y, l (jacB π t y) = (SmGL.torusChar ψ t : ℂ) * l y) (i : Fin n) : InSupport π (ψ i) := by
  let f := Equiv.sigmaUnique (Fin n) fun _ : Fin n => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h : unipRad k f = unipB k (Fin n) := unipRad_eq k f hmono
  let l' : Jacquet π (unipRad k f) →ₗ[ℂ] ℂ :=
    (twKer π (unipRad k f) 1).liftQ (l ∘ₗ (twKer π (unipB k (Fin n)) 1).mkQ) (by
      rw [h]; intro x hx
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hx])
  have hl' : ∀ v : V, l' (Submodule.Quotient.mk v) = l (Submodule.Quotient.mk v) := fun v => rfl
  let χ : Levi k (fun _ : Fin n => Fin 1) →* ℂˣ := leviChar _ ψ
  have key : ∀ (g : Levi k (fun _ : Fin n => Fin 1)) (v : V),
      l' (SmGL.jac f π g (Submodule.Quotient.mk v)) = (χ g : ℂ) * l' (Submodule.Quotient.mk v) := by
    intro g v
    set t : Fin n → kˣ := fun j => Matrix.GeneralLinearGroup.det (g j) with ht
    have h1 := hl t (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n)))
    rw [jacB_mk, map_smul, leviTorus_eq, leviEmb_torusToLevi, ← leviTorus_eq] at h1
    have hEmb : leviEmb k f g = diagT k (Fin n) t := by
      conv_lhs => rw [eq_torusToLevi n g]
      exact leviEmb_torusToLevi k f t
    rw [jac_mk, map_smul, hl', hl', deltaHalf_eq n g, hEmb, ← ht]
    have hc : (χ g : ℂ) = (SmGL.torusChar ψ t : ℂ) := by
      simp [χ, leviChar_apply, torusChar_apply, t]
    rw [hc, ← h1]
  refine ⟨n, fun _ => 1, f, i, rfl, ℂ, inferInstance, inferInstance, ofChar χ, isIrreducible_ofChar χ, ?_, ?_⟩
  · refine IsSubquotient.of_surjective ⟨l', fun g => ?_⟩ ?_
    · apply Submodule.linearMap_qext
      ext v
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [key, ofChar_apply]
    · obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
        by_contra hc; push_neg at hc; exact hl0 (LinearMap.ext hc)
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      intro c
      refine ⟨(c / l (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, ?_⟩
      show l' _ = c
      rw [map_smul, hl', smul_eq_mul, div_mul_cancel₀ _ hx]
  · intro g y
    rw [ofChar_apply]
    simp [χ, leviChar_apply, Pi.mulSingle_apply, apply_ite, Finset.prod_ite_eq']

end GlobalTheory.EigenSupport

theorem GlobalTheory.EigenSupport.inSupport_of_torus_eigenform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 → (∀ t y, l (jacB π t y) = (SmGL.torusChar ψ t : ℂ) * l y) → ∀ i, InSupport π (ψ i) := by
  intro k _ _ _ _ n V _ _ π ψ l hl0 hl i
  exact GlobalTheory.EigenSupport.inSupport_of_eigenform n V π ψ l hl0 hl i
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSupercuspidalSupportOfTorusJacquetEigenformStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_supercuspidalSupport_of_torus_jacquet_eigenform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 → (∀ t y, l (jacB π t y) = (GlobalTheory.SmGL.torusChar ψ t : ℂ) * l y) → ∀ i, InSupport π (ψ i) := by
  first | exact @GlobalTheory.EigenSupport.inSupport_of_torus_eigenform | exact GlobalTheory.EigenSupport.inSupport_of_torus_eigenform | (intros; apply GlobalTheory.EigenSupport.inSupport_of_torus_eigenform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DualSplitRel

open Formalism.L2.NTheta GlobalTheory.SplitPlace

section Abstract

variable {G : Type} [Group G]

theorem coset_mul [DecidableEq G] {K : Set G} {z α : G} {R : Finset G} (hz : ∀ k ∈ K, k * z = z * k)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    (∀ γ ∈ R.image (· * z), ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * (α * z) * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * (α * z) * k₂) → ∃! γ, γ ∈ R.image (· * z) ∧ γ⁻¹ * x ∈ K := by
  have conj : ∀ k ∈ K, z⁻¹ * k * z = k := fun k hk => by rw [mul_assoc, hz k hk, inv_mul_cancel_left]
  have conj' : ∀ k ∈ K, z * k * z⁻¹ = k := fun k hk => by rw [← hz k hk, mul_inv_cancel_right]
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨k₁, a₁, k₂, a₂, rfl⟩ := h1 δ hδ
    refine ⟨k₁, a₁, k₂, a₂, ?_⟩
    simp only [mul_assoc, hz k₂ a₂]
  · rintro _ ⟨k₁, a₁, k₂, a₂, rfl⟩
    have ex : k₁ * (α * z) * k₂ = k₁ * α * k₂ * z := by
      simp only [mul_assoc, hz k₂ a₂]
    obtain ⟨γ, ⟨hγ, hw⟩, hu⟩ := h2 (k₁ * α * k₂) ⟨k₁, a₁, k₂, a₂, rfl⟩
    refine ⟨γ * z, ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩
    · have := conj _ hw
      rw [ex]
      convert hw using 1
      rw [← this]
      group
    · rintro _ ⟨hm, hw'⟩
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hm
      rw [hu δ ⟨hδ, ?_⟩]
      have := conj' _ hw'
      rw [ex] at this hw'
      convert hw' using 1
      rw [← this]
      group

theorem coset_one (K : Subgroup G) :
    (∀ γ ∈ ({1} : Finset G), ∃ k₁ ∈ (K : Set G), ∃ k₂ ∈ (K : Set G), γ = k₁ * 1 * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ (K : Set G), ∃ k₂ ∈ (K : Set G), x = k₁ * 1 * k₂) →
        ∃! γ, γ ∈ ({1} : Finset G) ∧ γ⁻¹ * x ∈ (K : Set G) := by
  refine ⟨fun γ hγ => ⟨1, one_mem K, 1, one_mem K, by simpa using hγ⟩, ?_⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using mul_mem ha hb⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩

theorem eq_scalar {B n : Type} [CommRing B] [Fintype n] [DecidableEq n] (b : GL n B) {m : Matrix n n B} {c : B}
    (h : (b⁻¹).1 * m * b.1 = Matrix.scalar n c) : m = Matrix.scalar n c := by
  have h1 : m = b.1 * ((b⁻¹).1 * m * b.1) * (b⁻¹).1 := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h1, h, ← (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem scalar_parts {A B n : Type} [CommRing A] [CommRing B] [Fintype n] [DecidableEq n] (π : A →+* B) (t : B → A) (E c : A)
    (h3 : ∀ x, t (π x) = E * x) (m : Matrix n n A) (h5 : m.map π = Matrix.scalar n (π c)) :
    E • m = (E * c) • (1 : Matrix n n A) := by
  refine Matrix.ext fun i j => ?_
  have h8 : π (m i j) = π (c * (1 : Matrix n n A) i j) := by
    refine (congrFun (congrFun h5 i) j).trans ?_
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Matrix.one_apply]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc, ← h3, ← h3, h8]

end Abstract

section Divisors

variable {R : Type} [CommRing R] {n : ℕ}

theorem dv_scalar {Λ : (Fin n → R) → Prop} {O : R → Prop} {e c : R} {u u' : Fin n → R} {A Z : Matrix (Fin n) (Fin n) R}
    (hz : e • Z = (e * c) • (1 : Matrix (Fin n) (Fin n) R)) (hu : ∀ i, u' i = c * u i)
    (h : GlobalTheory.DivDual.Dv Λ O e u A) : GlobalTheory.DivDual.Dv Λ O e u' (A * Z) := by
  obtain ⟨B, b1, b2, b3, b4⟩ := h
  have core : ∀ y, e • (A * Z).mulVec y = c • e • A.mulVec y := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.smul_mulVec, hz, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, mul_comm]
  have core2 : ∀ w : Fin n → R, e • B.mulVec (fun i => u' i * w i) = c • e • B.mulVec (fun i => u i * w i) := fun w => by
    have : (fun i => u' i * w i) = c • fun i => u i * w i := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, hu, mul_assoc]
    rw [this, Matrix.mulVec_smul, smul_comm]
  refine ⟨B, b1, b2, fun y hy => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw, e1⟩ := b3 y hy
    exact ⟨w, hw, by rw [core, core2, e1]⟩
  · obtain ⟨y, hy, e1⟩ := b4 w hw
    exact ⟨y, hy, by rw [core, core2, e1]⟩

end Divisors

variable {D : D7}

theorem exists_idem {P : Pl D.host.E} (hP : conjPl P ≠ P) : ∃ e : AE D, IsIdemAt e P := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact ⟨e, h⟩
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem idem_unique {P : Pl D.host.E} {e e' f' : AE D} (he : IsIdemAt e P) (h : IsPrimeIdem P e' f') :
    f' = e + cA D e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨hd, ε, hε, h1⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨hd', ε', hε', h1'⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  rw [h1, h1', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]

theorem hyp_eq_locPart {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) (V : HSp D) :
    hyp V P = locPart V (KsphC V ∅) e := by
  refine Set.ext fun k => ⟨?_, fun h => ⟨h.1, e, e + cA D e, Or.inl ⟨he, rfl⟩, h.2⟩⟩
  rintro ⟨h1, e', f', h2, h3⟩
  rw [idem_unique he h2] at h3
  exact ⟨h1, h3⟩

theorem exists_central {e : AE D} (he : IsSplitIdem D e) (V : HSp D) {ϖ : D.host.E} (h0 : ϖ ≠ 0) :
    ∃ z : GA D V, SuppAt e V z ∧ (∀ k, SuppAt e V k → k * z = z * k) ∧
      finPart D e • fm V z = (finPart D e * finPart D (incA D ϖ⁻¹)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (RF D)) := by
  obtain ⟨v, π, s, h1, h2, h3, h4, -⟩ := GlobalTheory.SplitCoord.exists_coord e he
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1 h2 h3 h4 (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨hex, hinj⟩ := comp_bij (V := V) (B := B) he h1 h2
  have hu : ∀ x : D.host.E, x ≠ 0 → π (finPart D (incA D x)) ≠ 0 := fun x hx h => by
    have := congrArg π (congrArg (finPart D) (congrArg (incA D) (mul_inv_cancel₀ hx)))
    rw [map_mul, map_mul, map_mul, h, zero_mul, map_one, map_one, map_one] at this
    exact zero_ne_one this
  let t : (Fv D.host.F v)ˣ := Units.mk0 _ (hu _ (inv_ne_zero h0))
  let a : GL (Fin V.rank) (Fv D.host.F v) := Units.map (Matrix.scalar (Fin V.rank)).toMonoidHom t
  have ha : a.1 = Matrix.scalar (Fin V.rank) (π (finPart D (incA D ϖ⁻¹))) := rfl
  obtain ⟨z, hs, hz⟩ := hex a
  refine ⟨z, hs, fun k hk => hinj _ _ (suppAt_mul hk hs) (suppAt_mul hs hk) ?_, ?_⟩
  · rw [map_mul, map_mul, hz]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, ha]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq.symm
  · have h6 := comp_val (V := V) (π := π) (B := B) z
    rw [hz, ha] at h6
    exact scalar_parts π (fun w => finPart D (s w)) _ _ h3 _ (eq_scalar B h6.symm)

theorem divAt_mul {e : AE D} {V : HSp D} {ϖ : D.host.E} (h0 : ϖ ≠ 0) {z g : GA D V} {d : List ℤ}
    (hz : finPart D e • fm V z = (finPart D e * finPart D (incA D ϖ⁻¹)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (RF D)))
    (h : DivAt V e ϖ d g) : DivAt V e ϖ (d.map (· - 1)) (g * z) := by
  rw [GlobalTheory.DivDual.divAt_iff] at h ⊢
  obtain ⟨hd, h⟩ := h
  refine ⟨by simpa using hd, ?_⟩
  rw [show finMat D.sp.cm.sig V.gram (g * z) = fm V g * fm V z from fm_mul V g z]
  refine dv_scalar hz (fun i => ?_) h
  have hi : i.1 < d.length := by rw [hd]; exact i.2
  have gd : (d.map (· - 1)).getD i.1 0 = d.getD i.1 0 - 1 := by
    simp [List.getD_eq_getElem _ _ hi, hi]
  rw [gd, zpow_sub_one₀ h0, mul_comm, RingHom.map_mul, RingHom.map_mul]

theorem label_shift {n j : ℕ} (hj : j ≤ n) : (dualLab (splitLab n j)).map (· - 1) = splitLab n (n - j) := by
  simp [dualLab, splitLab, Nat.sub_sub_self hj]

theorem label_shift_zero (n : ℕ) : (List.replicate n (0 : ℤ)).map (· - 1) = splitLab n n := by
  simp [splitLab]

theorem sphOp_of {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) {V : HSp D} {d : List ℤ} (hd : d.Pairwise fun a b => b ≤ a) {α : GA D V}
    (hα : SuppAt e V α) (hD : DivAt V e (ϖ : D.host.E) d α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : SphOp V P d R :=
  ⟨e, e + cA D e, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), Or.inl ⟨he, rfl⟩, h1, h2, hd,
    fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hD, hR, hc⟩

theorem dual_rel : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ j, j ≤ V.rank → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (dualLab (splitLab V.rank j)) 1) (opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) u) = opOf π P (Finsupp.single (splitLab V.rank (V.rank - j)) 1) u := by
  classical
  intro D V P hP j hj M _ _ π u hu
  obtain ⟨e, he⟩ := exists_idem hP
  obtain ⟨-, ϖ, -, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, hc, hz⟩ := exists_central he.1 V h0
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  have hKl : locPart V (KsphC V ∅) e = (K : Set (GA D V)) := (hyp_eq_locPart he V).symm.trans hK
  have hKz : ∀ k ∈ locPart V (KsphC V ∅) e, k * z = z * k := fun k hk => hc k hk.2
  obtain ⟨-, hrep, hH⟩ := GlobalTheory.SplitPlace.split_local V P e he
  obtain ⟨α, hα⟩ := (hH ϖ h1 h2).1 j hj
  obtain ⟨R, r1, r2⟩ := hrep α hα.2.1
  have hDα : DivAt V e (ϖ : D.host.E) (dualLab (splitLab V.rank j)) α := by
    have := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0
      (GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ j α he h1 h2 hj hα)).1
    rwa [inv_inv] at this
  have c1 := (GlobalTheory.SphLabelOps.label_operators V P).1
  have shift : ∀ {d : List ℤ} {g : GA D V} {R' : Finset (GA D V)}, SuppAt e V g → DivAt V e (ϖ : D.host.E) d g →
      (∀ γ ∈ R', SuppAt e V γ) → IsCosetRep V (locPart V (KsphC V ∅) e) g R' →
      (d.map (· - 1)).Pairwise (fun a b => b ≤ a) → SphOp V P (d.map (· - 1)) (R'.image (· * z)) := by
    intro d g R' sg dg sR hr hp
    obtain ⟨a, b⟩ := coset_mul hKz (fun γ hγ => (hr.1 γ hγ).2) hr.2
    have sup : ∀ γ ∈ R'.image (· * z), SuppAt e V γ := fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      exact suppAt_mul (sR δ hδ) hs
    exact sphOp_of he h1 h2 hp (suppAt_mul sg hs) (divAt_mul h0 hz dg) sup
      ⟨fun γ hγ => ⟨mem_GfC he.1 (sup γ hγ), a γ hγ⟩, b⟩
  have one : IsCosetRep V (locPart V (KsphC V ∅) e) 1 {1} := by
    have := coset_one K
    rw [← hKl] at this
    refine ⟨fun γ hγ => ⟨?_, this.1 γ hγ⟩, this.2⟩
    rw [Finset.mem_singleton.1 hγ]
    exact one_mem _
  have S0 := shift (GlobalTheory.SplitHecke.suppAt_one V)
    (GlobalTheory.SphLabelOps.divAt_one V he.1.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (Or.inl ⟨he, rfl⟩)) (ϖ : D.host.E))
    (fun γ hγ => by rw [Finset.mem_singleton.1 hγ]; exact GlobalTheory.SplitHecke.suppAt_one V) one
    (by rw [label_shift_zero]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift_zero] at S0
  have S1 : SphOp V P (dualLab (splitLab V.rank j)) R := sphOp_of he h1 h2
    (by simp [dualLab, splitLab, List.pairwise_append, List.pairwise_replicate]) hα.2.1 hDα r1 r2
  have S2 := shift hα.2.1 hDα r1 r2
    (by rw [label_shift hj]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift hj] at S2
  have fixw : ∀ k ∈ hyp V P, π k (π z u) = π z u := fun k hk => by
    have hk' : k ∈ locPart V (KsphC V ∅) e := by rw [← hyp_eq_locPart he V]; exact hk
    have := congrArg (fun g => π g u) (hKz k hk')
    simp only [map_mul, Module.End.mul_apply, hu k hk] at this
    exact this
  have inj : Function.Injective (· * z : GA D V → GA D V) := mul_left_injective z
  have A := (c1 _ _ S0).2 M π u hu
  have Bq := (c1 _ _ S1).2 M π _ fixw
  have C := (c1 _ _ S2).2 M π u hu
  rw [← A, ← C, Finset.sum_image inj.injOn, Finset.sum_image inj.injOn, Finset.sum_singleton, one_mul, ← Bq]
  exact Finset.sum_congr rfl fun γ _ => by rw [map_mul, Module.End.mul_apply]

end GlobalTheory.DualSplitRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualSplitLabel_operator_mul_scalar_operator : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ j, j ≤ V.rank → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (dualLab (splitLab V.rank j)) 1) (opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) u) = opOf π P (Finsupp.single (splitLab V.rank (V.rank - j)) 1) u := by
  first | exact @GlobalTheory.DualSplitRel.dual_rel | exact GlobalTheory.DualSplitRel.dual_rel | (intros; apply GlobalTheory.DualSplitRel.dual_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLtOneOfResidue
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PointStabilizer

def stab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a v = v := ha
    have hb' : ρ b v = v := hb
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : ρ a v = v := ha
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_of_residue {x : 𝒪[k]} (hx : IsLocalRing.residue 𝒪[k] x = 0) :
    valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one] at hx
  exact lt_of_le_of_ne x.2 hx

theorem entry_of_mem_KOne {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) (i j : Fin n) :
    valuation k (g.val i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) h = 1 := hh
  have h2 : IsLocalRing.residue 𝒪[k] (h.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have := congrArg (fun u : GL (Fin n) _ => u.val i j) h1
    simpa using this
  have h3 : IsLocalRing.residue 𝒪[k] (h.val i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = 0 := by
    rw [map_sub, h2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have h4 := val_lt_one_of_residue h3
  rw [map_sub] at h4
  have h5 : algebraMap 𝒪[k] k ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  rw [h5] at h4
  exact h4

def pts (n : ℕ) : (Σ _ : Fin n, Fin 1) ≃ Fin n := Equiv.sigmaUnique (Fin n) fun _ => Fin 1

theorem unipRad_pts (n : ℕ) : unipRad k (pts n) = unipB k (Fin n) :=
  GlobalTheory.SmGL.EmptyBlocks.unipRad_eq k (pts n) (fun _ _ h => h)

theorem mk_ne_zero (H : GlobalTheory.Published.DepthZeroJacquetInjective) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : GlobalTheory.SplitRead.Irr k n) (v : π.V)
    (θ : Fin n → kˣ →* ℂˣ) (hv : v ≠ 0) (hI : GlobalTheory.TameIwahori.IsIwVec θ π.π v) :
    Submodule.Quotient.mk v ≠ (0 : π.V ⧸ twKer π.π (unipB k (Fin n)) 1) := by
  intro h0
  have hle : KOne k (Fin n) ⊔ (unipRad k (pts n) ⊓ KO k (Fin n)) ≤ stab π.π v := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · refine hI.1 g (iwahori_le_KO k (Fin n) (KOne_le_iwahori k (Fin n) hg)) (fun i j hij => ?_) (fun i => ?_)
      · simpa [Matrix.one_apply_ne hij.ne'] using entry_of_mem_KOne hg i j
      · simpa using entry_of_mem_KOne hg i i
    · have hu := (mem_unipB k).1 (unipRad_pts (k := k) n ▸ hg.1)
      refine hI.1 g hg.2 (fun i j hij => ?_) (fun i => ?_)
      · rw [hu.1 i j hij]; simp
      · rw [hu.2 i]; simp
  refine hv (H k n n (fun _ => 1) (pts n) π v (fun g => ?_) ?_)
  · have : π.π g v = v := hle g.2
    simpa using this
  · rw [Submodule.Quotient.mk_eq_zero] at h0 ⊢
    rw [unipRad_pts]
    exact h0

end GlobalTheory.PointStabilizer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZero
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TameIwahori.JacquetNonzero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jacquet_mk_ne_zero (hp : GlobalTheory.Published.DepthZeroJacquetInjective)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ) (hv : v ≠ 0) (hI : IsIwVec θ π.π v) :
    (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.PointStabilizer.mk_ne_zero
  | exact _root_.GlobalTheory.PointStabilizer.mk_ne_zero
  | (apply _root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PointStabilizer.mk_ne_zero ..)

end GlobalTheory.TameIwahori.JacquetNonzero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZeroStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ), v ≠ 0 → IsIwVec θ π.π v → (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | exact GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | (intros; apply GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero <;> assumption)
end
end
