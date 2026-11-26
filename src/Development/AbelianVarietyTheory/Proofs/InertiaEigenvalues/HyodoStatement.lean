module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
noncomputable section

namespace GlobalTheory.HyodoDef

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def geometricCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ b : V ⊗[Qp] BdR, ∀ g, c g ⊗ₜ[Qp] (1 : BdR) = actVdR PD ρ g b - b}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def crystallineCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x ∧
    ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, map_zero _, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hxφ, hx⟩ ⟨hb, y, hyφ, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, by rw [map_add (f := _), hxφ, hyφ], fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hxφ, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, by rw [map_smul, hxφ], fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

end GlobalTheory.HyodoDef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairing
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

noncomputable section
namespace GlobalTheory.DualTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
  {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]

def dualEquiv : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₗ[ℚ_[l]] Module.Dual ℚ_[l] V :=
  (Module.finBasis ℚ_[l] V).dualBasis.equivFun.symm

theorem dualEquiv_basis (z : Fin (finrank ℚ_[l] V) → ℚ_[l]) (i : Fin (finrank ℚ_[l] V)) :
    dualEquiv z (Module.finBasis ℚ_[l] V i) = z i := by
  simp [dualEquiv, Basis.equivFun_symm_apply, Finset.sum_apply, Basis.dualBasis_apply_self, Finsupp.single_apply]

theorem dualEquiv_symm_apply (f : Module.Dual ℚ_[l] V) (i : Fin (finrank ℚ_[l] V)) :
    (dualEquiv (V := V)).symm f i = f (Module.finBasis ℚ_[l] V i) := by
  conv_rhs => rw [← (dualEquiv (V := V)).apply_symm_apply f]
  rw [dualEquiv_basis]

def chiS (g : ↥(GK K)) : ℚ_[l] := ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])

theorem chiS_mul (g h : ↥(GK K)) : chiS P K (g * h) = chiS P K g * chiS P K h := by
  simp [chiS]

theorem chiS_one : chiS P K 1 = 1 := by simp [chiS]

def dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) :
    (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun y := chiS P K g • (dualEquiv (V := V)).symm ((dualEquiv y).comp (ρ g⁻¹))
  map_add' y z := by simp [LinearMap.add_comp, smul_add]
  map_smul' c y := by simp [LinearMap.smul_comp, smul_comm c]

theorem dualEquiv_dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (y) :
    dualEquiv (dualOp P K ρ g y) = chiS P K g • (dualEquiv y).comp (ρ g⁻¹) := by
  simp [dualOp]

def dualRep (ρ : Representation ℚ_[l] ↥(GK K) V) :
    Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun g := dualOp P K ρ g
  map_one' := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [dualEquiv_dualOp]
    simp [chiS_one, Module.End.one_eq_id]
  map_mul' g h := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [Module.End.mul_apply, dualEquiv_dualOp, dualEquiv_dualOp, dualEquiv_dualOp, chiS_mul,
      mul_inv_rev, map_mul, Module.End.mul_eq_comp, LinearMap.smul_comp, smul_smul, LinearMap.comp_assoc]

def dualPair : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l] :=
  (dualEquiv (V := V)).toLinearMap.flip

theorem dualPair_apply (x : V) (y : Fin (finrank ℚ_[l] V) → ℚ_[l]) : dualPair x y = dualEquiv y x := rfl

end GlobalTheory.DualTwist

namespace GlobalTheory.DualTwist
variable {l : ℕ} [Fact l.Prime]

theorem chiS_eq (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    chiS P K g = (P.χQ (g : GQ l) : ℚ_[l]) := by
  simp [chiS, cycLL, P.PD_χ]

theorem chiS_cont (P : LocPrime l) (K : FinExt l) : Continuous (chiS P K) := by
  have h : chiS P K = fun g : ↥(GK K) => (P.χQ (g : GQ l) : ℚ_[l]) := funext (chiS_eq P K)
  rw [h]
  exact (GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val

theorem exists_dual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → ∃ (ρ' : Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l])) (m : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]), (∀ y, Continuous fun g => ρ' g y) ∧ IsDual1 (P.PD K) ρ ρ' m := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  refine ⟨dualRep P K ρ, dualPair, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    apply continuous_pi
    intro i
    have h : (fun g : ↥(GK K) => dualRep P K ρ g y i) =
        fun g => chiS P K g * dualEquiv y (ρ g⁻¹ (Module.finBasis ℚ_[l] V i)) := by
      funext g
      change dualOp P K ρ g y i = _
      simp [dualOp, dualEquiv_symm_apply]
    rw [h]
    have hy : Continuous (dualEquiv (V := V) y) :=
      IsModuleTopology.continuous_of_linearMap (dualEquiv (V := V) y)
    exact (chiS_cont P K).mul (hy.comp ((hc _).comp continuous_inv))
  · intro g x y
    change dualEquiv (dualOp P K ρ g y) (ρ g x) = chiS P K g * dualEquiv y x
    rw [dualEquiv_dualOp, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, smul_eq_mul]
  · intro x hx
    apply (Module.finBasis ℚ_[l] V).forall_coord_eq_zero_iff.mp
    intro i
    have := hx ((dualEquiv (V := V)).symm ((Module.finBasis ℚ_[l] V).coord i))
    rwa [dualPair_apply, LinearEquiv.apply_symm_apply] at this
  · intro y hy
    funext i
    exact (dualEquiv_basis y i).symm.trans (hy _)
  · simp

end GlobalTheory.DualTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairingStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateTwistDual_perfectPairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → ∃ (ρ' : Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l])) (m : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]), (∀ y, Continuous fun g => ρ' g y) ∧ IsDual1 (P.PD K) ρ ρ' m := by
  first | exact @GlobalTheory.DualTwist.exists_dual1 | exact GlobalTheory.DualTwist.exists_dual1 | (intros; apply GlobalTheory.DualTwist.exists_dual1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddF
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompare
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompare
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoOrth

open GlobalTheory.BKOrth

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem pairT_filV_right (P : V →ₗ[LL] V' →ₗ[LL] LL) (a : ℤ) (v : V) (z : V' ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V') a) :
    pairT BdR P (v ⊗ₜ[Qp] (1 : BdR)) z ∈ FilV PD (LL := LL) (V := LL) a := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add (f := _)]; exact add_mem hy hy'
  | tmul v' f =>
    rw [AlgebraTensorModule.map_tmul, pairT_tmul, one_mul]
    exact ⟨P v v' ⊗ₜ[Qp] f, rfl⟩

theorem actVB_one (ρ : Representation LL G V) (x : V ⊗[Qp] B) : actVB PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b => simp [actVB_tmul]

end Gen

theorem cocycle_inv {G : Type} [Group G] {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]
    (ρ : Representation LL G V) (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) :
    ρ g (c g⁻¹) = - c g := by
  have h1 : c 1 = 0 := by simpa using hc 1 1
  have := hc g g⁻¹
  rw [mul_inv_cancel, h1] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem goodO_Zl (l : ℕ) [Fact l.Prime] : GoodO (Qp := ℚ_[l]) ℚ_[l] ℤ_[l] := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  exact (PadicInt.isOpenEmbedding_coe (p := l)).isOpen_range


set_option maxHeartbeats 1600000 in
theorem orth_of_cont (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V']
    [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V']
    [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V')
    (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]) (hρ' : ∀ y, Continuous fun g => ρ' g y)
    (hdR : IsDR (P.PD K) ρ') (hD : IsDual1 (P.PD K) ρ ρ' m)
    (hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]))
    (c : ↥(GK K) → V) (hc : c ∈ geometricCocycles (P.PD K) ρ) (a : ↥(GK K) → V')
    (ha : a ∈ crystallineCocycles (P.PD K) ρ') : CobL (P.PD K) (cupL ρ' m c a) := by
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨hcz, b, hb⟩ := hc
  obtain ⟨haz, β, hβφ, hβ⟩ := ha
  obtain ⟨-, d, hd, hd'⟩ :=
    GlobalTheory.CobCrisLift.coboundary_lift l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      { V := V', ρ := ρ', cont := hρ' } hdR a β hβ
  have hfixd : ∀ g, actVdR (P.PD K) ρ' g d = d := fun g => by
    have := (Submodule.mem_iInf _).1 hd g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI hT K ℚ_[l] ℚ_[l]
  obtain ⟨we, w0, hw0, hweφ, hweι⟩ := hsurj 0 (pairT P.R.BdR m b d)
  have hweφ' : φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = we := (sub_eq_zero.1 hweφ).symm
  let F : ↥(GK K) → ℚ_[l] ⊗[ℚ_[l]] P.R.B := fun h =>
    (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h we - we) -
      pairT P.R.B m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' h β)
  have hFφ : ∀ h, φVB (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) = F h := fun h => by
    have e1 : φVB (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
      simp [φVB]
    simp only [F, map_sub, pairT_φVB, e1, GlobalTheory.CobCrisLift.φVB_act, hβφ, hweφ']
  have hFι : ∀ h, ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) ∈
      FilV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) 0 := fun h => by
    have e1 : ιV (P.PD K) (LL := ℚ_[l]) (V := V) (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
      simp [ιV]
    have e2 : pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) (actVdR (P.PD K) ρ' h d) =
        actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h (pairT P.R.BdR m b d) -
          pairT P.R.BdR m b d := by
      rw [hb h, map_sub, LinearMap.sub_apply, ← pairT_actVdR (P.PD K) ρ ρ' m hD.1 h b d, hfixd h]
    have hι1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) we = pairT P.R.BdR m b d + w0 :=
      sub_eq_iff_eq_add.1 hweι
    have s1 : ιV (P.PD K) (LL := ℚ_[l]) (V := ℚ_[l]) (F h) =
        (actVdR (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) h w0 - w0) -
          pairT P.R.BdR m (c h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR))
            (actVdR (P.PD K) ρ' h (ιV (P.PD K) (LL := ℚ_[l]) (V := V') β - d)) := by
      simp only [F, map_sub, pairT_ιV, e1, GlobalTheory.CobCrisLift.ιV_act, hι1, map_add (f := _), e2]
      abel
    rw [s1]
    exact sub_mem (sub_mem (actVdR_filV (P.PD K) _ 0 h w0 hw0) hw0)
      (pairT_filV_right (P.PD K) m 0 (c h) _ (actVdR_filV (P.PD K) ρ' 0 h _ hd'))
  have hF : ∀ h, ∃ x : ℚ_[l], F h = x ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun h => hker (F h) (hFφ h) (hFι h)
  choose f hf using hF
  let bas := Module.finBasis ℚ_[l] V
  let γ : Fin (finrank ℚ_[l] V) → ↥(GK K) → ℚ_[l] := fun i g => bas.coord i (c g)
  have hγ : ∀ i, Continuous (γ i) := fun i =>
    (IsModuleTopology.continuous_of_linearMap (bas.coord i)).comp hcz.1
  let k : ↥(GK K) → ℚ_[l] := fun h => charRep (cycLL (P.PD K) ℚ_[l]) h (f h⁻¹)
  have hsum : ∀ g, k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      ∑ i, γ i g • pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β +
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (-we) - -we) := by
    intro g
    have ec : c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = ∑ i, γ i g • (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
      conv_lhs => rw [← bas.sum_repr (c g)]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul']
      rfl
    have ek : k g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F g⁻¹) := by
      rw [hf g⁻¹, actVB_tmul, map_one]
    have e3 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (pairT P.R.B m (c g⁻¹ ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g⁻¹ β)) =
        -pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β := by
      rw [← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, ← actVB_mul, mul_inv_cancel, actVB_one, actVB_tmul,
        map_one, cocycle_inv ρ c hcz.2 g, neg_tmul, map_neg, LinearMap.neg_apply]
    have e4 : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g
        (actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g⁻¹ we) = we := by
      rw [← actVB_mul, mul_inv_cancel, actVB_one]
    rw [ek]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sub, e3, e4, map_neg, ec, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply]
    abel
  have hk : Continuous k :=
    GlobalTheory.FundCont.contCore_tied l P AI hT K ℚ_[l] ℤ_[l] (goodO_Zl l)
      (charGRep (Qp := ℚ_[l]) (O := ℤ_[l]) (cycLL (P.PD K) ℚ_[l]) hχ) _
      (fun i => pairT P.R.B m (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) β) γ hγ (-we) k hsum
  have hfk : f = fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * k g⁻¹ := by
    funext g
    simp only [k, charRep_apply, inv_inv]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]
  have hcont : Continuous f := by
    rw [hfk]
    exact hχ.mul (hk.comp continuous_inv)
  refine ⟨f, hcont, ?_⟩
  funext ⟨g, h⟩
  have hcup : cupL ρ' m c a (g, h) = m (c g) (ρ' g (a h)) := rfl
  rw [hcup]
  apply tmul_one_injective (P.PD K) (LL := ℚ_[l])
  beta_reduce
  have hd1 : ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h) =
      charRep (cycLL (P.PD K) ℚ_[l]) g (f h) - f (g * h) + f g := rfl
  have hact : (charRep (cycLL (P.PD K) ℚ_[l]) g (f h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
    rw [actVB_tmul, map_one]
  have hch : actVB (P.PD K) ρ g (c h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [actVB_tmul, map_one]
  have hcoc : c (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) + ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [hcz.2 g h, add_tmul]
  have hrhs : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    have e : (m (c g) (ρ' g (a h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g (a h ⊗ₜ[ℚ_[l]] (1 : P.R.B))) := by
      rw [actVB_tmul, map_one, pairT_tmul, mul_one]
    rw [e, hβ h, map_sub, map_sub]
  have main : actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g =
      pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B))
          (actVB (P.PD K) ρ' g (actVB (P.PD K) ρ' h β)) -
        pairT P.R.B m (c g ⊗ₜ[ℚ_[l]] (1 : P.R.B)) (actVB (P.PD K) ρ' g β) := by
    simp only [F, map_sub, actVB_mul, hcoc, map_add (f := _), LinearMap.add_apply,
      ← pairT_actVB (P.PD K) ρ ρ' m hD.1 g, hch]
    abel
  calc (ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) ℚ_[l])) f (g, h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
      = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) -
          f (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) + f g ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
        rw [hd1, tmul_one_sub_add, hact]
    _ = actVB (P.PD K) (charRep (cycLL (P.PD K) ℚ_[l])) g (F h) - F (g * h) + F g := by
        rw [hf h, hf (g * h), hf g]
    _ = _ := main
    _ = _ := hrhs.symm

theorem hyodo_orth : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → ∀ c ∈ geometricCocycles (P.PD K) ρ, ∀ a ∈ crystallineCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m c a) := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hρ hρ' hdR hD c hc a ha
  by_cases hV : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨v', hv'⟩ : ∃ v', m v v' ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (hD.2.1 v h)
    have hm : Continuous fun p : V × V' => m p.1 p.2 :=
      IsModuleTopology.continuous_bilinear_of_finite_left m
    have hχ : Continuous fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      have e : (fun g => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) =
          fun g => m (ρ g v) (ρ' g v') * (m v v')⁻¹ := by
        funext g
        rw [hD.1, mul_assoc, mul_inv_cancel₀ hv', mul_one]
      rw [e]
      exact (hm.comp ((hρ v).prodMk (hρ' v'))).mul continuous_const
    exact orth_of_cont l P AI hT K V ρ V' ρ' m hρ' hdR hD hχ c hc a ha
  · push_neg at hV
    refine ⟨0, continuous_const, funext fun x => ?_⟩
    simp [cupL, hV (c x.1), ReciprocityTheory.Def.d1]

end GlobalTheory.HyodoOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCocycleDimensionCompareStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_cocycle_dimension_compare : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → ∀ c ∈ geometricCocycles (P.PD K) ρ, ∀ a ∈ crystallineCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m c a) := by
  first | exact @GlobalTheory.HyodoOrth.hyodo_orth | exact GlobalTheory.HyodoOrth.hyodo_orth | (intros; apply GlobalTheory.HyodoOrth.hyodo_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAnnihilatorAdd
open Module

namespace GlobalTheory.HyodoDef.PairLin

variable {k M M' : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [FiniteDimensional k M] [FiniteDimensional k M']

theorem finrank_annihilator_add (β : M →ₗ[k] M' →ₗ[k] k) (S : Submodule k M')
    (hS : LinearMap.ker β.flip ≤ S) :
    finrank k (LinearMap.ker (S.subtype.dualMap ∘ₗ β)) + finrank k S
      = finrank k M + finrank k (LinearMap.ker β.flip) := by
  set φ : M →ₗ[k] Dual k S := S.subtype.dualMap ∘ₗ β with hφ
  set ψ : S →ₗ[k] Dual k M := β.flip ∘ₗ S.subtype with hψ
  have hφψ : φ = ψ.dualMap ∘ₗ (Module.evalEquiv k M).toLinearMap := by
    ext a s; rfl
  have hrange : LinearMap.range φ = LinearMap.range ψ.dualMap := by
    rw [hφψ, LinearEquiv.range_comp]
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_range_add_finrank_ker ψ
  have h3 : finrank k (LinearMap.range φ) = finrank k (LinearMap.range ψ) := by
    rw [hrange, LinearMap.finrank_range_dualMap_eq_finrank_range]
  have h4 : finrank k (LinearMap.ker ψ) = finrank k (LinearMap.ker β.flip) := by
    have : LinearMap.ker ψ = (LinearMap.ker β.flip).comap S.subtype := by
      rw [hψ, LinearMap.ker_comp]
    rw [this]
    exact (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  omega

theorem finrank_add_le (β : M →ₗ[k] M' →ₗ[k] k) (Ag Af : Submodule k M) (Ae Af' : Submodule k M')
    (hN : ∀ b : M', (∀ a : M, β a b = 0) → b ∈ Ae ⊓ Af')
    (hg : ∀ a ∈ Ag, ∀ b ∈ Ae, β a b = 0)
    (hf : ∀ a : M, a ∈ Af ↔ ∀ b ∈ Af', β a b = 0) :
    finrank k Ag + finrank k Ae ≤ finrank k Af + finrank k Af' := by
  have hker : ∀ b : M', b ∈ LinearMap.ker β.flip → b ∈ Ae ⊓ Af' := by
    intro b hb
    apply hN b
    intro a
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hb) a
    simpa using this
  have hNe : LinearMap.ker β.flip ≤ Ae := fun b hb => (hker b hb).1
  have hNf : LinearMap.ker β.flip ≤ Af' := fun b hb => (hker b hb).2
  have he := finrank_annihilator_add β Ae hNe
  have hf' := finrank_annihilator_add β Af' hNf
  have hgle : Ag ≤ LinearMap.ker (Ae.subtype.dualMap ∘ₗ β) := by
    intro a ha
    rw [LinearMap.mem_ker]
    ext ⟨b, hb⟩
    simpa using hg a ha b hb
  have hfeq : Af = LinearMap.ker (Af'.subtype.dualMap ∘ₗ β) := by
    ext a
    rw [hf a, LinearMap.mem_ker]
    constructor
    · intro h
      ext ⟨b, hb⟩
      simpa using h b hb
    · intro h b hb
      have := LinearMap.congr_fun h ⟨b, hb⟩
      simpa using this
  have hAg := Submodule.finrank_mono hgle
  rw [hfeq]
  omega

end GlobalTheory.HyodoDef.PairLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddF
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoDef.Count

theorem finrank_blochKato_g_add_e_le_f_add_f_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hc hc' hdR hdR' hdual
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hO := GlobalTheory.Published.BlochKato.goodO_padicInt (l := l)
  have hTD := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  have hEC := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V', ρ := ρ', cont := hc' }
  have hdual' : IsDual1 (P.PD K) ρ' ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  obtain ⟨hfin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A' A m.flip hdual'
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ) := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hfin
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ') := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A' hfin'
  obtain ⟨β, hβ, -, hr⟩ : ∃ β : ↥(continuousCocycles ρ) →ₗ[ℚ_[l]] ↥(continuousCocycles ρ') →ₗ[ℚ_[l]] ℚ_[l],
      (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL ρ' m a.1 b.1)) ∧
      (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 ρ' :=
    GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  have hann : ∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles (P.PD K) ρ ↔
      ∀ b ∈ finiteCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m a b)) :=
    (GlobalTheory.T.blochKato_exact_annihilators_periodDatum hTD hEC l P AI hT K ℚ_[l] ℤ_[l] hO A A' m hdR hdual).1
  have horth := GlobalTheory.T.de_rham_cocycle_dimension_compare l P AI hT K V ρ V' ρ' m hc hc' hdR' hdual
  have hg : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have he : crystallineCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hf : finiteCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have hf' : finiteCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hBf : B1 ρ' ≤ finiteCocycles (P.PD K) ρ' := GlobalTheory.BlochKatoAnn.B1_le_Z1f (P.PD K) A'
  have hBe : B1 ρ' ≤ crystallineCocycles (P.PD K) ρ' := by
    intro c hcB
    refine ⟨hf' (hBf hcB), ?_⟩
    obtain ⟨x, rfl⟩ := hcB
    refine ⟨x ⊗ₜ[ℚ_[l]] 1, ?_, fun g => ?_⟩
    · simp [φVB]
    · simp [cob, actVB, sub_tmul]
  have key := GlobalTheory.HyodoDef.PairLin.finrank_add_le β
    ((geometricCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((finiteCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype)
    ((crystallineCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype) ((finiteCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype)
    (fun b hb => ⟨hBe ((hr b).1 hb), hBf ((hr b).1 hb)⟩)
    (fun a ha b hb => (hβ a b).2 (horth a.1 ha b.1 hb))
    (fun a => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, hann a.1 a.2]
      constructor
      · intro h b hb
        exact (hβ a b).2 (h b.1 hb)
      · intro h b hb
        exact (hβ a ⟨b, hf' hb⟩).1 (h ⟨b, hf' hb⟩ hb))
  rwa [(Submodule.comapSubtypeEquivOfLe hg).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe he).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf').finrank_eq] at key

end GlobalTheory.HyodoDef.Count
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddFStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_blochKato_g_add_e_le_f_add_f : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  first | exact @GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | exact GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | (intros; apply GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalContinuousCocyclesGaloisRep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalContinuousCocyclesGaloisRep
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoFin

theorem finite_continuous_cocycles_localGaloisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  obtain ⟨ρ', m, hc', hD⟩ := GlobalTheory.T.exists_tateTwistDual_perfectPairing l P K V ρ hc
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] :=
    { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hc' }
  have hH := (GlobalTheory.T.finrank_H1_dual_pair CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler l P K ℚ_[l] ℤ_[l]
    GlobalTheory.Published.BlochKato.goodO_padicInt A A' m hD).1
  exact GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hH

end GlobalTheory.HyodoFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalContinuousCocyclesGaloisRepStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_continuousCocycles_galoisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  first | exact @GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep | exact GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep | (intros; apply GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisFiniteOfIsDR
noncomputable section

namespace GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  have h : Function.Injective
      (LinearMap.lTensor V (PD.ι.toLinearMap.restrictScalars Qp)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ PD.ι_inj
  exact h

theorem ιV_actVB (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_Dcris_le (ρ : Representation LL G V) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) ≤ DdR PD ρ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe] at hx
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hx ⊢
  intro g
  rw [← ιV_actVB, hx g]

theorem DdR_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(DdR PD ρ) := by
  by_cases hV : finrank LL V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
    have h0 : ∀ x : V ⊗[Qp] BdR, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
      | add a c ha hc => rw [ha, hc, add_zero]
    haveI : Subsingleton ↥(DdR PD ρ) :=
      ⟨fun x y => Subtype.ext ((h0 x).trans (h0 y).symm)⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

theorem Dcris_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := DdR_finite PD ρ h
  haveI : FiniteDimensional LL ↥((Dcris PD ρ).map (ιV PD (LL := LL) (V := V))) :=
    Submodule.finiteDimensional_of_le (map_Dcris_le PD ρ)
  exact Module.Finite.equiv
    (Submodule.equivMapOfInjective _ (ιV_injective PD) (Dcris PD ρ)).symm

end Generic

end GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.DcrisFin.dcris_finite_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsDR (P.PD K) ρ → Module.Finite ℚ_[l] ↥(Dcris (P.PD K) ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI := (P.PD K).finK
  exact GlobalTheory.DcrisFin.Dcris_finite (P.PD K) ρ h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocycles
noncomputable section

namespace GlobalTheory.HyodoFE

open Formalism Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HyodoDef TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem φVB_mem_Dcris {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [mem_Dcris_iff] at hx ⊢
  intro g
  rw [← GlobalTheory.CobCrisLift.φVB_act, hx g]

def oneSubφ : Dcris PD ρ →ₗ[LL] Dcris PD ρ :=
  (LinearMap.id - φVB PD (LL := LL) (V := V)).restrict (p := Dcris PD ρ) (q := Dcris PD ρ)
    (fun x hx => (Dcris PD ρ).sub_mem hx (φVB_mem_Dcris PD ρ hx))

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def pairs : Submodule LL ((G → V) × (V ⊗[Qp] B)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def projZ : pairs PD ρ →ₗ[LL] finiteCocycles PD ρ :=
  LinearMap.codRestrict (finiteCocycles PD ρ) ((LinearMap.fst LL (G → V) (V ⊗[Qp] B)).comp (pairs PD ρ).subtype)
    (fun p => ⟨p.2.1, p.1.2, p.2.2⟩)

theorem projZ_surjective : Function.Surjective (projZ PD ρ) := by
  rintro ⟨c, hc, x, hx⟩
  exact ⟨⟨(c, x), hc, hx⟩, rfl⟩

def toDcris : pairs PD ρ →ₗ[LL] Dcris PD ρ :=
  LinearMap.codRestrict (Dcris PD ρ)
    (((LinearMap.id - φVB PD (LL := LL) (V := V)).comp (LinearMap.snd LL (G → V) (V ⊗[Qp] B))).comp
      (pairs PD ρ).subtype)
    (fun p => GlobalTheory.CobCrisLift.sub_φ_mem_Dcris PD ρ p.1.1 p.1.2 p.2.2)

theorem fst_mem_exponential_cocycles (p : pairs PD ρ) (hp : toDcris PD ρ p ∈ LinearMap.range (oneSubφ PD ρ)) :
    (p : (G → V) × (V ⊗[Qp] B)).1 ∈ crystallineCocycles PD ρ := by
  obtain ⟨e, he⟩ := hp
  have he' : (e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e
      = p.1.2 - φVB PD (LL := LL) (V := V) p.1.2 := congrArg Subtype.val he
  refine ⟨p.2.1, p.1.2 - e, ?_, fun g => ?_⟩
  · rw [map_sub]
    calc φVB PD (LL := LL) (V := V) p.1.2 - φVB PD (LL := LL) (V := V) e
        = (p.1.2 - (e : V ⊗[Qp] B)) + (((e : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) e)
          - (p.1.2 - φVB PD (LL := LL) (V := V) p.1.2)) := by abel
      _ = p.1.2 - e := by rw [he', sub_self, add_zero]
  · have hg := (mem_Dcris_iff PD ρ e).1 e.2 g
    rw [p.2.2 g, map_sub, hg]
    abel

theorem finrank_finite_cocycles_le [Module.Finite LL (Dcris PD ρ)] :
    finrank LL (finiteCocycles PD ρ) ≤ finrank LL (crystallineCocycles PD ρ) +
      finrank LL ↥(Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id)) := by
  by_cases hf : Module.Finite LL (finiteCocycles PD ρ)
  swap
  · rw [Module.finrank_of_not_finite hf]; exact Nat.zero_le _
  obtain ⟨s, hs⟩ := (projZ PD ρ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (projZ_surjective PD ρ))
  set N := LinearMap.range (oneSubφ PD ρ) with hN
  let T : finiteCocycles PD ρ →ₗ[LL] (Dcris PD ρ ⧸ N) := N.mkQ ∘ₗ toDcris PD ρ ∘ₗ s
  have hle : crystallineCocycles PD ρ ≤ finiteCocycles PD ρ := fun c ⟨hc, x, _, hx⟩ => ⟨hc, x, hx⟩
  haveI : Module.Finite LL (crystallineCocycles PD ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hmem : ∀ k : LinearMap.ker T, ((k : finiteCocycles PD ρ) : G → V) ∈ crystallineCocycles PD ρ := by
    intro k
    have hk : T k = 0 := LinearMap.mem_ker.1 k.2
    have h := fst_mem_exponential_cocycles PD ρ (s k) ((Submodule.Quotient.mk_eq_zero N).1 hk)
    have hsk : projZ PD ρ (s k) = k := LinearMap.congr_fun hs k
    have hv : ((s k : pairs PD ρ) : (G → V) × (V ⊗[Qp] B)).1 = ((k : finiteCocycles PD ρ) : G → V) :=
      congrArg Subtype.val hsk
    rwa [hv] at h
  have h1 : finrank LL (LinearMap.ker T) ≤ finrank LL (crystallineCocycles PD ρ) := by
    let j : LinearMap.ker T →ₗ[LL] crystallineCocycles PD ρ :=
      LinearMap.codRestrict (crystallineCocycles PD ρ) ((finiteCocycles PD ρ).subtype ∘ₗ (LinearMap.ker T).subtype) hmem
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h2 : finrank LL (LinearMap.range T) ≤ finrank LL (Dcris PD ρ ⧸ N) := Submodule.finrank_le _
  have h3 := Submodule.finrank_quotient_add_finrank N
  have h4 := LinearMap.finrank_range_add_finrank_ker (oneSubφ PD ρ)
  have h5 := LinearMap.finrank_range_add_finrank_ker T
  set W := Dcris PD ρ ⊓ LinearMap.ker (φVB PD (LL := LL) (V := V) - LinearMap.id) with hW
  haveI : Module.Finite LL W :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : W ≤ Dcris PD ρ))
      (Submodule.inclusion_injective _)
  have hmemW : ∀ k : LinearMap.ker (oneSubφ PD ρ), ((k : Dcris PD ρ) : V ⊗[Qp] B) ∈ W := by
    intro k
    have hk : oneSubφ PD ρ k = 0 := LinearMap.mem_ker.1 k.2
    have hk' : ((k : Dcris PD ρ) : V ⊗[Qp] B) - φVB PD (LL := LL) (V := V) (k : Dcris PD ρ) = 0 :=
      congrArg Subtype.val hk
    refine Submodule.mem_inf.2 ⟨(k : Dcris PD ρ).2, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    rw [sub_eq_zero] at hk' ⊢
    exact hk'.symm
  have h6 : finrank LL (LinearMap.ker (oneSubφ PD ρ)) ≤ finrank LL W := by
    let j : LinearMap.ker (oneSubφ PD ρ) →ₗ[LL] W :=
      LinearMap.codRestrict W ((Dcris PD ρ).subtype ∘ₗ (LinearMap.ker (oneSubφ PD ρ)).subtype) hmemW
    have hj : Function.Injective j := by
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
      exact Subtype.ext (Subtype.ext h)
    exact LinearMap.finrank_le_finrank_of_injective hj
  have h7 : finrank LL N = finrank LL (LinearMap.range (oneSubφ PD ρ)) := rfl
  omega

end Generic

end GlobalTheory.HyodoFE

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.HyodoFE.finrank_finite_le_exponential_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  intro l _ P AI _ K V _ _ _ _ _ _ _ ρ _ hdR
  haveI := GlobalTheory.DcrisFin.dcris_finite_of_isDR l P K V ρ hdR
  exact GlobalTheory.HyodoFE.finrank_finite_cocycles_le (P.PD K) ρ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocyclesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_finite_le_exponential_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  first | exact @GlobalTheory.HyodoFE.finrank_finite_le_exponential_add | exact GlobalTheory.HyodoFE.finrank_finite_le_exponential_add | (intros; apply GlobalTheory.HyodoFE.finrank_finite_le_exponential_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatement
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.HyodoDef TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo : Hyodo := by
  intro l _ P AI T K V _ _ _ _ _ ρ hcont hsst c hc hcoc hdR
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  obtain ⟨ρ', m, hρ'c, hdual⟩ := GlobalTheory.T.exists_tateTwistDual_perfectPairing l P K V ρ hcont
  have hdrV : IsDR (P.PD K) ρ := GlobalTheory.T.isDeRham_of_isSemistable l P AI T K V ρ hsst
  have hdrV' : IsDR (P.PD K) ρ' := by
    letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
    haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact (GlobalTheory.T.de_rham_filtration_duality l P AI T K).1 ℚ_[l] ℤ_[l] GlobalTheory.Published.BlochKato.goodO_padicInt
      { V := V, ρ := ρ, cont := hcont } { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hρ'c } m hdrV hdual
  have hfin : Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := GlobalTheory.T.finiteDimensional_continuousCocycles_galoisRep l P K V ρ hcont
  obtain ⟨S, _hfS, hSc, hSst, hSdR, hS⟩ := GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous l P AI T K V _ ρ ρ' m hcont hdual hsst hfin
  have hgc : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  haveI : Module.Finite ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hgc) (Submodule.inclusion_injective hgc)
  have hSg : S ≤ geometricCocycles (P.PD K) ρ := fun c hc => ⟨hSc hc, hSdR c hc⟩
  have h1 := GlobalTheory.T.finrank_blochKato_g_add_e_le_f_add_f l P AI T K V ρ _ ρ' m hcont hρ'c hdrV hdrV' hdual
  have h2 := GlobalTheory.T.finrank_finite_le_exponential_cocycles l P AI T K _ ρ' hρ'c hdrV'
  have hEq : S = geometricCocycles (P.PD K) ρ := Submodule.eq_of_le_of_finrank_le hSg (by omega)
  have hcg : c ∈ geometricCocycles (P.PD K) ρ := ⟨⟨hc, hcoc⟩, hdR⟩
  rw [← hEq] at hcg
  exact hSst c hcg

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatementStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyodo_statement : Hyodo := by
  first | exact @GlobalTheory.PMon.hyodo | exact GlobalTheory.PMon.hyodo | (intros; apply GlobalTheory.PMon.hyodo <;> assumption)
end
