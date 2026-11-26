module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenIntertwinerModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittUnfoldedIntegralLeCoreQuotientHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexLevelSelfDualStabilizerEqProdLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeTermGeneratorConstantViaFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThK.PureTensIndep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Filter GlobalTheory.ThK.ModelPol

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem sum_local_eq_zero (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, vac v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) {m : ℕ} (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ i, ∀ v ∉ T, φ i v = vac v) (hs : ∑ i, pure (f i) (φ i) = 0)
    (x : κ → mixedEmbedding.mixedSpace F) (z : ∀ v : T, κ → Fv F v) :
    ∑ i, f i x * ∏ v : T, φ i v (z v) = 0 := by
  classical
  have key : ∀ v : Pl F, ∃ p : κ → Fv F v, vac v p ≠ 0 ∧
      (vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        ∀ i, p i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨p, hp⟩ := Function.ne_iff.1 (h0 v)
    refine ⟨p, hp, fun h => ?_⟩
    rw [h] at hp
    exact Set.mem_of_indicator_ne_zero hp
  choose p hp hp' using key
  let w : ∀ v : Pl F, κ → Fv F v := fun v => if h : v ∈ T then z ⟨v, h⟩ else p v
  have hw : ∀ i, ∀ᶠ v in cofinite, w v i ∈ v.adicCompletionIntegers F := by
    intro i
    filter_upwards [hstd, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    have hvT' : v ∉ T := hvT
    simp only [w, dif_neg hvT']
    exact hp' v hv i
  let y : κ → Af F := fun i => ⟨fun v => w v i, hw i⟩
  have hy : ∀ v, (fun i => evalV F v (y i)) = w v := fun _ => rfl
  have hS : {v | vac v ≠ Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite :=
    Filter.eventually_cofinite.1 hstd
  have hCfin : (Function.mulSupport fun v => if v ∈ T then (1 : ℂ) else vac v (p v)).Finite := by
    refine hS.subset fun v hv => ?_
    by_cases hvT : v ∈ T
    · simp [hvT] at hv
    · intro he
      apply hv
      simp only [if_neg hvT]
      rw [he, Set.indicator_of_mem (show p v ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from hp' v he)]
      rfl
  have hC : (∏ᶠ v, if v ∈ T then (1 : ℂ) else vac v (p v)) ≠ 0 :=
    finprod_induction (fun c : ℂ => c ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => by
      by_cases hvT : v ∈ T
      · simp [hvT]
      · simp only [if_neg hvT]; exact hp v
  have hval : ∀ i, finPr (φ i) y = (∏ v : T, φ i v (z v)) * ∏ᶠ v, if v ∈ T then (1 : ℂ) else vac v (p v) := by
    intro i
    have e1 : (fun v => φ i v fun j => evalV F v (y j)) =
        fun v => (if v ∈ T then φ i v (w v) else 1) * (if v ∈ T then (1 : ℂ) else vac v (p v)) := by
      funext v
      rw [hy v]
      by_cases hvT : v ∈ T
      · simp [hvT]
      · simp [hvT, hφ i v hvT, w]
    have hAfin : (Function.mulSupport fun v => if v ∈ T then φ i v (w v) else 1).Finite := by
      refine T.finite_toSet.subset fun v hv => ?_
      by_contra h
      exact hv (if_neg h)
    show (∏ᶠ v, φ i v fun j => evalV F v (y j)) = _
    rw [e1, finprod_mul_distrib hAfin hCfin]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ (fun v hv => by
      by_contra h
      exact hv (if_neg h))]
    rw [← Finset.prod_coe_sort T]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [v.2, w]
  have h1 := congrFun hs (pt x y)
  simp only [Finset.sum_apply, Pi.zero_apply, pure_eq, pureA_pt, hval] at h1
  have h2 : (∑ i, f i x * ∏ v : T, φ i v (z v)) * ∏ᶠ v, (if v ∈ T then (1 : ℂ) else vac v (p v)) = 0 := by
    rw [Finset.sum_mul]
    simpa [mul_assoc] using h1
  exact (mul_eq_zero.1 h2).resolve_right hC

section Forms


variable (F κ) in
def coeL : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun f := f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

variable (F κ) in
theorem coeL_injective : Function.Injective (coeL F κ) := fun _ _ h => SchwartzMap.ext (congrFun h)


variable (F κ) in
def Xf (T : Finset (Pl F)) : Option T → Type
  | none => κ → mixedEmbedding.mixedSpace F
  | some v => κ → Fv F v


variable (F κ) in
def Vf (T : Finset (Pl F)) : ∀ l : Option T, Submodule ℂ (Xf F κ T l → ℂ)
  | none => LinearMap.range (coeL F κ)
  | some _ => ⊤

def famOf (T : Finset (Pl F)) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : ∀ l, Vf F κ T l
  | none => ⟨coeL F κ f, LinearMap.mem_range_self _ _⟩
  | some v => ⟨φ v, Submodule.mem_top⟩

def back (T : Finset (Pl F)) : Vf F κ T none ≃ₗ[ℂ] SInf F κ :=
  (LinearEquiv.ofInjective _ (coeL_injective F κ)).symm

theorem back_famOf (T : Finset (Pl F)) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    back T (famOf T f φ none) = f :=
  (LinearEquiv.symm_apply_eq _).2 (Subtype.ext rfl)

theorem q_add {T : Finset (Pl F)} {v : T} {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (q : ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q) (a b : Vf F κ T (some v)) :
    q ((a + b : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ) =
      q (a : Xf F κ T (some v) → ℂ) + q (b : Xf F κ T (some v) → ℂ) :=
  q.map_add (a : Xf F κ T (some v) → ℂ) (b : Xf F κ T (some v) → ℂ)

theorem q_smul {T : Finset (Pl F)} {v : T} {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (q : ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q) (c : ℂ) (b : Vf F κ T (some v)) :
    q ((c • b : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ) = c • q (b : Xf F κ T (some v) → ℂ) :=
  q.map_smul c (b : Xf F κ T (some v) → ℂ)

theorem upd_some {T : Finset (Pl F)} [DecidableEq (Option T)] {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)]
    [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) (w : ∀ l, Vf F κ T l) (v₀ : T)
    (c : Vf F κ T (some v₀)) :
    (fun v : T => q v ((Function.update w (some v₀) c (some v) : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ)) =
      Function.update (fun v : T => q v (w (some v) : Xf F κ T (some v) → ℂ))
        v₀ (q v₀ (c : Xf F κ T (some v₀) → ℂ)) := by
  funext v
  by_cases h : v = v₀
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne (fun e => h (Option.some_injective _ e))]

theorem upd_none {T : Finset (Pl F)} [DecidableEq (Option T)] {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)]
    [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) (w : ∀ l, Vf F κ T l) (c : Vf F κ T none) :
    (fun v : T => q v ((Function.update w none c (some v) : Vf F κ T (some v)) : Xf F κ T (some v) → ℂ)) =
      fun v : T => q v (w (some v) : Xf F κ T (some v) → ℂ) := by
  funext v
  rw [Function.update_of_ne (Option.some_ne_none v)]

def formOf {T : Finset (Pl F)} {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F κ →ₗ[ℂ] P) {Q : Pl F → Type}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (ℓ : Module.Dual ℂ (P ⊗[ℂ] PiTensorProduct ℂ fun v : T => Q v)) :
    (∀ l, Vf F κ T l) →ₘₗ[ℂ] ℂ where
  toFun w := ℓ (p (back T (w none)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (w (some v) : Xf F κ T (some v) → ℂ))
  map_update_add' := by
    intro _ w l a b
    cases l with
    | none =>
      simp only [upd_none, Function.update_self, map_add (f := _), TensorProduct.add_tmul]
    | some v₀ =>
      simp only [upd_some, Function.update_of_ne (Option.some_ne_none v₀).symm, q_add,
        MultilinearMap.map_update_add, TensorProduct.tmul_add, map_add]
  map_update_smul' := by
    intro _ w l a b
    cases l with
    | none =>
      simp only [RingHom.id_apply, upd_none, Function.update_self, map_smul]
      rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul]
    | some v₀ =>
      simp only [upd_some, Function.update_of_ne (Option.some_ne_none v₀).symm, q_smul,
        MultilinearMap.map_update_smul, RingHom.id_apply, TensorProduct.tmul_smul, map_smul, smul_eq_mul]

theorem formOf_famOf {T : Finset (Pl F)} {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F κ →ₗ[ℂ] P)
    {Q : Pl F → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (ℓ : Module.Dual ℂ (P ⊗[ℂ] PiTensorProduct ℂ fun v : T => Q v)) (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    formOf p q ℓ (famOf T f φ) = ℓ (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => q v (φ v)) := by
  show ℓ (p (back T (famOf T f φ none)) ⊗ₜ[ℂ] _) = _
  rw [back_famOf]
  rfl

end Forms

theorem tmul_sum_eq_zero_of_pure : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ v, vac v ≠ 0) → (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] (p : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] P) (Q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type)
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ i, ∀ v ∉ T, φ i v = vac v) → ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = 0 →
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) = 0 := by
  intro F _ _ κ _ vac h0 hstd P _ _ p Q _ _ q T m f φ hφ hs
  have hloc := sum_local_eq_zero vac h0 hstd T f φ hφ hs
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  have key := GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq (Vf F κ T) (formOf p q ℓ) (Finsupp.equivFunOnFinite.symm fun _ : Fin m => (1 : ℂ))
    (fun i => famOf T (f i) (φ i)) (fun _ => 0) (fun z => by
      rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
      simp only [Finsupp.coe_equivFunOnFinite_symm, one_mul, Fintype.prod_option]
      have h1 := hloc (z none) fun v => z (some v)
      simp only [Pi.zero_apply, ZeroMemClass.coe_zero, zero_mul, Finset.sum_const_zero]
      exact h1)
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at key
  simp only [Finsupp.coe_equivFunOnFinite_symm, one_mul, MultilinearMap.map_zero, Finset.sum_const_zero,
    formOf_famOf] at key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact key

end GlobalTheory.ThK.PureTensIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZeroStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ v, vac v ≠ 0) → (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ {P : Type} [AddCommGroup P] [Module ℂ P] (p : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] P) (Q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type)
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (q : ∀ v, ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] Q v)
    (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
    (∀ i, ∀ v ∉ T, φ i v = vac v) → ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) = 0 →
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) = 0 := by
  first | exact @GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | exact GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure | (intros; apply GlobalTheory.ThK.PureTensIndep.tmul_sum_eq_zero_of_pure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittUnfoldedIntegralLeCoreQuotientHeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * quotHeight V₀ g ^ A) := by
  first | exact @GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight | exact GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight | (intros; apply GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamily
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]


set_option maxHeartbeats 400000 in
theorem tot_continuous (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) : Continuous (a.tot G Φ) := by
  obtain ⟨vT⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.1 0 V₀.rank
  have hmix := (GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W ρ 0 a.d (hypZero W) a.vS vT a.χV a.χW a.om
    ha.weil Φ hΦ).1
  have hpos : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      (⟨a.d.nB p.2.2 * a.d.levi p.2.1.1, mul_mem (a.d.nB_mem_NFlag _) (a.d.levi_mem_NFlag p.2.1.2)⟩ : flagN a.d) :=
    ((a.d.continuous_nB.comp continuous_snd.snd).mul
      ((a.d.continuous_levi.comp continuous_subtype_val).comp continuous_snd.fst)).subtype_mk _
  have hTh : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.Th p.1.2 (a.d.nB p.2.2 * a.d.levi p.2.1.1) :=
    ha.cont.comp (continuous_fst.snd.prodMk hpos)
  have hM : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1)
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2) := by
    have h1 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => a.d.emb0 (a.g p.1.2) :=
      a.d.continuous_embed.comp (ha.g.comp continuous_fst.snd)
    have h2 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1 : Mx D W.rank ρ) :=
      continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd.fst))
    have h3 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2 : WO V₀ W) :=
      continuous_const.matrix_mul continuous_snd.snd
    have hq : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        (((a.d.emb0 (a.g p.1.2), p.1.1), ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1, (rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) :=
      (h1.prodMk continuous_fst.fst).prodMk (h2.prodMk h3)
    have hc := hmix.comp hq
    exact hc
  have hfin := (hG.2.1.comp continuous_fst.fst).mul (hTh.mul hM)
  exact hfin

theorem inner_unfold (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) (y : Y) :
    IntegrableOn (fun h => G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ)) 𝓑
      a.vW.μ ∧
    ∫ n in a.vN.𝓝, a.Th y n.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (n.1 * a.d.emb0 (a.g y)) ∂a.vN.ν =
      ∫ h in 𝓑, G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ := by
  have hD : Descent D := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om', hom'⟩ := (hD ψ V W a.χV a.χW a.om ha.weil).1 V₀ ρ a.d
  have hΦ' := ha.weil.om_pres (a.d.emb0 (a.g y), 1) Φ hΦ
  obtain ⟨h1, h2⟩ := GlobalTheory.Unf.unfold_over_N_lift D hD ψ V V₀ W ρ a.d a.χV a.χW a.om om' ha.weil hom' a.vS a.vN a.vb
    a.vU a.vW a.x₀ (a.Th y) ha.base (ha.th y) G (a.om (a.d.emb0 (a.g y), 1) Φ) hG hΦ' 𝓑 h𝓑
  have hsplit : ∀ h, a.om (1, h) (a.om (a.d.emb0 (a.g y), 1) Φ) = a.om (a.d.emb0 (a.g y), h) Φ := by
    intro h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hlift : ∀ n, liftS a.om a.vW.μ a.vW.𝓕 G (a.om (a.d.emb0 (a.g y), 1) Φ) n =
      liftS a.om a.vW.μ a.vW.𝓕 G Φ (n * a.d.emb0 (a.g y)) := by
    intro n
    have ht := (GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D ψ V W a.χV a.χW a.om ha.weil a.vW G Φ hG hΦ).2.2.2.2
      (a.d.emb0 (a.g y)) 1
    have hr : rTrans (1 : GA D W) G = G := by funext x; simp [rTrans]
    rw [hr] at ht
    rw [ht]; rfl
  simp only [hsplit, hlift] at h1 h2
  exact ⟨h1, h2⟩

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]


set_option maxHeartbeats 1000000 in
theorem tot_integrable [SecondCountableTopology Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y) (ha : a.Is)
    (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G) (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) :
    Integrable (a.tot G Φ) (a.totMeas 𝓑) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, i3, -⟩ := lattice_Mx D ρ V₀.rank
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  obtain ⟨C, A, hCA⟩ := GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight D ψ V V₀ W ρ a.d a.χV a.χW a.om ha.weil a.vS a.vb a.vU a.vW a.x₀ ha.base G Φ
    hG hΦ 𝓑 h𝓑
  obtain ⟨M, -, hMb, hMi⟩ := ha.small
  have hM0 : ∀ y, 0 ≤ M y := fun y => (norm_nonneg _).trans (hMb y 1 (one_mem _))
  set Bd : GA D V₀ → GA D W → ENNReal := fun g h => ∫⁻ u, ∫⁻ b in a.vb.𝓕,
    ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 g, h) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
      ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂a.vb.μ ∂a.vU.ν with hBd
  set F : GA D W × Y → ENNReal := fun q => ENNReal.ofReal (M q.2) * (‖G q.1‖ₑ * Bd (a.g q.2) q.1) with hF
  haveI : SecondCountableTopology (GA D W × Y) := inferInstance
  haveI : OpensMeasurableSpace (GA D W × Y) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (UX D ρ) (Mx D ρ V₀.rank) := secondCountableTopologyEither_of_right _ _
  haveI : OpensMeasurableSpace (UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (GA D W × Y) (UX D ρ × Mx D ρ V₀.rank) :=
    secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace ((GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  have hmeas : Measurable (a.tot G Φ) := (tot_continuous a ha G Φ hG hΦ).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) < ⊤
  have hpt : ∀ q : GA D W × Y, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ≤ F q := by
    intro q
    have hc : ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
    calc ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))
        ≤ ∫⁻ u, ∫⁻ b, ‖a.tot G Φ (q, (u, b))‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := lintegral_prod_le _
      _ ≤ ∫⁻ u, ∫⁻ b, ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ *
            ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := by
          refine lintegral_mono fun u => lintegral_mono fun b => ?_
          have hmem : a.d.nB b * a.d.levi u.1 ∈ flagN a.d := mul_mem (a.d.nB_mem_NFlag b) (a.d.levi_mem_NFlag u.2)
          have hth : ‖a.Th q.2 (a.d.nB b * a.d.levi u.1)‖ₑ ≤ ENNReal.ofReal (M q.2) := by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hMb _ _ hmem)
          show ‖G q.1 * (a.Th q.2 (a.d.nB b * a.d.levi u.1) * a.d.mixS W ψ a.vS.μ a.vS.𝓕
            (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b))‖ₑ ≤ _
          rw [enorm_mul, enorm_mul, ← mul_assoc, mul_comm (‖G q.1‖ₑ), mul_assoc, mul_assoc]
          gcongr
      _ = ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ * Bd (a.g q.2) q.1 := by
          simp only [hBd]
          rw [← lintegral_const_mul' _ _ hc]
          refine lintegral_congr fun u => ?_
          rw [← lintegral_const_mul' _ _ hc]
      _ = F q := by simp only [hF, mul_assoc]
  calc ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)))
      ≤ ∫⁻ q, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ∂((a.vW.μ.restrict 𝓑).prod a.m) :=
        lintegral_prod_le _
    _ ≤ ∫⁻ q, F q ∂((a.vW.μ.restrict 𝓑).prod a.m) := lintegral_mono hpt
    _ = ∫⁻ z, F z.swap ∂(a.m.prod (a.vW.μ.restrict 𝓑)) := (lintegral_prod_swap F).symm
    _ ≤ ∫⁻ y, ∫⁻ h, F (h, y) ∂(a.vW.μ.restrict 𝓑) ∂a.m := lintegral_prod_le _
    _ = ∫⁻ y, ENNReal.ofReal (M y) * ∫⁻ h in 𝓑, ‖G h‖ₑ * Bd (a.g y) h ∂a.vW.μ ∂a.m := by
        simp only [hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y, ENNReal.ofReal (M y) * ENNReal.ofReal (C * quotHeight V₀ (a.g y) ^ A) ∂a.m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact hCA (a.g y)
    _ = ∫⁻ y, ENNReal.ofReal (C * (M y * quotHeight V₀ (a.g y) ^ A)) ∂a.m := by
        refine lintegral_congr fun y => ?_
        rw [← ENNReal.ofReal_mul (hM0 y)]
        ring_nf
    _ < ⊤ := ((hMi A).const_mul C).lintegral_lt_top

theorem fubini_tot (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (B₀ : Set (GA D W))
    (hI : Integrable (a.tot G Φ) (a.totMeas B₀)) :
    IntegrableOn (a.ker G Φ) B₀ a.vW.μ ∧ ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ h in B₀, a.ker G Φ h ∂a.vW.μ ∧
    ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ y, ∫ h in B₀,
      G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ ∂a.m := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI' : Integrable (a.tot G Φ) (((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) :=
    hI
  set K : GA D W × Y → ℂ := fun q =>
    G q.1 * fl ψ a.d W a.vS a.vb a.vU (a.Th q.2) (rat a.x₀) (a.om (a.d.emb0 (a.g q.2), q.1) Φ) with hK
  have hae : (fun q => ∫ r, a.tot G Φ (q, r) ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) =ᵐ[(a.vW.μ.restrict B₀).prod a.m]
      K := by
    filter_upwards [hI'.prod_right_ae] with q hq
    rw [integral_prod _ hq]
    simp only [Gen.tot, integral_const_mul, hK, fl]
  have hKi : Integrable K ((a.vW.μ.restrict B₀).prod a.m) := hI'.integral_prod_left.congr hae
  have hker : ∀ h, ∫ y, K (h, y) ∂a.m = a.ker G Φ h := by
    intro h
    simp only [hK, Gen.ker, integral_const_mul]
  have htot : ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ q, K q ∂((a.vW.μ.restrict B₀).prod a.m) := by
    show ∫ p, a.tot G Φ p ∂(((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) = _
    rw [integral_prod _ hI']
    exact integral_congr_ae hae
  refine ⟨?_, ?_, ?_⟩
  · have := hKi.integral_prod_left
    simp only [hker] at this
    exact this
  · rw [htot, integral_prod _ hKi]
    simp only [hker]
  · rw [htot, integral_prod_symm _ hKi]

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc


set_option maxHeartbeats 1000000 in
theorem unfold_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) := by
  intro D ψ V V₀ W ρ Y _ _ _ _ a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI := Gen.tot_integrable a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨hker, -, hE⟩ := Gen.fubini_tot a ha G Φ 𝓑 hI
  refine ⟨hI, hker, ?_, ?_⟩
  · rw [hE, Gen.lhs]
    exact integral_congr_ae (ae_of_all _ fun y => (Gen.inner_unfold a ha G Φ hG hΦ 𝓑 h𝓑 y).2)
  · intro S hS
    have hset : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        (S ×ˢ (Set.univ : Set Y)) ×ˢ (Set.univ : Set (UX D ρ × Mx D ρ V₀.rank)) := by
      ext p; simp
    have hres : (a.totMeas 𝓑).restrict {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        a.totMeas (𝓑 ∩ S) := by
      simp only [Gen.totMeas]
      rw [hset, ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ,
        Measure.restrict_restrict hS, Set.inter_comm]
    have hI' : Integrable (a.tot G Φ) (a.totMeas (𝓑 ∩ S)) := by
      rw [← hres]; exact hI.restrict
    rw [hres]
    exact ((Gen.fubini_tot a ha G Φ (𝓑 ∩ S) hI').2.1).symm

end GlobalTheory.Asc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamilyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_unfolding_integrated_over_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) := by
  first | exact @GlobalTheory.Asc.unfold_family | exact GlobalTheory.Asc.unfold_family | (intros; apply GlobalTheory.Asc.unfold_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardGLDivParabolicIndexFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardGLDivParabolicIndexFiniteField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.Twist.GLIndexLoc

theorem card_GL_real_eq (κ : Type) [Field κ] [Finite κ] (n : ℕ) :
    (Nat.card (GL (Fin n) κ) : ℝ) =
      (Nat.card κ : ℝ) ^ (n ^ 2) * ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  haveI := Fintype.ofFinite κ
  have hq1 : 1 ≤ Nat.card κ := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  rw [Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [hIoc, Finset.prod_map, sq, pow_mul,
    show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n := Nat.pow_le_pow_right hq1 (by omega)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
  congr 1
  have hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]

theorem index_loc : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ), n = r + t → (Nat.card (GL (Fin n) κ) : ℝ) / ((Nat.card (GL (Fin t) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * t)) * ((Nat.card κ : ℝ) ^ (r ^ 2 + r * t))⁻¹ = ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  intro κ _ _ n r t hn
  haveI := Fintype.ofFinite κ
  have hq2 : (2 : ℝ) ≤ Nat.card κ := by
    have := Fintype.one_lt_card (α := κ)
    rw [← Nat.card_eq_fintype_card] at this
    exact_mod_cast this
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  have hP : ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi1 : 1 ≤ i := (Finset.mem_Ioc.mp hi).1
    have : (2 : ℝ) ≤ (Nat.card κ : ℝ) ^ i :=
      le_trans hq2 (le_self_pow₀ (by linarith) (by omega))
    have : ((Nat.card κ : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  rw [card_GL_real_eq, card_GL_real_eq,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (show t ≤ n by omega)]
  have hpow : (Nat.card κ : ℝ) ^ (n ^ 2) =
      (Nat.card κ : ℝ) ^ (t ^ 2) * (Nat.card κ : ℝ) ^ (r * t) * (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) := by
    rw [← pow_add, ← pow_add]; congr 1; subst hn; ring
  rw [hpow]
  generalize ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = P at hP ⊢
  generalize ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = Q
  have h1 : (Nat.card κ : ℝ) ^ (t ^ 2) ≠ 0 := pow_ne_zero _ hq0
  have h2 : (Nat.card κ : ℝ) ^ (r * t) ≠ 0 := pow_ne_zero _ hq0
  have h3 : (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) ≠ 0 := pow_ne_zero _ hq0
  field_simp

end GlobalTheory.Twist.GLIndexLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardGLDivParabolicIndexFiniteFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_div_parabolic_index_finiteField : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ), n = r + t → (Nat.card (GL (Fin n) κ) : ℝ) / ((Nat.card (GL (Fin t) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * t)) * ((Nat.card κ : ℝ) ^ (r ^ 2 + r * t))⁻¹ = ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  first | exact @GlobalTheory.Twist.GLIndexLoc.index_loc | exact GlobalTheory.Twist.GLIndexLoc.index_loc | (intros; apply GlobalTheory.Twist.GLIndexLoc.index_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormula
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.LevelIndex

theorem levelIndexNormC : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → LevelIndexNormC R F := by
  intro hLoc D G _ _ Pl0 T A Ks _ _ _ R F hPM
  intro i t σ s P cμ cη m ω BW f₀ f c io hd
  classical
  have hC : Hk3.Core R F := hd.1
  obtain ⟨Hl, cl, hP⟩ := hd.2.2.2.1
  refine ⟨?_, fun μ 𝓧 hμ => ?_⟩
  · obtain ⟨c0, hc0⟩ := hC.lev.βV i
    rw [one_pow] at hc0
    exact GlobalTheory.T.level_le_stabilizer_selfDual_lattice_frame D (Vc D i) _ _ _ hc0
  · have hn := GlobalTheory.T.levelVector_squareNorm_eq_prod_localVolumes hLoc R F hPM i t σ s P cμ cη m ω BW f₀ f c io hd Hl cl hP μ 𝓧 hμ
    rw [GlobalTheory.T.relIndex_level_selfDual_stabilizer_eq_prod_local R F i t P m Hl cl hC hP, hn]
    obtain ⟨hdis, hinj, hsp⟩ := GlobalTheory.T.levelAndTwistPlaces_split_distinct R F hC t
    have hrank : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have hrt : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have key : ∀ PP ∈ R.Pg ∪ R.Q t, (dLoc D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))⁻¹ =
        (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) *
          (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
      intro PP hPP
      obtain ⟨h2, hq⟩ := hsp PP hPP
      haveI : Fact PP.asIdeal.IsMaximal := ⟨PP.isMaximal⟩
      letI : Field (kP PP) := Ideal.Quotient.field _
      rw [GlobalTheory.T.card_GL_div_parabolic_index_finiteField (kP PP) _ D.R.r D.R.t hrt, hrank]
      unfold dLoc quadTerm quadSign
      rw [if_pos h2, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_inv, hq]
      simp
    have hcard : ∀ PP : Pl D.host.E, ∀ n : ℕ, (Nat.card (GL (Fin n) (kP PP)) : ℝ) ≠ 0 := fun PP n => by
      have : Finite (GL (Fin n) (kP PP)) := inferInstance
      exact_mod_cast (Nat.card_pos (α := GL (Fin n) (kP PP))).ne'
    have hHl : ∀ PP, (Nat.card (Hl PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := Hl PP)).ne'
    have hq0 : ∀ PP : Pl D.host.E, (Nat.card (kP PP) : ℝ) ≠ 0 := fun PP => by
      exact_mod_cast (Nat.card_pos (α := kP PP)).ne'
    unfold finS
    rw [Finset.prod_image hinj, Finset.prod_union hdis, ← Finset.prod_attach R.Pg, mul_mul_mul_comm,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun PP _ => ?_
      rw [key PP.1 (Finset.mem_union_left _ PP.2)]
      field_simp [hHl PP, hcard PP.1, hq0 PP.1]
    · refine Finset.prod_congr rfl fun PP hPP => ?_
      rw [key PP (Finset.mem_union_right _ hPP)]
      field_simp [hcard PP, hq0 PP]

end GlobalTheory.LevelIndex

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormulaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → LevelIndexNormC R F := by
  first | exact @GlobalTheory.LevelIndex.levelIndexNormC | exact GlobalTheory.LevelIndex.levelIndexNormC | (intros; apply GlobalTheory.LevelIndex.levelIndexNormC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadTie
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadingKernelsMatchCosetsThroughFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadingKernelsMatchCosetsThroughFrame
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeTerm

open NumberField in
theorem splitSup {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {P : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) :
    P.asIdeal ⊔ P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  by_contra hne
  have hsub : P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ P.asIdeal :=
    le_sup_right.trans (P.isMaximal.eq_of_le hne le_sup_left).ge
  apply h
  rw [Formalism.L2.Col.conjIdeal_asIdeal]
  refine (P.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_).symm
  rw [Formalism.L2.Col.mem_conjP]
  have : Formalism.L2.Col.cO D.host.E a = H.bar a := RingOfIntegers.ext (H.bar_eq a).symm
  rw [this]
  exact hsub (Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ha)

theorem phiW_unfold {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    castDict hV (T.phiJ j σ a f) g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
      (T.cE j σ (castDict hV (T.dict j σ) g).1 * castDict hV (T.mu j σ) g *
        rdU (T.U j σ) f (castDict hV (T.dict j σ) g).1 (castDict hV (T.dict j σ) g).2) := by
  subst hV
  rfl

theorem heckeTerm : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  intro D hP hS hVF G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeKernel_complex_point_matches_cosets D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  refine ⟨e, fun C => ⟨?_, fun z hz f hf => ?_⟩⟩
  · have hsp := splitSup T.Q.H hs.1.1
    have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p :=
      GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsp, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    have hT := hP.2.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hHP
    exact @hT (CAt σ) _ (inferInstanceAs (IsAlgClosed ℂ)) _ _ C
  · obtain ⟨hx', t, ht1, hB⟩ := he C z hz
    have hg := GlobalTheory.T.heckeTerm_generator_constant_via_frame D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
      _ (e C).2 C z hz hx' t ht1 hB
    have hw := GlobalTheory.FrameEval.evR_frBor _ _ _ _ _ _ (CAt σ) _ _ f hf t _ z hB
    have hwc : wchar (ex (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) (κ i).n) t = (t none : CAt σ) ^ (κ i).n := by
      unfold wchar
      rw [Finset.prod_eq_single none (fun j _ hj => by rw [ht1 j hj]; simp) (fun h0 => absurd (Finset.mem_univ _) h0)]
      rfl
    rw [hwc] at hw
    show _ = _ * castDict hV (T.phiJ ((i : ℕ) + 1) σ (wtA (κ i)) f) (h * (e C : GA D (Wc D i)))
    rw [phiW_unfold]
    have hr : rdU (T.U ((i : ℕ) + 1) σ) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1
        (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 =
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := dif_pos hx'
    rw [hr, hw]
    have hz' : toC ((t none : CAt σ) ^ (κ i).n * evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) =
        toC (t none : CAt σ) ^ (κ i).n * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := rfl
    rw [hz']
    linear_combination ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩))) * hg

end GlobalTheory.HeckeTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadingKernelsMatchCosetsThroughFrameStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  first | exact @GlobalTheory.HeckeTerm.heckeTerm | exact GlobalTheory.HeckeTerm.heckeTerm | (intros; apply GlobalTheory.HeckeTerm.heckeTerm <;> assumption)
end
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeReadProof

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem phiW_eq {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i))
    (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom) :
    phiW T i σ hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := by
  show T.phiJ _ σ a f _ = _
  rw [CoreJ.phiJ_apply]
  simp only [Core.phiAd, Pi.smul_apply, smul_eq_mul, adel, rdU, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [dictW, castDict] at hx ⊢
  split_ifs with h1
  · ring
  · exact absurd hx h1

theorem heckeReadTie (hSL : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D) (hVF : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D) :
    GlobalTheory.HeckeSupSt.HeckeReadTie := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthP ht i σ hσ hV hpin
  intro P p k α Rc hs cq f g hf hg hr h
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hgood : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  obtain ⟨hx, -, -⟩ := exists_witness T i σ hV ht.laws.toLawsM hgood h
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame D GlobalTheory.HeckePointLaw.heckePointLaws (hSL D) (hVF D) G Pl0 T0 A T R F κ v₀ hlev hgrp hfam
    hmod hthP ht i σ hσ hV hpin P p k α Rc hs h hx
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := Finite.of_equiv _ e.symm
  rw [phiW_eq T i σ hV _ g h hx]
  have hr' := hr (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)
  have e1 : toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c g
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) =
      σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * ∑ᶠ C,
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) := by
    refine (congrArg toC hr').trans ?_
    have hs1 : σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) = σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) := by
      simp only [hkScal, one_mul, map_mul]
    show σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) * toC (hkVal _ _ _ _ f _) = _
    rw [hs1]
    congr 1
    unfold hkVal
    show (∑ᶠ C, toC (hkTerm _ _ _ _ f _ C)) = _
    refine finsum_congr fun C => ?_
    unfold hkTerm
    split_ifs with h1
    · rfl
    · exact absurd (he C).1 h1
  rw [e1]
  have e2 : ∀ C, (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) =
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) :=
    fun C => (he C).2 _ (he C).1.choose_spec f hf
  have e3 : ∑ᶠ C, (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) =
      (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA (κ i)) f (h * a) := by
    rw [finsum_comp_equiv e (f := fun a : Rc =>
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (a : GA D (Wc D i))))]
    rw [finsum_eq_sum_of_fintype, Finset.sum_coe_sort Rc
      (fun a => (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * a)), Finset.mul_sum]
  rw [mul_assoc (σ cq) ((muAt T R i P)⁻¹ ^ k), ← e3, ← finsum_congr e2, ← mul_finsum]
  ring

end GlobalTheory.HeckeReadProof
end
end
