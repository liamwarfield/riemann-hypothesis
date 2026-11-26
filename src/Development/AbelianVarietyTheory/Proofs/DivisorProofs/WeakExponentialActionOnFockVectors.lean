module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ExpAct
open Matrix NumberField IsDedekindDomain
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem form_eq_sum {d : ℕ} (φ : (Fin d → ℂ) →ₗ[ℂ] ℂ) (y : Fin d → ℂ) :
    φ y = ∑ i, y i * φ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

def coordCLM {d : ℕ} (x : Fin d → ℂ) (i : Fin d) : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M *ᵥ x) i
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun r M => by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }

theorem coordCLM_apply {d : ℕ} (x : Fin d → ℂ) (i : Fin d) (M : Matrix (Fin d) (Fin d) ℂ) :
    coordCLM x i M = (M *ᵥ x) i := rfl

theorem flow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℝ → (Fin d → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ s y, HasDerivAt (fun s => a s y) (a s (A *ᵥ y)) s) (x : Fin d → ℂ) :
    a 1 x = a 0 (NormedSpace.exp A *ᵥ x) := by
  set c : ℝ → Fin d → ℂ := fun s => NormedSpace.exp ((1 - s) • A) *ᵥ x with hc
  set h : ℝ → ℂ := fun s => ∑ i, c s i * a s (Pi.single i 1) with hh
  have hcd : ∀ s i, HasDerivAt (fun s => c s i) (-(A *ᵥ c s) i) s := by
    intro s i
    have e1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) (A * NormedSpace.exp ((1 - s) • A)) (1 - s) :=
      hasDerivAt_exp_smul_const' A (1 - s)
    have e2 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((1 - s) • A)) (-(A * NormedSpace.exp ((1 - s) • A))) s := by
      have := e1.scomp s ((hasDerivAt_id s).const_sub 1)
      simp only [neg_smul, one_smul, id] at this
      exact this
    have e3 := (coordCLM x i).hasFDerivAt.comp_hasDerivAt s e2
    have e4 : coordCLM x i (-(A * NormedSpace.exp ((1 - s) • A))) = -(A *ᵥ c s) i := by
      rw [coordCLM_apply, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
      rfl
    exact e3.congr_deriv e4
  have hd : ∀ s, HasDerivAt h 0 s := by
    intro s
    have hs : HasDerivAt h (∑ i, (-(A *ᵥ c s) i * a s (Pi.single i 1) + c s i * a s (A *ᵥ Pi.single i 1))) s :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hcd s i).mul (ha s (Pi.single i 1)))
    convert hs using 1
    · have e4 : ∑ i, c s i * a s (A *ᵥ Pi.single i 1) = a s (A *ᵥ c s) := by
        have e7 := form_eq_sum ((a s).comp (Matrix.toLin' A)) (c s)
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply] at e7
        exact e7.symm
      have e5 : ∑ i, (A *ᵥ c s) i * a s (Pi.single i 1) = a s (A *ᵥ c s) := (form_eq_sum (a s) _).symm
      rw [Finset.sum_add_distrib, e4]
      simp only [neg_mul, Finset.sum_neg_distrib]
      rw [e5]; ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) 1 0
  have h1 : h 1 = a 1 x := by
    simp only [hh, hc, sub_self, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
    exact (form_eq_sum (a 1) x).symm
  have h0 : h 0 = a 0 (NormedSpace.exp A *ᵥ x) := by
    simp only [hh, hc, sub_zero, one_smul]
    exact (form_eq_sum (a 0) _).symm
  rw [← h1, ← h0, hconst]

theorem hasSum_exp_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (φ : (Fin d → ℂ) →ₗ[ℂ] ℂ) (x : Fin d → ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * φ ((A ^ n) *ᵥ x)) (φ (NormedSpace.exp A *ᵥ x)) := by
  let ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => φ (M *ᵥ x)
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (LinearMap.toContinuousLinearMap ψ)
  have e : ∀ n : ℕ, LinearMap.toContinuousLinearMap ψ (((n.factorial : ℂ))⁻¹ • A ^ n) =
      ((n.factorial : ℂ))⁻¹ * φ ((A ^ n) *ᵥ x) := fun n => by
    show ψ _ = _
    simp [ψ, Matrix.smul_mulVec]
  simp only [e] at h
  exact h

theorem eq_of_forms {V : Type} [AddCommGroup V] [Module ℂ V] {a b : V} (h : ∀ l : V →ₗ[ℂ] ℂ, l a = l b) : a = b := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ (a - b)]
  intro l
  simp [h l]

section Sub

variable {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N]
  (hN : ∀ y ∈ N, L y ∈ N)

def crd : N ≃ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) := (Module.finBasis ℂ N).equivFun

def emb : (Fin (Module.finrank ℂ N) → ℂ) →ₗ[ℂ] V := N.subtype ∘ₗ (crd N).symm.toLinearMap

def mat : Matrix (Fin (Module.finrank ℂ N)) (Fin (Module.finrank ℂ N)) ℂ :=
  LinearMap.toMatrix' ((crd N).toLinearMap ∘ₗ L.restrict hN ∘ₗ (crd N).symm.toLinearMap)

theorem emb_mulVec (y) : emb N (mat L N hN *ᵥ y) = L (emb N y) := by
  simp [mat, emb, LinearMap.toMatrix'_mulVec, LinearMap.restrict_apply]

theorem emb_pow_mulVec (n : ℕ) (y) : emb N ((mat L N hN ^ n) *ᵥ y) = (L ^ n) (emb N y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, emb_mulVec, pow_succ, Module.End.mul_apply]

theorem emb_crd (v : V) (hv : v ∈ N) : emb N (crd N ⟨v, hv⟩) = v := by
  simp [emb]

theorem hasSum_emb (v : V) (hv : v ∈ N) (l : V →ₗ[ℂ] ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v))
      (l (emb N (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨v, hv⟩))) := by
  have h := hasSum_exp_mulVec (mat L N hN) (l ∘ₗ emb N) (crd N ⟨v, hv⟩)
  simp only [LinearMap.comp_apply, emb_pow_mulVec, emb_crd] at h
  exact h

end Sub

theorem exists_isExp {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (hL : GlobalTheory.RealLift.LocFin L) :
    ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U := by
  have hp : ∀ v : V, ∃ u : V, ∀ l : V →ₗ[ℂ] ℂ,
      HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) (l u) := by
    intro v
    obtain ⟨N, hfin, hv, hN⟩ := hL v
    exact ⟨_, hasSum_emb L N hN v hv⟩
  choose U0 hU0 using hp
  refine ⟨{ toFun := U0, map_add' := fun v w => ?_, map_smul' := fun c v => ?_ }, fun v l => hU0 v l⟩
  · refine eq_of_forms fun l => (hU0 (v + w) l).unique ?_
    have := (hU0 v l).add (hU0 w l)
    simp only [map_add (f := _), mul_add]
    exact this
  · refine eq_of_forms fun l => (hU0 (c • v) l).unique ?_
    have := (hU0 v l).mul_left c
    have e : ∀ n : ℕ, c * (((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) = ((n.factorial : ℂ))⁻¹ * l ((L ^ n) (c • v)) :=
      fun n => by simp only [map_smul, smul_eq_mul]; ring
    simp only [e] at this
    simp only [map_smul, smul_eq_mul] at this ⊢
    exact this

def evalAt {X : Type} (p : X) : (X → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj p


open scoped Classical in
theorem evalAt_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (p : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) : evalAt p ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (p i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (p i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [evalAt, GlobalTheory.WeilM.pureA, mul_comm]


open scoped Classical in
def pureL (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun f := GlobalTheory.WeilM.pureA F f g
  map_add' f f' := by funext x; simp [GlobalTheory.WeilM.pureA, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.WeilM.pureA, mul_assoc]

theorem expAct_fock : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V]
    (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V)
    (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L →
    (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) →
    (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) →
    ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := by
  intro F _ _ κ V _ _ _ Φ L om hL hadm hSD
  obtain ⟨U, hU⟩ := exists_isExp L hL
  refine ⟨U, hU, fun T g hg => ?_⟩
  obtain ⟨N, hfin, hT, hN⟩ := hL T
  have hUT : U T = emb N (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨T, hT⟩) :=
    eq_of_forms fun l => (hU T l).unique (hasSum_emb L N hN T hT l)
  funext p
  let a : ℝ → (Fin (Module.finrank ℂ N) → ℂ) →ₗ[ℂ] ℂ := fun s =>
    evalAt p ∘ₗ om (Multiplicative.ofAdd s) ∘ₗ pureL F g ∘ₗ Φ ∘ₗ emb N
  have ha : ∀ s y, HasDerivAt (fun s => a s y) (a s (mat L N hN *ᵥ y)) s := by
    intro s y
    have h0 := hSD (emb N y) g hg _ (hadm (Multiplicative.ofAdd s) _ (evalAt_mem_adm F κ p))
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h0)
    have e : (fun u => (evalAt p ∘ₗ om (Multiplicative.ofAdd s))
        (om (Multiplicative.ofAdd (u - s)) (GlobalTheory.WeilM.pureA F (Φ (emb N y)) g))) = fun u => a u y := by
      funext u
      show evalAt p (om (Multiplicative.ofAdd s) (om (Multiplicative.ofAdd (u - s)) _)) =
        evalAt p (om (Multiplicative.ofAdd u) _)
      rw [← Module.End.mul_apply, ← map_mul, ← ofAdd_add, add_sub_cancel]
      rfl
    have ev : (evalAt p ∘ₗ om (Multiplicative.ofAdd s)) (GlobalTheory.WeilM.pureA F (Φ (L (emb N y))) g) =
        a s (mat L N hN *ᵥ y) := by
      show _ = evalAt p (om (Multiplicative.ofAdd s) (GlobalTheory.WeilM.pureA F (Φ (emb N (mat L N hN *ᵥ y))) g))
      rw [emb_mulVec]
      rfl
    rw [← e]
    exact h1.congr_deriv ev
  have hf := flow (mat L N hN) a ha (crd N ⟨T, hT⟩)
  have l1 : a 1 (crd N ⟨T, hT⟩) = om (Multiplicative.ofAdd 1) (GlobalTheory.WeilM.pureA F (Φ T) g) p := by
    show evalAt p (om (Multiplicative.ofAdd 1) (GlobalTheory.WeilM.pureA F (Φ (emb N (crd N ⟨T, hT⟩))) g)) = _
    rw [emb_crd]
    rfl
  have l0 : a 0 (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨T, hT⟩) = GlobalTheory.WeilM.pureA F (Φ (U T)) g p := by
    show evalAt p (om (Multiplicative.ofAdd 0)
      (GlobalTheory.WeilM.pureA F (Φ (emb N (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨T, hT⟩))) g)) = _
    rw [← hUT, ofAdd_zero, map_one, Module.End.one_apply]
    rfl
  rw [← l1, ← l0]
  exact hf

end GlobalTheory.ExpAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakExponential_action_on_fockVectors : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := by
  first | exact @GlobalTheory.ExpAct.expAct_fock | exact GlobalTheory.ExpAct.expAct_fock | (intros; apply GlobalTheory.ExpAct.expAct_fock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)

namespace GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure Frame (P : Pair D cc δ t0 Q) where

  A : HSp D

  B : HSp D
  rkA : A.rank = P.a
  rkB : B.rank = P.d

  ιA : Formalism.MainNotions.StandardLatticesGL3.GA D P.a →* GA D A

  ιB : Formalism.MainNotions.StandardLatticesGL3.GA D P.d →* GA D B

  KA : Subgroup (GL (Fin A.rank) (Lev.EAf D))

  KB : Subgroup (GL (Fin B.rank) (Lev.EAf D))

  m : Measure (GA D A)

  mH : Measure (GA D B)

structure IsFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  gramA : Y.A.gram = 1
  gramB : Y.B.gram = 1
  defA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.A
  defB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.B
  injA : Function.Injective Y.ιA
  injB : Function.Injective Y.ιB
  rangeA : Y.ιA.range = GfC Y.A
  rangeB : Y.ιB.range = GfC Y.B
  ratA : ∀ x, (∃ γ ∈ GQ Y.A, finHom Y.A γ = finHom Y.A (Y.ιA x)) ↔ x ∈ ratG D P.a
  ratB : ∀ h, (∃ γ ∈ GQ Y.B, finHom Y.B γ = finHom Y.B (Y.ιB h)) ↔ h ∈ ratG D P.d
  levA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.A Y.KA
  levB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B Y.KB
  levA_iff : ∀ x, Lev.finE Y.A (Y.ιA x) ∈ Y.KA ↔ x ∈ intG D P.a
  levB_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ Y.KB ↔ h ∈ P.J
  haarA : Y.m.IsHaarMeasure
  haarB : Y.mH.IsHaarMeasure
  measA : ∃ 𝓕, Links.IsMeasDef Y.A Y.KA Y.m 𝓕
  measB : ∃ 𝓕, Links.IsMeasDef Y.B Y.KB Y.mH 𝓕

structure Data (P : Pair D cc δ t0 Q) extends Frame P where

  ψ : AddChar (AF D.host.F) ℂ

  θ : InfFam D

  χA : (AE D)ˣ →* Circle

  χB : (AE D)ˣ →* Circle

  om : GlobalTheory.Core.Rk.IP.WRep A B

  vac : WO A B → ℂ

  c₁ : ℂ

namespace Data

variable {P : Pair D cc δ t0 Q} (X : Data P)

def var (k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d) : FVar D X.B.rank X.A.rank :=
  (k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2)

def fock (T : Tup D P.a P.d P.n) : WO X.A X.B → ℂ :=
  pureTensorL (aPlusAll (heisO X.ψ X.A X.B) X.θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) X.vac
    (MvPolynomial.rename X.var (minorPol D T))

def lift (T : Tup D P.a P.d P.n) : GA D X.B → ℂ := GlobalTheory.Core.Rk.IP.up X.om X.m (X.fock T) 1

end Data

structure IsWeilOf (P : Pair D cc δ t0 Q) (X : Data P) : Prop where
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  vac_theta : IsThetaFunO X.ψ X.A X.B X.vac
  vac_fock : ∀ τ, IsFockVacAt (heisO X.ψ X.A X.B) X.θ τ (cplxO 1 1) X.vac
  c₁_ne : X.c₁ ≠ 0
  ker : ∀ x h T, thetaKO X.om (X.ιA x) (X.ιB h) (X.fock T) = X.c₁ * P.term x h T

  fixA : ∀ k ∈ intG D P.a, ∀ T, X.om (X.ιA k, 1) (X.fock T) = X.fock T

  eigB : ∀ j ∈ P.J, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ T, X.om (1, X.ιB j) (X.fock T) = c • X.fock T

  infB : ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))

def IsDict (P : Pair D cc δ t0 Q) (X : Data P) : Prop := IsFrame P X.toFrame ∧ IsWeilOf P X

end GlobalTheory.NormDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis

variable {D : D7}

def SiegelWeilFockAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank → wittIndex B = 0 →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

def GlobalFormAnisoAt (A : HSp D) (L : Lat A) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA,
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    (∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s) m) ∧
    ∃ z, HolValueAt (fun s => ∫ g, integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s g ∂m) (sZero A B) z ∧
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * z

def GlobalFormAniso (D : D7) : Prop := ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → GlobalFormAnisoAt A L

def HeckeFormAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

def trivPar (a : ℕ) : LFun.Fam D.host.E := LFun.segFam (fun _ => 1) a

end GlobalTheory.BottomRallis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def twistSpan (ν β : kˣ →* ℂˣ) : Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL A k) (Ψ : Matrix A D k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧
    z = omA ν β g 1 Ψ - Ψ}

def lowRank (r : ℕ) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0}
  add_mem' hΦ hΨ := ⟨add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ hΦ := ⟨Submodule.smul_mem _ c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

theorem mem_lowRank {r : ℕ} {Φ : Matrix A D k → ℂ} :
    Φ ∈ lowRank r ↔ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0 := Iff.rfl

theorem omA_one_apply (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) (X : Matrix A D k) :
    omA ν β g 1 Φ X = (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2) *
      Φ ((g⁻¹).val * X) := by
  simp [omA, invT_val]

theorem sub_mem_twistSpan (ν β : kˣ →* ℂˣ) (g : GL A k) {Ψ : Matrix A D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k)) : omA ν β g 1 Ψ - Ψ ∈ twistSpan ν β :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

def box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Set (Matrix A D k) :=
  {X | ∀ i j, valuation k (X i j - C i j) ≤ valuation k ((ϖ ^ e i : kˣ) : k)}

def boxFn (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Matrix A D k → ℂ := (box ϖ C e).indicator 1


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_preimage (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun X : Matrix A D k => Matrix.of fun i j => (((ϖ ^ e i)⁻¹ : kˣ) : k) * (X i j - C i j)) ⁻¹'
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  ext X
  simp only [box, Set.mem_setOf_eq, Set.mem_preimage, of_apply, Valuation.mem_integer_iff, map_mul]
  refine forall₂_congr fun i j => ?_
  have h0 : 0 < valuation k ((ϖ ^ e i : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_image (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun Y : Matrix A D k => Matrix.of fun i j => C i j + ((ϖ ^ e i : kˣ) : k) * Y i j) ''
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  rw [box_eq_preimage]
  ext X
  constructor
  · intro hX
    refine ⟨_, hX, ?_⟩
    ext i j
    simp [← mul_assoc]
  · rintro ⟨Y, hY, rfl⟩
    simpa [← mul_assoc] using hY


omit [DecidableEq A] [DecidableEq D] in
theorem isCompact_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsCompact (box ϖ C e) := by
  rw [box_eq_image]
  exact isCompact_intMatrix.image (by fun_prop)


omit [DecidableEq A] [DecidableEq D] in
theorem isClopen_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsClopen (box ϖ C e) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : T2Space (Matrix A D k) := inferInstanceAs (T2Space (A → D → k))
  refine ⟨(isCompact_box ϖ C e).isClosed, ?_⟩
  rw [box_eq_preimage]
  exact isOpen_intMatrix.preimage (by fun_prop)


omit [DecidableEq A] [DecidableEq D] in
theorem boxFn_mem_SB (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    boxFn ϖ C e ∈ GlobalTheory.WeilM.SB (Matrix A D k) :=
  ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (isClopen_box ϖ C e)).isLocallyConstant,
    HasCompactSupport.intro (isCompact_box ϖ C e) fun _ hx => Set.indicator_of_notMem hx _⟩


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) : box ϖ X e = box ϖ C e := by
  ext Y
  refine ⟨fun hY i j => ?_, fun hY i j => ?_⟩
  · rw [show Y i j - C i j = (Y i j - X i j) + (X i j - C i j) by ring]
    exact Valuation.map_add_le _ (hY i j) (hX i j)
  · rw [show Y i j - X i j = (Y i j - C i j) - (X i j - C i j) by ring]
    exact Valuation.map_sub_le _ (hY i j) (hX i j)


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem boxFn_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) :
    boxFn ϖ X e = boxFn ϖ C e := by
  rw [boxFn, boxFn, box_eq_of_mem hX]

end GlobalTheory.RankCoinv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem GlobalTheory.ColNorms.familyVectors : GlobalTheory.ColNorms.FamilyVectors := by
  intro D cc δ B χ _ _ hc hδ hχ _ N N' L L' hA
  obtain ⟨h1, h2⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ N N' L L' hA
  refine ⟨h1, h2, ?_⟩
  obtain ⟨χ', e, -, hv, -⟩ := GlobalTheory.TrueTheta.exists_family_of_curve D cc δ ⟨hc, hδ⟩
  obtain ⟨e1, e2, M, hM, hC⟩ := hv N N' L L' hA
  obtain ⟨c, hcE⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hc, hδ⟩ N N' _
    (Or.inr ⟨_, _, hA.2.2.1, hA.2.2.2, rfl⟩)).1 _ h1 _ e1 e2
  have hE : B.eNat χ N N' L L' = fun z => c * e N N' L L' z := hcE
  have hQ : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α ∈ Qbar := by
    intro α
    have := GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simpa using zero_mem _⟩ α
    have hU : U D B.tor 0 (B.eNat χ N N' L L') = B.eNat χ N N' L L' := by
      funext z; simp [U, Hf]
    rwa [hU] at this
  have ht : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := fun α => by
    rw [hE, GlobalTheory.ProdThetaConj.taylor_const_mul e1.1]
  obtain ⟨α, hα⟩ : ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α ≠ 0 := by
    by_contra h
    push_neg at h
    apply e2
    funext z
    rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D e1.1 z]
    simp [h]
  have hMQ : ∀ x ∈ M, x ∈ Qbar := fun x hx => mem_algebraicClosure_iff.2
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M)))
  have hcQ : c ∈ Qbar := by
    have : c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := by rw [ht, mul_div_cancel_right₀ _ hα]
    rw [this]
    exact div_mem (hQ α) (hMQ _ (hC α))
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.1 hcQ).isIntegral
  refine ⟨M ⊔ IntermediateField.adjoin ℚ {c}, IntermediateField.finiteDimensional_sup _ _, fun β => ?_⟩
  rw [ht]
  exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.subset_adjoin ℚ {c} (Set.mem_singleton _)))
    ((le_sup_left : M ≤ _) (hC β))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open scoped IsMulCommutative in
def polEval {ι : Type} (m : ι → Module.End ℂ V) (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) :
    MvPolynomial ι ℂ →ₗ[ℂ] V :=
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range m)) :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hm i j)
  (LinearMap.applyₗ f₀ ∘ₗ (Algebra.adjoin ℂ (Set.range m)).val.toLinearMap) ∘ₗ
    (MvPolynomial.aeval (fun i => (⟨m i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range m)))).toLinearMap

def polMap (W Λ : Type) [Fintype W] [DecidableEq W] :
    (⨂[ℂ] _ : W, MvPolynomial Λ ℂ) →ₗ[ℂ] MvPolynomial (W × Λ) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (W × Λ) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Prod.mk w)).toLinearMap)

def unitAt {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    W → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

def fockM {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))

def fockD {W : Type} [DecidableEq W] {P Q R S : ℕ} (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V)
    (j : W × (Ix P Q × Ix R S)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAt j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I)))

def coefM (z ε : ℂ) : ℂ := (z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

def coefD (z ε : ℂ) : ℂ := -(z.re : ℂ) + ε * Complex.I * (z.im : ℂ)

end GlobalTheory.CCRFock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormul
namespace GlobalTheory.Published

theorem arShift_of_arChange : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  intro hE hC k _ X _ p D hX L a t ha
  have h := GlobalTheory.TwistTop.isSelfInter_shift hE hC k X p D hX L a (fun _ => t) (fun _ => rfl) ha
  rw [← mul_finsum, ← mul_assoc] at h
  exact h

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormulStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  first | exact @GlobalTheory.Published.arShift_of_arChange | exact GlobalTheory.Published.arShift_of_arChange | (intros; apply GlobalTheory.Published.arShift_of_arChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductive
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.HermLB

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]

theorem mixed_eq_of_icls (hX : IsArithVar p D) {T M N : HermLB p} {L : ι → HermLB p}
    {Ψ : MvPolynomial (Option (Option ι)) ℝ →ₗ[ℝ] ℝ}
    (hΨ : IsArFun (fun o : Option (Option ι) => o.elim T fun o => o.elim M L) D Ψ) (a b : ℤ)
    (hN : N.icls = b • T.icls + a • M.icls) {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim N L) D Φ) (n : ι → ℤ) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
      b * Ψ (MvPolynomial.X none * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) +
      a * Ψ (MvPolynomial.X (some none) * rename (some ∘ some) (lin fun i => (n i : ℝ)) ^ D) := by
  classical
  let A : Option ι → Option (Option ι) → ℤ := fun j => j.elim (fun o => o.elim b fun o => o.elim a 0)
    fun i => Pi.single (some (some i)) 1
  have h := ((Published.arIso_holds k X p D hX).2 _ _ Ψ hΨ).2.2 (Option ι) (fun o : Option ι => o.elim N L) A (by
    rintro (_ | i)
    · exact icls_eq_iff.1 (by simp [A, icls_comb, Fintype.sum_option, hN])
    · exact isometric_comb_single _ (some (some i)))
  have e₀ : (lin fun i => (A none i : ℝ)) = (b : ℝ) • MvPolynomial.X none + (a : ℝ) • MvPolynomial.X (some none) := by
    simp [A, lin, Fintype.sum_option, smul_eq_C_mul]
  have e₁ (i : ι) : (lin fun j => (A (some i) j : ℝ)) = MvPolynomial.X (some (some i)) := lin_single _
  have e₂ : aeval (fun j => lin fun i => (A j i : ℝ)) (rename some (lin fun i => (n i : ℝ))) =
      rename (some ∘ some) (lin fun i => (n i : ℝ)) := by
    conv_lhs => rw [aeval_rename]
    simp only [Function.comp_def, e₁]
    rw [rename_eq_aeval]
    rfl
  rw [Model.isArFun_unique hX hΦ h, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_pow, e₂, aeval_X, e₀,
    add_mul, smul_mul_assoc, smul_mul_assoc, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.ArInt

namespace GlobalTheory.Published

theorem arMetric_of_arMix : ArExists → ArMix → ArMetric := by
  intro HE H k _ X _ p D hX ι _ M L u hu hc Φ Φ' hΦ hΦ' n
  obtain ⟨Ψ, hΨ⟩ := ((HE k X p D hX).2 _
    fun o : Option (Option ι) => o.elim (ArInt.fnB u hu hc) fun o => o.elim M L).1
  obtain ⟨Θ, hΘ⟩ := ((HE k X p D hX).2 _ fun o : Option ι => o.elim (ArInt.fnB u hu hc) L).1
  obtain ⟨h₁, h₂⟩ := H.fnB HE hX hΘ n
  refine ⟨h₁, ?_⟩
  rw [← h₂, mixed_eq_of_icls hX hΨ 1 0 (by simp) hΦ, mixed_eq_of_icls hX hΨ 0 1 (by simp) hΘ,
    mixed_eq_of_icls hX hΨ 1 1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB M u hu hc), icls_tens, one_smul, one_smul, add_comm]) hΦ']
  push_cast
  ring

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductiveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArMetric := by
  first | exact @GlobalTheory.Published.arMetric_of_arMix | exact GlobalTheory.Published.arMetric_of_arMix | (intros; apply GlobalTheory.Published.arMetric_of_arMix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection
namespace GlobalTheory.Published

theorem arCalc_of_form_mix_projection : ArFormExists → ArMix → HeightProjection → ArCalc := fun hF hM hP =>
  have hE : ArExists := GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive hF hM
  have hC : ArChange := arChange_of_arMix hE hM
  ⟨hE, hC, GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula hE hC, hM, GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula hP, arIso_holds, GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive hE hM⟩

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjectionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionCalculus_of_form_mixed_projection : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArCalc := by
  first | exact @GlobalTheory.Published.arCalc_of_form_mix_projection | exact GlobalTheory.Published.arCalc_of_form_mix_projection | (intros; apply GlobalTheory.Published.arCalc_of_form_mix_projection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
open Matrix

namespace GlobalTheory.RealLiftGen

theorem map_star_mul {l m n : Type} [Fintype m] (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, Matrix.map_apply, star_sum]

theorem map_star_star {m n : Type} (A : Matrix m n ℂ) : (A.map star).map star = A := by
  ext i j; simp

theorem Jm_map_star (R S : ℕ) : (Jm R S).map star = Jm R S := by
  rw [Jm, Formalism.UG.P.Jpq_eq_diagonal]; ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem Jm_mul_Jm (R S : ℕ) : Jm R S * Jm R S = 1 := Formalism.UG.P.Jpq_mul_self R S

theorem gen_of_cont {n : Type} [Fintype n] [DecidableEq n] (N : ℝ → Matrix n n ℂ) (hc : Continuous N)
    (h0 : N 0 = 1) (hm : ∀ s t, N (s + t) = N s * N t) : ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) :=
  GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous N hc h0 hm

theorem cont_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)} (γ : Multiplicative ℝ →* UG (cA σ) J)
    (hγ : Continuous γ) (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) :=
  GlobalTheory.T.continuous_unitaryOneParameter_realPlaceComponent γ hγ w τ

theorem piInf_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : AE F E) :
    piInf τ (cA σ x) = star (piInf τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a e =>
    have := h.1
    have h3 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) (evInf F w a)
    simp only [piInf, cA, compInf, RingHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.id_apply, infEmb_tmul]
    rw [star_mul', h.2.2.2 τ.1 e, ← h3, Complex.star_def, Complex.conj_ofReal]

theorem mem_upq_of {R S : ℕ} (Y : Mat R S)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᵀ * Jm R S * (NormedSpace.exp (t • Y)).map star = Jm R S) :
    Y ∈ upq R S := by
  have key : Yᵀ * Jm R S + Jm R S * Y.map star = 0 := by
    letI : NormedRing (Matrix (Ix R S) (Ix R S) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Ix R S) (Ix R S) ℂ) := Matrix.linftyOpNormedAlgebra
    have hs : ∀ A : Matrix (Ix R S) (Ix R S) ℂ, A.map star = Aᴴᵀ := fun A => by ext i j; rfl
    have e1 : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᵀ = NormedSpace.exp (t • Yᵀ) := fun t => by
      rw [← Matrix.exp_transpose, Matrix.transpose_smul]
    have e2 : ∀ t : ℝ, (NormedSpace.exp (t • Y)).map star = NormedSpace.exp (t • Y.map star) := fun t => by
      rw [hs, hs, ← Matrix.exp_conjTranspose, ← Matrix.exp_transpose, Matrix.conjTranspose_smul, Matrix.transpose_smul,
        star_trivial]
    have h1 := ((hasDerivAt_exp_smul_const (Yᵀ) (0:ℝ)).mul_const (Jm R S)).mul
      (hasDerivAt_exp_smul_const (Y.map star) (0:ℝ))
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h1
    have hc : ((fun y : ℝ => NormedSpace.exp (y • Yᵀ) * Jm R S) * fun u : ℝ => NormedSpace.exp (u • Y.map star)) =
        fun _ => Jm R S := funext fun t => by
      show NormedSpace.exp (t • Yᵀ) * Jm R S * NormedSpace.exp (t • Y.map star) = Jm R S
      rw [← e1, ← e2]; exact h t
    have h2 : HasDerivAt (fun _ : ℝ => Jm R S) (Yᵀ * Jm R S * 1 + Jm R S * Y.map star) 0 :=
      h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun hc t).symm)
    have h3 := h2.unique (hasDerivAt_const (0:ℝ) (Jm R S))
    simpa only [mul_one] using h3
  have h5 : (Yᵀ * Jm R S + Jm R S * Y.map star).map star = 0 := by rw [key]; ext; simp
  rw [Matrix.map_add _ (fun a b => star_add a b), map_star_mul, map_star_mul, map_star_star, Jm_map_star] at h5
  show Yᴴ * Jm R S + Jm R S * Y = 0
  exact h5

theorem genEx : GlobalTheory.RealLift.GenEx := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC γ hγ
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm R S := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm R S * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm R S), Matrix.mul_assoc (Jm R S), hF, Jm_mul_Jm]
    have h2 : (Jm R S * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm R S * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm R S * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : InfinitePlace F → ℝ → Matrix β β ℂ :=
    fun w t => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMm : ∀ w s t, M w (s + t) = M w s * M w t := by
    intro w s t
    simp only [hM, ofAdd_add, map_mul, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM0 : ∀ w, M w 0 = 1 := by
    intro w
    simp only [hM, ofAdd_zero, map_one, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ w t, (M w t)ᵀ * K w * (M w t).map star = K w := by
    intro w t
    have hg := (γ (Multiplicative.ofAdd t)).2
    change (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)))ᵀ * J *
      (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M w t)ᵀ * J.map (piInf (τ w)) * (M w t).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  set N : InfinitePlace F → ℝ → Mat R S := fun w t => A' w * M w t * C w with hN
  have hCN : ∀ w t, C w * N w t = M w t * C w := by
    intro w t; simp only [hN, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  have hNc : ∀ w, Continuous (N w) := fun w =>
    (continuous_const.matrix_mul (cont_map γ hγ.1 w (τ w))).matrix_mul continuous_const
  have hN0 : ∀ w, N w 0 = 1 := by intro w; simp only [hN, hM0, Matrix.mul_one, hAC]
  have hNm : ∀ w s t, N w (s + t) = N w s * N w t := by
    intro w s t
    simp only [hN, hMm]
    calc A' w * (M w s * M w t) * C w = A' w * M w s * (C w * A' w) * M w t * C w := by
          rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  choose Y hY using fun w => gen_of_cont (N w) (hNc w) (hN0 w) (hNm w)
  refine ⟨Y, fun w => mem_upq_of (Y w) fun t => ?_, fun t w => ?_⟩
  · rw [← hY w t, ← hF w]
    calc (N w t)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (N w t).map star
        = (C w * N w t)ᵀ * K w * (C w * N w t).map star := by
          simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = (C w)ᵀ * ((M w t)ᵀ * K w * (M w t).map star) * (C w).map star := by
          simp only [hCN, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
      _ = _ := by rw [hMu]
  · show M w t * C w = _
    rw [← hCN, hY]

end GlobalTheory.RealLiftGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamSubgroup_generators_exist : GlobalTheory.RealLift.GenEx := by
  first | exact @GlobalTheory.RealLiftGen.genEx | exact GlobalTheory.RealLiftGen.genEx | (intros; apply GlobalTheory.RealLiftGen.genEx <;> assumption)
end
end
