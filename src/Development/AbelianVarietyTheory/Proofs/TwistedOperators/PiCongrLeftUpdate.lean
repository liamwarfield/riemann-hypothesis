module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
  Formalism.L2.SG.EvalTOntoRep MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def contSub : Submodule ℂ (L2X X) where
  carrier := {f | ∃ φ, IsContRep X f φ}
  add_mem' := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨φ + ψ, contRep_add X hφ hψ⟩
  zero_mem' := ⟨0, contRep_zero X⟩
  smul_mem' := fun a _ ⟨φ, hφ⟩ => ⟨a • φ, contRep_smul X a hφ⟩

def repOn : contSub X →ₗ[ℂ] (X.B.I.GA → ℂ) where
  toFun f := f.2.choose
  map_add' f g := contRep_unique X (f + g).2.choose_spec (contRep_add X f.2.choose_spec g.2.choose_spec)
  map_smul' a f := contRep_unique X (a • f).2.choose_spec (contRep_smul X a f.2.choose_spec)

def contRepL : L2X X →ₗ[ℂ] (X.B.I.GA → ℂ) := (LinearMap.exists_extend (repOn X)).choose

theorem contRepL_spec {f : L2X X} {φ : X.B.I.GA → ℂ} (hf : IsContRep X f φ) : contRepL X f = φ := by
  have e := LinearMap.congr_fun (LinearMap.exists_extend (repOn X)).choose_spec ⟨f, φ, hf⟩
  have e' : contRepL X f = repOn X ⟨f, φ, hf⟩ := e
  rw [e']
  exact contRep_unique X (Exists.choose_spec (p := fun φ => IsContRep X f φ) _) hf

theorem eq_of_inner_tens {p q : X.B.Hs} (h : ∀ y, ⟪p, X.B.tens y⟫_ℂ = ⟪q, X.B.tens y⟫_ℂ) : p = q := by
  let f : X.B.Hs →L[ℂ] ℂ := innerSL ℂ (p - q)
  have hsp : (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} := by
    refine (Submodule.span_le (p := LinearMap.ker (f : X.B.Hs →ₗ[ℂ] ℂ))).2 ?_
    rintro _ ⟨y, rfl⟩
    show ⟪p - q, X.B.tens y⟫_ℂ = 0
    rw [inner_sub_left, h y, sub_self]
  have hcl : closure (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} :=
    closure_minimal hsp (isClosed_eq f.continuous continuous_const)
  rw [X.B.tens_spec.2.2.closure_eq] at hcl
  have h0 : f (p - q) = 0 := hcl (Set.mem_univ _)
  have : ⟪p - q, p - q⟫_ℂ = 0 := h0
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem prod_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] (x y : ∀ i, H i) (v : ι) (z : H v) :
    ∏ w, ⟪Function.update x v z w, y w⟫_ℂ = ⟪z, y v⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪x w, y w⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_add [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a b : X.B.H v) :
    X.B.tens (Function.update x v (a + b)) =
      X.B.tens (Function.update x v a) + X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_add_left, X.B.tens_spec.1, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, prod_update,
    inner_add_left, add_mul]

theorem tens_update_smul [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a : ℂ) (b : X.B.H v) :
    X.B.tens (Function.update x v (a • b)) = a • X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_smul_left, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, inner_smul_left, mul_assoc]

variable {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S)

def vecC (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) : ∀ v, X.B.H v :=
  Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (u τ : M.H τ))

theorem piCongrLeft_update {α β : Type} [DecidableEq α] [DecidableEq β] (P : β → Type) (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) (x : P (e a)) :
    Equiv.piCongrLeft P e (Function.update f a x) = Function.update (Equiv.piCongrLeft P e f) (e a) x := by
  apply (Equiv.piCongrLeft P e).symm.injective
  rw [Equiv.symm_apply_apply]
  funext a'
  rw [Equiv.piCongrLeft_symm_apply]
  by_cases ha : a' = a
  · subst ha
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ha, Function.update_of_ne (e.injective.ne ha), Equiv.piCongrLeft_apply_apply]

theorem vecC_update [DecidableEq D.what₂.Tau] [DecidableEq (NumberField.InfinitePlace X.B.I.F)]
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    vecC X M c (Function.update u τ w) = Function.update (vecC X M c u) (X.pl.symm τ) (c τ (w : M.H τ)) := by
  unfold vecC
  rw [← piCongrLeft_update]
  congr 1
  funext τ'
  exact Function.apply_update (fun i (s : M.sm i) => c i (s : M.H i)) u τ w τ'

theorem vecC_eq (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (g : ∀ v, X.B.H v)
    (hg : ∀ τ, c τ (u τ : M.H τ) = g (X.pl.symm τ)) : vecC X M c u = g := by
  unfold vecC
  have : (fun τ => c τ (u τ : M.H τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm g := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply, hg τ]
  rw [this, Equiv.apply_symm_apply]

def conjMap (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) : MMap M where
  toFun u := fun y => star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹)))
  map_update_add' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_add, map_add (f := _), tens_update_add, Pi.add_apply, star_add]
  map_update_smul' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_smul, LinearIsometryEquiv.map_smulₛₗ, tens_update_smul, map_smul,
      Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, star_star, RingHom.id_apply]

theorem conjMap_apply (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (u : M.Vec) (y : GA D (D.sp.Y 0)) :
    conjMap X M c A h t u y = star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹))) := rfl

end GlobalTheory.ConjRowMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PhaseReal

variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  ext i j
  rfl

theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram :=
  Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i

theorem infPart_cA (z : AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem hO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    hO V W (isoPart V W C κ) (isoPart V W C' (y.map (incA D))) =
      Matrix.trace ((adj D y * W.gram).map (incA D) * κ) := by
  have hz : (y * (adj D C' * V.gram))ᴴ = V.gram * C' * adj D y := by
    rw [conjTranspose_mul, conjTranspose_mul, gram_ct, adj_eq, adj_eq, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hu : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D) := by
    rw [Matrix.map_mul]
    rfl
  have hu' : ((isoPart V W C' (y.map (incA D))).map (cA D))ᵀ = (V.gram * C' * adj D y).map (incA D) := by
    rw [hu, ← hz]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.cA_incA _
  have e1 : (V.gram⁻¹).map (incA D) * (V.gram * C' * adj D y).map (incA D) * W.gram.map (incA D) =
      C'.map (incA D) * (adj D y * W.gram).map (incA D) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    rw [Matrix.mul_assoc V.gram, Matrix.nonsing_inv_mul_cancel_left _ _ (Formalism.L2.Theta.gram_det_ne V).isUnit,
      Matrix.mul_assoc]
  have e2 : (adj D C * V.gram).map (incA D) * C'.map (incA D) = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e3 : isoPart V W C κ = κ * (adj D C * V.gram).map (incA D) := rfl
  rw [hO_eq_trace, hu', e1, e3, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, e2,
    Matrix.mul_one]

theorem pairQ_map (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (pairQ W y).map (incA D) = incA D D.host.xi0 • (adj D y * W.gram).map (incA D) := by
  ext i j
  simp only [pairQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem symplO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    symplO V W (isoPart V W C' (y.map (incA D))) (isoPart V W C κ) =
      -Algebra.trace (AF D.host.F) (AE D) (Matrix.trace ((pairQ W y).map (incA D) * κ)) := by
  unfold symplO
  rw [← GlobalTheory.FinTranslate.hO_herm, hO_iso V W C C' hC, pairQ_map, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem finPart_trace {m n : ℕ} (P : Matrix (Fin n) (Fin m) (AE D)) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) : finPart D (Matrix.trace (P * κ)) = 0 := by
  have h : ∀ i j, finPart D (κ i j) = 0 := fun i j => congrFun (congrFun hκ i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem trace_real {t : AE D} (h : finPart D t = 0) :
    Algebra.trace (AF D.host.F) (AE D) t =
      pairA D.host.F (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t)) 0 := by
  have h3 : GlobalTheory.FinTranslate.eInf D * Algebra.trace (AF D.host.F) (AE D) t =
      Algebra.trace (AF D.host.F) (AE D) t := by
    conv_rhs => rw [← GlobalTheory.FinTranslate.smul_eq_self_of_fin h, map_smul, smul_eq_mul]
  refine Prod.ext rfl ?_
  have := congrArg Prod.snd h3
  exact this.symm.trans (zero_mul _)

theorem theta_trace (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : AE D) :
    θ ρ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) := by
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hA : algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t) = t + cA D t :=
    GlobalTheory.SelfDualLatticeCompare.trace_tensor (AF D.host.F) hcm t
  have hB := congrArg (infPart D) hA
  rw [map_add (f := _), infPart_cA] at hB
  have hC : infPart D (algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t)) =
      fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [← hC, hB, map_add (f := _), GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ ρ), Complex.add_conj]

theorem theta_pair (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {m n : ℕ}
    (P : Matrix (Fin n) (Fin m) D.host.E) (κ : Mx D m n) :
    θ ρ (infPart D (Matrix.trace (P.map (incA D) * κ))) =
      Matrix.trace (P.map (tauE D ρ) * compAt θ ρ κ) := by
  have h : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hθ ρ).1 e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt, h]

end GlobalTheory.PhaseReal

theorem GlobalTheory.PhaseReal.phase_eq : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  intro D V W r C C' hC ψ hψ θ hθ y κ hκ
  unfold phase
  rw [GlobalTheory.PhaseReal.symplO_iso V W C C' hC]
  set t := Matrix.trace ((pairQ W y).map (incA D) * κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ (-T) = psiInf D.host.F ψ (-(fstA D.host.F T)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F T))
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F T)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace ((pairQ W y).map (tauE D ρ) * compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, ht,
      GlobalTheory.PhaseReal.theta_pair θ hθ ρ]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.PhaseReal.phase_eq | exact GlobalTheory.PhaseReal.phase_eq | (intros; apply GlobalTheory.PhaseReal.phase_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.VacOff

variable {D : D7}

theorem placeIdem_smul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D w ε) (hwv : w ≠ v) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun x => x = v) : algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hx
    have hβα : β * α = 0 := by
      refine RestrictedProduct.ext _ _ fun y => ?_
      change evalV D.host.F y (β * α) = evalV D.host.F y 0
      rw [map_mul, map_zero]
      by_cases hy : y = w
      · subst hy; rw [hP y hwv, mul_zero]
      · rw [h0 y hy, zero_mul]
    have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = (0 : AE D)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, TensorProduct.zero_tmul]
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem idemSum_mul_off {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {Pset : Finset (Pl D.host.E)} (he : IsIdemSum e Pset)
    (hv : ∀ PP ∈ Pset, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) {u : WO S T} (hu : u ∈ latO S T LS LT fun x => x = v) (a b) :
    e * u a b = 0 ∧ cA D e * u a b = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have key : ∀ PP ∈ Pset, es PP * u a b = 0 ∧ cA D (es PP) * u a b = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hw : w ≠ v := fun h => hv PP hPP (by
      rw [← h]; exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP w ε (hes PP hPP) hε a3)
    have h0 := congrFun (congrFun (placeIdem_smul_off hε hw hu) a) b
    rw [Matrix.smul_apply, smul_eq_mul, ← a3, Matrix.zero_apply] at h0
    have c1 : cA D (es PP) * cA D (es PP) = cA D (es PP) := by rw [← map_mul, a1]
    have c2 : cA D (es PP) * es PP = 0 := by rw [mul_comm, a2]
    refine ⟨?_, ?_⟩
    · linear_combination es PP * h0 - u a b * a1 - u a b * a2
    · linear_combination cA D (es PP) * h0 - u a b * c1 - u a b * c2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).1
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).2

end GlobalTheory.FinZeta.VacOff


open GlobalTheory.FinZeta.VacOff in
theorem GlobalTheory.FinZeta.levVec_vacFin : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ v ∉ finS R t, VacFin R.ψ (Vc D i) (Wc D i) v f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h
  obtain ⟨hC, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have := hpt 1
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  refine ⟨hθ, fun v hv => ⟨hθ, ?_⟩⟩
  obtain ⟨hf₀, e, he, hth⟩ := hlv
  have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (frameLat (Vc D i) : Set _) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hC.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
  have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (frameLat (Wc D i) : Set _) := by
    rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    obtain ⟨c, -, -, -, h1, h2⟩ := hC.lev.βW i
    ext x
    constructor
    · intro hx
      simpa using h2 x hx
    · intro hx
      simpa using h1 x hx
  have hlat := hf₀.2.lat
  have hle : latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v) ≤
      latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
    rw [hV, hW]
    exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hoff : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun PP hPP h0 =>
    hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (frameLat (Vc D i) : Set _) (frameLat (Wc D i) : Set _) (fun u => u = v),
      ∀ a b, cA D e * u a b = 0 ∧ cA D (cA D e) * u a b = 0 := fun u hu a b => by
    obtain ⟨h1, h2⟩ := idemSum_mul_off he hoff hu a b
    rw [GlobalTheory.DualPairCheck.cA_cA]
    exact ⟨h2, h1⟩
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth (2 • u)
      (hz _ (AddSubgroup.nsmul_mem _ hu 2)) (hlat.1 u (hle hu))
  · exact GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ _ _ _ _ _ _ hth u (hz u hu) (hlat.2 e' he' u (hle hu) hh)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorFiniteDatumIsThetaVacuumOffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelVector_finiteDatum_isTheta_vacuum_off : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ v ∉ finS R t, VacFin R.ψ (Vc D i) (Wc D i) v f := by
  first | exact @GlobalTheory.FinZeta.levVec_vacFin | exact GlobalTheory.FinZeta.levVec_vacFin | (intros; apply GlobalTheory.FinZeta.levVec_vacFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
noncomputable section

namespace GlobalTheory.SplitFlag

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions GlobalTheory.AdelicU GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

def wPart (τ : E →ₐ[F] Fv F v) (W : Submodule E V.V) : Submodule (Fv F v) (Fin V.rank → Fv F v) where
  carrier := splitVec τ '' (extSub (F := F) V (Fv F v) W : Set (Fin V.rank → Fv F v ⊗[F] E))
  zero_mem' := ⟨0, zero_mem _, funext fun _ => map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z, add_mem hy hz, splitVec_add τ y z⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    refine ⟨algebraMap (Fv F v) (Fv F v ⊗[F] E) c • y, Submodule.smul_mem _ _ hy, ?_⟩
    rw [splitVec_smul, AlgHom.commutes]
    rfl

theorem wPart_mono (τ : E →ₐ[F] Fv F v) {A B : Submodule E V.V} (h : A ≤ B) : wPart τ A ≤ wPart τ B := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, GlobalTheory.Cusp.extSub_mono V _ h hy, rfl⟩

section Perp

theorem le_perp_perp (W : Submodule E V.V) : W ≤ perp V (perp V W) := fun y hy =>
  GlobalTheory.Cusp.mem_perp.2 fun x hx => by
    have := GlobalTheory.Cusp.mem_perp.1 hx y hy
    simp only [HSpace.hD] at this ⊢
    rw [← V.herm.eq, this, map_zero]

theorem perp_perp (W : Submodule E V.V) : perp V (perp V W) = W := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_perp_perp W) ?_).symm
  have h1 := GlobalTheory.IsoDim.finrank_perp_add V W
  have h2 := GlobalTheory.IsoDim.finrank_perp_add V (perp V W)
  omega

end Perp

section Split

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (τ : E →ₐ[F] Fv F v)


include h in
theorem mem_extSub_iff_split {W : Submodule E V.V} {y : Fin V.rank → Fv F v ⊗[F] E} :
    y ∈ extSub (F := F) V (Fv F v) W ↔
      splitVec τ y ∈ wPart τ W ∧ splitVec (τ.comp hc.sig) y ∈ wPart (τ.comp hc.sig) W := by
  refine ⟨fun hy => ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩, fun ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ => ?_⟩
  rw [← (splitVecEquiv h τ).symm_apply_apply y]
  change splitIncl h τ (splitVec τ y) + splitIncl h (τ.comp hc.sig) (splitVec (τ.comp hc.sig) y) ∈ _
  rw [← e₁, ← e₂, splitIncl_splitVec, splitIncl_splitVec]
  exact add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)

include h in
theorem splitIncl_mem_extSub_iff {W : Submodule E V.V} {u : Fin V.rank → Fv F v} :
    splitIncl h τ u ∈ extSub (F := F) V (Fv F v) W ↔ u ∈ wPart τ W := by
  rw [mem_extSub_iff_split hc h τ, splitVec_splitIncl, splitVec_comp_splitIncl]
  exact and_iff_left (zero_mem _)

end Split

section Dual

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram) (τ : E →ₐ[F] Fv F v)


include h hJ in
theorem mem_wPart_comp_iff {W : Submodule E V.V} {u' : Fin V.rank → Fv F v} :
    u' ∈ wPart (τ.comp hc.sig) W ↔ ∀ u ∈ wPart τ (perp V W), u' ⬝ᵥ V.gram.map τ *ᵥ u = 0 := by
  rw [← splitIncl_mem_extSub_iff hc h (τ.comp hc.sig)]
  conv_lhs => rw [← perp_perp W]
  rw [GlobalTheory.Cusp.mem_extSub_perp hc V]
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    have := congrArg (splitProj (τ.comp hc.sig)) (H x hx)
    change splitProj (τ.comp hc.sig) (hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x) = _ at this
    rwa [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero] at this
  · intro H x hx
    change hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x = 0
    refine split_ext h τ ?_ ?_
    · rw [splitProj_hLin, splitVec_splitIncl_comp, map_zero, Matrix.mulVec_zero, dotProduct_zero]
    · rw [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero]
      exact H _ ⟨x, hx, rfl⟩

end Dual

section Chain

def flagChain (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v) (j : Fin (2 * 𝔉.k + 2)) :
    Submodule (Fv F v) (Fin V.rank → Fv F v) :=
  if hj : (j : ℕ) ≤ 𝔉.k then wPart τ (𝔉.X ⟨j, by omega⟩)
  else wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩))

variable (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v)

theorem flagChain_of_le {j : Fin (2 * 𝔉.k + 2)} (hj : (j : ℕ) ≤ 𝔉.k) :
    flagChain 𝔉 τ j = wPart τ (𝔉.X ⟨j, by omega⟩) := dif_pos hj

theorem flagChain_of_lt {j : Fin (2 * 𝔉.k + 2)} (hj : 𝔉.k < (j : ℕ)) :
    flagChain 𝔉 τ j = wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩)) := dif_neg (not_le.2 hj)

theorem flagChain_mono : Monotone (flagChain 𝔉 τ) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  rcases le_or_gt (i : ℕ) 𝔉.k with hi | hi <;> rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_le 𝔉 τ hj]
    exact wPart_mono τ (𝔉.strictMono.monotone (Fin.mk_le_mk.2 hij'))
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (𝔉.le_perp _ _)
  · omega
  · rw [flagChain_of_lt 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (GlobalTheory.Cusp.perp_anti (𝔉.strictMono.monotone (Fin.mk_le_mk.2 (by omega))))

theorem wPart_bot : wPart τ (⊥ : Submodule E V.V) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, GlobalTheory.Cusp.extSub_bot, Submodule.mem_bot] at hy
  rw [hy, Submodule.mem_bot]
  exact funext fun _ => map_zero _

theorem wPart_top {hc : CMData F E} (h : IsCMExt F E hc.sig) : wPart τ (⊤ : Submodule E V.V) = ⊤ :=
  eq_top_iff.2 fun u _ => ⟨splitIncl h τ u, by rw [GlobalTheory.Cusp.extSub_top]; trivial, splitVec_splitIncl h τ u⟩

theorem flagChain_zero : flagChain 𝔉 τ 0 = ⊥ := by
  rw [flagChain_of_le 𝔉 τ (Nat.zero_le _)]
  convert wPart_bot τ
  exact 𝔉.zero

theorem flagChain_last {hc : CMData F E} (h : IsCMExt F E hc.sig) : flagChain 𝔉 τ (Fin.last _) = ⊤ := by
  rw [flagChain_of_lt 𝔉 τ (by simp; omega)]
  convert wPart_top τ h
  have : (⟨2 * 𝔉.k + 1 - (Fin.last (2 * 𝔉.k + 1) : ℕ), by simp⟩ : Fin (𝔉.k + 1)) = 0 := Fin.ext (by simp)
  rw [this, 𝔉.zero, GlobalTheory.Cusp.perp_bot]

end Chain

end GlobalTheory.SplitFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace ENNReal NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

namespace GlobalTheory.PairLift.LowAllPf

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem kernel_zero : thetaKO ω g h 0 = 0 := by simp [thetaKO]

theorem kernel_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO, map_add (f := _)]

theorem kernel_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO, map_sub]

theorem kernel_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO, map_smul]

end Kernel

theorem multT_apply_smooth_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT'.aut w), GlobalTheory.MultMem.isCuspFun_smul c (hT'.cusp w)⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem liftInt_span_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, funext fun x => ?_⟩
    simp [Lift.liftInt, kernel_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (a + b) Φ x =
        Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x + Lift.liftInt ν 𝓕 (thetaKO ω) b Φ x := by
      simp only [Lift.liftInt, kernel_add, add_mul]
      exact integral_add (hI a ha.1 x) (hI b hb.1 x)
    simp [e, congrFun ha.2 x, congrFun hb.2 x]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (c • a) Φ x = c * Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x := by
      simp only [Lift.liftInt, kernel_smul, mul_assoc]
      exact integral_const_mul c _
    simp [e, congrFun ha.2 x]

theorem eq_zero_of_le_mul_all {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  rcases eq_or_ne K 0 with hK0 | hK0
  · have h1 := h 1 one_pos
    rw [hK0, zero_mul] at h1
    exact h1.trans zero_le
  · refine (h (ε / K) (ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') hK)).trans (le_of_eq ?_)
    exact ENNReal.mul_div_cancel hK0 hK

theorem liftInt_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hKt : (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (hL.decay_ne_top Φ hΦ A)
  funext x
  have hI : ∀ f', IsThetaFunO ψ V W f' → IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' => by
    simpa only [rTr, mul_one] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ δ : ℝ≥0∞, 0 < δ → ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ / height V x ^ A) ≤
      (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by
    intro δ hδ
    obtain ⟨g, hgU, hg0, hlt⟩ := happ d δ hδ
    have hfg : f - g ∈ GlobalTheory.Size.thetaLevel ψ V W U := sub_mem hf hgU
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x := by
      have e' : Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x =
          Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x - Lift.liftInt ν 𝓕 (thetaKO ω) g Φ x := by
        simp only [Lift.liftInt, kernel_sub, sub_mul]
        exact integral_sub (hI f hf.1) (hI g hgU.1)
      rw [e', congrFun hg0 x, Pi.zero_apply, sub_zero]
    have h2 : ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x‖ / height V x ^ A) ≤
        growthSob θ V 0 A (lift ω ν 𝓕 (f - g) Φ) := by
      simp only [growthSob, wordSum_zero, growthSize]
      exact le_iSup (fun y => ENNReal.ofReal (‖lift ω ν 𝓕 (f - g) Φ y‖ / height V y ^ A)) x
    rw [e]
    calc _ ≤ _ := h2
      _ ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := hC (f - g) hfg Φ hΦ
      _ = (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * sobO ψ θ μ 𝓓 d (f - g) := by ring
      _ ≤ (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by gcongr
  have h0 := eq_zero_of_le_mul_all hKt key
  rw [ENNReal.ofReal_eq_zero] at h0
  have hpos : 0 < height V x ^ A := pow_pos (height_pos V x) A
  have h3 : ‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ ≤ 0 := by
    simpa using (div_le_iff₀ hpos).1 h0
  exact norm_le_zero_iff.1 h3

end GlobalTheory.PairLift.LowAllPf

namespace GlobalTheory.PairLift

theorem lowAll_of_lowFock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  intro D X hIn hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v f' hf
  obtain ⟨χS, χT, hW, -⟩ := id hω
  have hL := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hFv := LowAllPf.multT_apply_smooth_cusp θ M' ∅ 1 F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  obtain ⟨U, hU, hfU, happ⟩ := hIn.dense V' W A (Fr.ofModel M') θ ψ hW.std hθ μ 𝓓 hμ f' hf
  have hI : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa only [rTr, mul_one] using hL.integ f (F v) hf hFv x 1
  have hspan := LowAllPf.liftInt_span_zero hI
    (s := {g | ∃ f₀ P, IsVacF ψ θ A (Fr.ofModel M') f₀ ∧ f₀ ∈ GlobalTheory.Size.thetaLevel ψ V' W U ∧
      g = ptF ψ θ A (Fr.ofModel M') f₀ P})
    (by
      rintro _ ⟨f₀, P, hv, -, rfl⟩
      exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hv.1 P,
        hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hv P⟩)
  refine LowAllPf.liftInt_zero_of_approx hL hFv hμ.1 hμ.2.1 hU hfU fun d δ hδ => ?_
  obtain ⟨g, hg, hgU, hlt⟩ := happ d δ hδ
  exact ⟨g, hgU, (hspan g hg).2, hlt⟩

end GlobalTheory.PairLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFockStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  first | exact @GlobalTheory.PairLift.lowAll_of_lowFock | exact GlobalTheory.PairLift.lowAll_of_lowFock | (intros; apply GlobalTheory.PairLift.lowAll_of_lowFock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasure
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TorCentTop

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}
  {k : Type} [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k]


omit [FiniteDimensional F E] [TopologicalSpace k] [IsTopologicalRing k] in
theorem isScalarTower_base : IsScalarTower k (k ⊗[F] E) (k ⊗[F] Fld P) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change c ⊗ₜ[F] (1 : Fld P) = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) (c ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

theorem continuous_mulMat (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) : Continuous (mulMat φ) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : ContinuousAdd (k ⊗[F] E) := IsModuleTopology.toContinuousAdd k _
  haveI := isScalarTower_base (k := k) (P := P)
  refine continuous_matrix fun i j => ?_
  have e : ∀ l, mulMat φ l i j = φ (l * φ.symm (Pi.single j 1)) i := fun l => by
    rw [← mulMat_mulVec, φ.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [e]
  exact IsModuleTopology.continuous_of_linearMap (((LinearMap.proj i).comp (φ.toLinearMap.comp
    (LinearMap.mulRight (k ⊗[F] E) (φ.symm (Pi.single j 1))))).restrictScalars k)

theorem torUnit_val (t : Tor P k) : (torUnit t).1 = (matHom k (star' P) (one₁ P) t).1 0 0 :=
  Matrix.det_fin_one _

theorem continuous_torUnit : Continuous fun t : Tor P k => (torUnit t).1 := by
  simp only [torUnit_val]
  exact (Units.continuous_val.comp (isEmbedding_matHom k (star' P) (one₁ P)).continuous).matrix_elem 0 0

theorem matHom_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (matHom k σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl

theorem torUnit_eq {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) (t : Tor P k) : (torUnit t).1 = φ.symm ((matHom k σ J (torEmb h t)).1 *ᵥ φ 1) := by
  rw [matHom_torEmb, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_one]

theorem continuous_torEmb {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)}
    (h : IsIsom P k J x φ) : Continuous (torEmb h) := by
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  refine (isEmbedding_matHom k σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun t => (matHom k σ J (torEmb h t)).1
    simp only [matHom_torEmb]
    exact (continuous_mulMat φ).comp continuous_torUnit
  · change Continuous fun t => (matHom k σ J (torEmb h t))⁻¹.1
    simp only [← map_inv, matHom_torEmb]
    exact (continuous_mulMat φ).comp (continuous_torUnit.comp continuous_inv)

theorem continuous_back (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) :
    Continuous fun g : HA k σ J => φ.symm ((matHom k σ J g).1 *ᵥ φ 1) := by
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology k (k ⊗[F] Fld P) := ⟨rfl⟩
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  haveI := isScalarTower_base (k := k) (P := P)
  haveI : ContinuousAdd (k ⊗[F] Fld P) := IsModuleTopology.toContinuousAdd k _
  have h1 : Continuous (φ.symm.toLinearMap.restrictScalars k) := IsModuleTopology.continuous_of_linearMap _
  refine h1.comp (Continuous.matrix_mulVec ?_ continuous_const)
  exact Units.continuous_val.comp (isEmbedding_matHom k σ J).continuous

theorem torEquiv_cent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ e : Tor P k ≃ₜ* cent (gam h), (∀ t, (e t).1 = torEmb h t) ∧ ∀ dt : Measure (Tor P k), centMeas h dt = dt.map e := by
  intro F E _ _ _ _ _ σ hCM r n P J hJ k _ _ _ _ _ x φ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : FiniteDimensional F (Fld P) := Module.Finite.trans E _
  obtain ⟨-, -, hinj, hrange⟩ := GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hCM r n P J hJ k x φ h
  let e0 : Tor P k ≃* cent (gam h) := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  have he : ∀ t, (e0 t).1 = torEmb h t := fun t => rfl
  have hs : ∀ s, torEmb h (e0.symm s) = s.1 := fun s => by rw [← he, e0.apply_symm_apply]
  have hback : ∀ s, (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0 = φ.symm ((matHom k σ J s.1).1 *ᵥ φ 1) :=
    fun s => by rw [← torUnit_val, GlobalTheory.TorCentTop.torUnit_eq h, hs]
  let e : Tor P k ≃ₜ* cent (gam h) :=
    { e0 with
      continuous_toFun := continuous_induced_rng.2 (GlobalTheory.TorCentTop.continuous_torEmb h)
      continuous_invFun := by
        refine (isEmbedding_matHom k (star' P) (one₁ P)).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s)).1 0 0
          simp only [hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp continuous_subtype_val
        · refine continuous_matrix fun i j => ?_
          rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
          change Continuous fun s => (matHom k (star' P) (one₁ P) (e0.symm s))⁻¹.1 0 0
          simp only [← map_inv, hback]
          exact (GlobalTheory.TorCentTop.continuous_back φ).comp (continuous_subtype_val.comp continuous_inv) }
  refine ⟨e, fun t => rfl, fun dt => ?_⟩
  haveI : IsModuleTopology k (k ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (k ⊗[F] E) := IsModuleTopology.isTopologicalRing k _
  have eh : (k ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → k) :=
    let b := (Algebra.TensorProduct.basis k (Module.finBasis F E)).equivFun
    { b.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap }
  haveI : T2Space (k ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : T2Space (GL (Fin n) (k ⊗[F] E)) := Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (HA k σ J) := (isEmbedding_matHom k σ J).t2Space
  have hset : (cent (gam h) : Set (HA k σ J)) = {g | gam h * g = g * gam h} := by
    ext g; simp [cent, Subgroup.mem_centralizer_iff]
  have hclosed : IsClosed (cent (gam h) : Set (HA k σ J)) := by
    rw [hset]; exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hf : (torEmb h : Tor P k → HA k σ J) = Subtype.val ∘ e := funext fun t => rfl
  unfold centMeas
  rw [hf, ← Measure.map_map measurable_subtype_coe (map_continuous e).measurable]
  exact (MeasurableEmbedding.subtype_coe hclosed.measurableSet).comap_map _

end GlobalTheory.TorCentTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasureStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ e : Tor P k ≃ₜ* cent (gam h), (∀ t, (e t).1 = torEmb h t) ∧ ∀ dt : Measure (Tor P k), centMeas h dt = dt.map e := by
  first | exact @GlobalTheory.TorCentTop.torEquiv_cent | exact GlobalTheory.TorCentTop.torEquiv_cent | (intros; apply GlobalTheory.TorCentTop.torEquiv_cent <;> assumption)
end
end
