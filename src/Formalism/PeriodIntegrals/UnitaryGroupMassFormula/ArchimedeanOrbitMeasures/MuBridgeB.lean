module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MuBridgeA
noncomputable section

namespace PI.AprimeInfW.MuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

section Tr

variable {D : D7} (X : HidaSetting D)

theorem emb_real (v : InfinitePlace X.B.I.F) (a : X.B.I.F) : conj (v.embedding a) = v.embedding a := by
  have hv : v.IsReal := totReal_of X v
  have h := NumberField.ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hv)
  have := RingHom.congr_fun h a
  simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

theorem phi_star (v : InfinitePlace X.B.I.F) (e : X.B.I.E) : X.B.I.φ v (star e) = conj (X.B.I.φ v e) :=
  X.B.I.cm.cmUnram.2.1 _ e

theorem phi_notReal (v : InfinitePlace X.B.I.F) : ¬ ∀ e : X.B.I.E, conj (X.B.I.φ v e) = X.B.I.φ v e := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal (X.B.I.φ v) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext e
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq, h e]
  have hc := X.B.I.cm.cmUnram.1.isComplex (InfinitePlace.mk (X.B.I.φ v))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem emb_trace (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    v.embedding (Algebra.trace X.B.I.F X.B.I.E e) = X.B.I.φ v e + conj (X.B.I.φ v e) := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  let φA : X.B.I.E →ₐ[X.B.I.F] ℂ := { X.B.I.φ v with commutes' := X.B.I.φ_over v }
  let ψA : X.B.I.E →ₐ[X.B.I.F] ℂ :=
    { (starRingEnd ℂ).comp (X.B.I.φ v) with
      commutes' := fun a => by
        show conj (X.B.I.φ v (algebraMap X.B.I.F X.B.I.E a)) = v.embedding a
        rw [X.B.I.φ_over, emb_real] }
  have hne : φA ≠ ψA := by
    intro h
    apply phi_notReal X v
    intro e
    have := congrArg (fun f : X.B.I.E →ₐ[X.B.I.F] ℂ => f e) h
    exact this.symm
  have hcard : Fintype.card (X.B.I.E →ₐ[X.B.I.F] ℂ) = 2 := by
    rw [AlgHom.card X.B.I.F X.B.I.E ℂ, X.B.I.cm.deg2]
  have huniv : (Finset.univ : Finset (X.B.I.E →ₐ[X.B.I.F] ℂ)) = {φA, ψA} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have h := trace_eq_sum_embeddings (K := X.B.I.F) (L := X.B.I.E) ℂ (x := e)
  rw [huniv, Finset.sum_pair hne] at h
  exact h

theorem evInf_conj (v : InfinitePlace X.B.I.F) (a : Ainf X.B.I.F) :
    conj (PI.AprimeInfU.evInf X v a) = PI.AprimeInfU.evInf X v a := by
  have hv : v.IsReal := totReal_of X v
  show conj (InfinitePlace.Completion.extensionEmbedding v (a v)) =
    InfinitePlace.Completion.extensionEmbedding v (a v)
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem evInf_alg (v : InfinitePlace X.B.I.F) (a : X.B.I.F) :
    PI.AprimeInfU.evInf X v (algebraMap X.B.I.F (Ainf X.B.I.F) a) = v.embedding a :=
  evV_algebraMap X.B.I v a

theorem trace_one_tmul (e : X.B.I.E) :
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) =
      algebraMap X.B.I.F (Ainf X.B.I.F) (Algebra.trace X.B.I.F X.B.I.E e) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem evInf_trace (v : InfinitePlace X.B.I.F) (z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.evInf X v (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) z) =
      PI.AprimeInfU.thetaInf X v z + conj (PI.AprimeInfU.thetaInf X v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[X.B.I.F] e = a • ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, trace_one_tmul, smul_eq_mul, map_mul, evInf_alg, emb_trace, ← h1, thetaInf_tmul, map_mul,
      evInf_conj]
    ring
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]; ring

theorem theta_sigR (v : InfinitePlace X.B.I.F) (t : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (sigR (Ainf X.B.I.F) X.B.I.cm.sig t) = conj (PI.AprimeInfU.thetaInf X v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : sigR (Ainf X.B.I.F) X.B.I.cm.sig (a ⊗ₜ[X.B.I.F] e) = a ⊗ₜ[X.B.I.F] (star e) := rfl
    rw [h, thetaInf_tmul, thetaInf_tmul, map_mul, evInf_conj, phi_star]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem theta_hR (v : InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (hR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y) =
      ∑ i, ∑ j, conj (PI.AprimeInfU.thetaInf X v (x i)) * X.B.I.φ v (X.B.I.J i j) *
        PI.AprimeInfU.thetaInf X v (y j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, theta_sigR, JR, Matrix.map_apply, thetaInf_inclR]

end Tr

section Form

theorem form_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj (p i) * M i j * q j = star p ⬝ᵥ (M *ᵥ q) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_P {n : ℕ} (P A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj ((P *ᵥ p) i) * A i j * (P *ᵥ q) j = ∑ i, ∑ j, conj (p i) * (Pᴴ * A * P) i j * q j := by
  rw [form_dot, form_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem form_Jm {n : ℕ} (ε : Fin n → Bool) (p q : Fin n → ℂ) :
    (∑ i, ∑ j, conj (p i) * Formalism.REAL.Jm ε i j * q j).re =
      ∑ i, (if ε i then 1 else -1 : ℝ) * ((p i).re * (q i).re + (p i).im * (q i).im) := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

end Form

section Beta

variable {D : D7} (X : HidaSetting D)

theorem theta_col (v : InfinitePlace X.B.I.F) (Y : TupI X) (b : Fin (D.R.rS + 1 + D.R.rS)) :
    (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) = X.B.I.P v *ᵥ fun i => betaV X v Y i b := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have : (fun i => betaV X v Y i b) = (X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y b j) := by
    funext i
    simp [betaV]
  rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]

theorem re_evInf_BR (v : InfinitePlace X.B.I.F) (Y Z : TupI X) :
    (PI.AprimeInfU.evInf X v (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y Z)).re =
      ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v Y i b).re * (betaV X v Z i b).re + (betaV X v Y i b).im * (betaV X v Z i b).im)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [BR, map_sum, Complex.re_sum, evInf_trace, Complex.add_re, Complex.conj_re]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [theta_hR]
  have e1 := theta_col X v Y b
  have e2 := theta_col X v Z b
  have hY : ∀ i, PI.AprimeInfU.thetaInf X v (Y b i) = (X.B.I.P v *ᵥ fun i => betaV X v Y i b) i :=
    fun i => congrFun e1 i
  have hZ : ∀ i, PI.AprimeInfU.thetaInf X v (Z b i) = (X.B.I.P v *ᵥ fun i => betaV X v Z i b) i :=
    fun i => congrFun e2 i
  simp only [hY, hZ]
  have hJ : ∀ i j, X.B.I.φ v (X.B.I.J i j) = (X.B.I.J.map (X.B.I.φ v)) i j := fun _ _ => rfl
  simp only [hJ]
  rw [form_P, X.B.I.P_spec v, form_Jm, ← two_mul, Finset.mul_sum]

theorem betaI_bridge (x y : EuclideanSpace ℝ (KapI X)) :
    betaI X x y = ∑ v, ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v ((tupCoord X).symm x) i b).re * (betaV X v ((tupCoord X).symm y) i b).re +
          (betaV X v ((tupCoord X).symm x) i b).im * (betaV X v ((tupCoord X).symm y) i b).im)) := by
  simp only [betaI]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact re_evInf_BR X v _ _

end Beta

end PI.AprimeInfW.MuB
end
end

noncomputable section

namespace PI.AprimeInfW.MuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

open Classical

variable {D : D7} (X : HidaSetting D)

abbrev BrI : Type := InfinitePlace X.B.I.F × Fin X.B.I.n × Fin (D.R.rS + 1 + D.R.rS) × Bool

theorem reimV_apply {V : Type} {n m : ℕ} (M : V → Matrix (Fin n) (Fin m) ℂ) (p : V × Fin n × Fin m × Bool) :
    reimV M p = if p.2.2.2 then (M p.1 p.2.1 p.2.2.1).re else (M p.1 p.2.1 p.2.2.1).im := rfl

theorem reimV_addB {V : Type} {n m : ℕ} (A B : V → Matrix (Fin n) (Fin m) ℂ) :
    reimV (A + B) = reimV A + reimV B := by
  ext p
  by_cases h : p.2.2.2 <;> simp [reimV, h]

def bAdd : EuclideanSpace ℝ (KapI X) →+ EuclideanSpace ℝ (BrI X) :=
  AddMonoidHom.mk' (fun x => reimV (fun v => betaV X v ((tupCoord X).symm x))) fun x y => by
    rw [← reimV_addB]
    congr 1
    funext v
    rw [tupCoord_symm_add, betaV_add]
    rfl

theorem continuous_betaV (v : InfinitePlace X.B.I.F) (i : Fin X.B.I.n) (b : Fin (D.R.rS + 1 + D.R.rS)) :
    Continuous fun Y : TupI X => betaV X v Y i b := by
  simp only [betaV, Matrix.of_apply, Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul
    ((continuous_thetaInf X v).comp ((continuous_apply j).comp (continuous_apply b)))

theorem continuous_bAdd : Continuous (bAdd X) := by
  show Continuous fun x => reimV (fun v => betaV X v ((tupCoord X).symm x))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  rcases p with ⟨v, i, b, s⟩
  cases s
  · exact Complex.continuous_im.comp ((continuous_betaV X v i b).comp (tupCoord X).symm.continuous)
  · exact Complex.continuous_re.comp ((continuous_betaV X v i b).comp (tupCoord X).symm.continuous)

def bL : EuclideanSpace ℝ (KapI X) →L[ℝ] EuclideanSpace ℝ (BrI X) :=
  (bAdd X).toRealLinearMap (continuous_bAdd X)

theorem bL_apply (x : EuclideanSpace ℝ (KapI X)) : bL X x = reimV (fun v => betaV X v ((tupCoord X).symm x)) :=
  rfl

def qD (p : BrI X) : ℝ := 2 * (if X.B.I.ε p.1 p.2.1 then 1 else -1)

theorem betaI_q (x y : EuclideanSpace ℝ (KapI X)) : betaI X x y = ∑ p : BrI X, qD X p * bL X x p * bL X y p := by
  rw [betaI_bridge]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, bL_apply, reimV_apply, qD, if_true, Bool.false_eq_true,
    if_false]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem card_cbi : Fintype.card
    (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [← Module.finrank_eq_card_chooseBasisIndex, Module.finrank_baseChange, X.B.I.cm.deg2]

theorem card_BrI : Fintype.card (BrI X) = Fintype.card (KapI X) := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, card_cbi]
  ring

def eI : BrI X ≃ KapI X := Fintype.equivOfCardEq (card_BrI X)

def U : EuclideanSpace ℝ (BrI X) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (KapI X) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (eI X)

def fK : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  (U X).toLinearEquiv.toLinearMap ∘ₗ (bL X).toLinearMap

theorem fK_apply (x : EuclideanSpace ℝ (KapI X)) (k : KapI X) : fK X x k = bL X x ((eI X).symm k) := by
  simp [fK, U, Equiv.piCongrLeft'_apply]


open Classical in
def Bq : Matrix (KapI X) (KapI X) ℝ := fun k l => bL X (EuclideanSpace.single l 1) ((eI X).symm k)

open Classical in
theorem toMatrix_fK : LinearMap.toMatrix (EuclideanSpace.basisFun (KapI X) ℝ).toBasis
    (EuclideanSpace.basisFun (KapI X) ℝ).toBasis (fK X) = Bq X := by
  ext k l
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, fK_apply]
  rfl

theorem det_fK : LinearMap.det (fK X) = (Bq X).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (KapI X) ℝ).toBasis, toMatrix_fK]

open Classical in
theorem matI_eq : matI X = (Bq X)ᵀ * Matrix.diagonal (fun k => qD X ((eI X).symm k)) * Bq X := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  show betaI X _ _ = _
  rw [betaI_q, ← (eI X).symm.sum_comp]
  refine Finset.sum_congr rfl fun k' _ => ?_
  simp only [Bq]
  ring

theorem det_matI : (matI X).det = (Bq X).det ^ 2 * ∏ p : BrI X, qD X p := by
  rw [matI_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    (eI X).symm.prod_comp (fun p => qD X p)]
  ring

theorem abs_prod_qD : |∏ p : BrI X, qD X p| =
    ((2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F))) ^ 2 := by
  rw [Finset.abs_prod]
  have h : ∀ p : BrI X, |qD X p| = 2 := by
    intro p
    unfold qD
    split_ifs <;> norm_num
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul]
  congr 1
  ring

theorem sqrt_matI (hd : (matI X).det ≠ 0) :
    (Bq X).det ≠ 0 ∧ Real.sqrt |(matI X).det| =
      |(Bq X).det| * 2 ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F)) := by
  have hdm := det_matI X
  refine ⟨fun h0 => hd (by rw [hdm, h0]; ring), ?_⟩
  rw [hdm, abs_mul, abs_prod_qD, abs_pow, sq_abs]
  have hnn : 0 ≤ |(Bq X).det| * (2 : ℝ) ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F)) :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _)
  rw [← Real.sqrt_sq hnn, mul_pow, sq_abs]

end PI.AprimeInfW.MuB

namespace PI.AprimeInfW

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets
open Classical

theorem muBridge_holds : MuBridge := by
  intro D X u' ψ hT μinf νinf fibInf hP
  have hd : (matI X).det ≠ 0 := matNDH_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨hB0, hsq⟩ := MuB.sqrt_matI X hd
  have hfd : LinearMap.det (MuB.fK X) ≠ 0 := by rw [MuB.det_fK]; exact hB0
  have hfun : (fun Y => reimV (fun v => betaV X v Y)) = (MuB.U X).symm ∘ (MuB.fK X) ∘ (tupCoord X) := by
    funext Y
    simp [MuB.fK, MuB.bL_apply]
  have hUm : Measurable (MuB.U X).symm := (MuB.U X).symm.continuous.measurable
  have hfKm : Measurable (MuB.fK X) := (LinearMap.continuous_of_finiteDimensional (MuB.fK X)).measurable
  have htm : Measurable (tupCoord X) := (tupCoord X).continuous.measurable
  have e1 : μinf.map ((MuB.U X).symm ∘ (MuB.fK X) ∘ (tupCoord X)) =
      ((μinf.map (tupCoord X)).map (MuB.fK X)).map (MuB.U X).symm := by
    rw [Measure.map_map hUm hfKm, Measure.map_map (hUm.comp hfKm) htm]
    rfl
  rw [hfun, e1, densMu_holds X u' ψ hT μinf νinf fibInf hP, Measure.map_smul,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hfd, Measure.map_smul, Measure.map_smul,
    ((MuB.U X).symm.measurePreserving).map_eq, smul_smul, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hsq,
    MuB.det_fK]
  congr 2
  have ha : |(MuB.Bq X).det| ≠ 0 := abs_ne_zero.2 hB0
  rw [abs_inv]
  field_simp
  all_goals first | exact hUm.aemeasurable | exact hfKm.aemeasurable

theorem betaIso_holds : BetaIso := by
  intro D X
  have hinj : Function.Injective (MuB.fK X) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hb : MuB.bL X x = 0 := by
      have := congrArg (MuB.U X).symm hx
      simpa [MuB.fK] using this
    have hβ : ∀ v, betaV X v ((tupCoord X).symm x) = betaV X v 0 := by
      intro v
      have h0 : betaV X v 0 = 0 := by
        have := betaV_add X v 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      rw [h0]
      ext i b
      have hre := congrArg (fun z : EuclideanSpace ℝ (MuB.BrI X) => z (v, i, b, true)) hb
      have him := congrArg (fun z : EuclideanSpace ℝ (MuB.BrI X) => z (v, i, b, false)) hb
      simp only [MuB.bL_apply, MuB.reimV_apply, if_true, Bool.false_eq_true, if_false] at hre him
      exact Complex.ext (by simpa using hre) (by simpa using him)
    have h1 := betaV_inj X _ _ hβ
    have h2 : tupCoord X 0 = 0 := by
      have := tupCoord_add X 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [← (tupCoord X).apply_symm_apply x, h1, h2]
  have hsurj : Function.Surjective (MuB.fK X) := LinearMap.injective_iff_surjective.1 hinj
  let eF := LinearEquiv.ofBijective (MuB.fK X) ⟨hinj, hsurj⟩
  refine ⟨(eF.trans (MuB.U X).symm.toLinearEquiv).toContinuousLinearEquiv, fun Y => ?_⟩
  show (MuB.U X).symm (MuB.fK X (tupCoord X Y)) = _
  simp [MuB.fK, MuB.bL_apply]

end PI.AprimeInfW
