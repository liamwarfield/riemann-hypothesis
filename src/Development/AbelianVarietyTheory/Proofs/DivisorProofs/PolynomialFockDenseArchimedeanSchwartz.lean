module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussVacuumNondegenerateGaussianDualPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveComplexStructureDarbouxPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSympNegOne
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

theorem trace_symp_neg_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
      (u v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) u v)) =
        ∑ w, -2 * (∑ i, ∑ j, ∑ k, ∑ l, piInf (τ w) (u i j) * (τ w).1 (JX i k) * (τ w).1 (JW j l) *
          star (piInf (τ w) (v k l))).re := by
  intro F E _ _ _ _ _ σ hCM τ n d JX JW u v
  haveI : IsTotallyReal F := hCM.1
  rw [trace_rho]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [symp, rho_trace hCM (τ w)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_neg, map_one, hTens, map_sum, incM, Matrix.map_apply, piInf_inclR,
    GlobalTheory.WrongSignPair.piInf_cA hCM, neg_one_mul, Complex.neg_re]
  ring
end GlobalTheory.ThK.EvAt0.PlaneQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCartanInvolutionInvariantAndPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCartanInvolutionInvariantAndPositive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.CartanTensor

open Matrix
open scoped Kronecker ComplexOrder

variable {n d : ℕ}

theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

theorem cartan_comm {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M * θ.map star = θᵀ * M := by
  obtain ⟨h1, h2, -⟩ := h
  have h1' : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1]
    exact Matrix.map_one star (star_zero _) (star_one _)
  calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [h2]
    _ = θᵀ * M := by rw [Matrix.mul_assoc (θᵀ * M), h1', Matrix.mul_one]

theorem cartan_posDef {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) :
    (θᵀ * M).PosDef := by
  have hH : (θᵀ * M).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, ← cartan_comm h]
    congr 1 <;> ext i j <;> simp [hM]
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun c hc => Complex.pos_iff.2 ⟨?_, (hH.im_star_dotProduct_mulVec_self c).symm⟩⟩
  have hx : star c ≠ 0 := by simpa using hc
  have := h.2.2 (star c) hx
  rw [star_star] at this
  convert this using 2
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem quadruple_sum_eq_trace_transpose_mul (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * A i k * B j l * star (y k l)) = trace (xᵀ * (A * y.map star * Bᵀ)) := by
  rw [← trace_transpose_mul, transpose_transpose]
  simp only [trace, diag_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadruple_sum_eq_kronecker_quadraticForm (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) (x : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * P i k * Q j l * star (x k l)) =
      star (fun p : Fin n × Fin d => star (x p.1 p.2)) ⬝ᵥ ((P ⊗ₖ Q) *ᵥ fun p : Fin n × Fin d => star (x p.1 p.2)) := by
  simp only [dotProduct, mulVec, kronecker_apply, Fintype.sum_prod_type, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem map_star_smulI {a b : Type} (M : Matrix a b ℂ) : (Complex.I • M).map star = (-Complex.I) • M.map star := by
  ext i j; simp

theorem cancelI {A B : Matrix (Fin d) (Fin d) ℂ} (h : Complex.I • A = Complex.I • B) : A = B :=
  smul_right_injective _ Complex.I_ne_zero h

theorem tensor_cartan_invariant_pos : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  intro n d JX θX JW θW hJX hX hJW hW x y
  have hWc : θWᵀ * JW * θW.map star = JW := by
    have h := hW.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cW : JW * θW.map star = θWᵀ * JW := by
    have h := cartan_comm hW
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cX := cartan_comm hX
  have hIW : ∀ i j, star ((Complex.I • JW) j i) = (Complex.I • JW) i j := by
    intro i j; simp [hJW]
  constructor
  · rw [quadruple_sum_eq_trace_transpose_mul, quadruple_sum_eq_trace_transpose_mul]
    have e1 : (Complex.I • (θX * x * θWᵀ))ᵀ * (JX * (Complex.I • (θX * y * θWᵀ)).map star * JWᵀ) =
        θW * (xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ) := by
      rw [map_star_smulI, transpose_smul, map_star_mul, map_star_mul, transpose_mul, transpose_mul, transpose_transpose,
        transpose_map]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_mul]
    have e2 : xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ * θW =
        xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θWᵀ * JW * θW.map star)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e1, trace_mul_comm, e2, hX.2.1, hWc]
    simp only [Matrix.mul_assoc]
  · intro hx
    have e3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
        -(xᵀ * ((θXᵀ * JX) * x.map star * (θWᵀ * (Complex.I • JW))ᵀ)) := by
      have h3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
          (-Complex.I) • (xᵀ * (JX * θX.map star) * x.map star * (JW * θW.map star)ᵀ) := by
        rw [map_star_smulI, map_star_mul, map_star_mul, transpose_map, transpose_mul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      rw [h3, cX, cW]
      simp only [Matrix.smul_mul, Matrix.mul_smul, transpose_smul, neg_smul, Matrix.mul_assoc]
    rw [quadruple_sum_eq_trace_transpose_mul, e3, trace_neg, Complex.neg_re, neg_neg,
      ← quadruple_sum_eq_trace_transpose_mul (θXᵀ * JX) (θWᵀ * (Complex.I • JW)) x x, quadruple_sum_eq_kronecker_quadraticForm]
    have hK := (cartan_posDef hJX hX).kronecker (cartan_posDef hIW hW)
    have hc : (fun p : Fin n × Fin d => star (x p.1 p.2)) ≠ 0 := by
      intro h; apply hx; ext i j; have := congrFun h (i, j); simpa using this
    exact (Complex.pos_iff.1 ((posDef_iff_dotProduct_mulVec.1 hK).2 hc)).1

end GlobalTheory.CartanTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCartanInvolutionInvariantAndPositiveStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorCartanInvolution_invariant_and_positive : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  first | exact @GlobalTheory.CartanTensor.tensor_cartan_invariant_pos | exact GlobalTheory.CartanTensor.tensor_cartan_invariant_pos | (intros; apply GlobalTheory.CartanTensor.tensor_cartan_invariant_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveComplexStructureDarbouxPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussFockPair

open GlobalTheory.GaussFockJ

def tensC {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)

theorem tensC_zero_left {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (y : Matrix (Fin n) (Fin d) ℂ) :
    tensC JX JW 0 y = 0 := by
  simp [tensC]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pair_Psi {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M u).1 (Psi M v).2 -
                 GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M v).1 (Psi M u).2 =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) u v)) := by
  have hform := M.co.form u v
  simp only [cA, incM] at hform
  rw [hform, ← evIHom_apply, map_sub, map_sub]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.GaussLine.pairInf_apply, Psi, EvAt0.PolD.arc, dotProduct, map_sum, map_mul, evIHom_apply]

theorem exists_pos_complex_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  choose R hRat hRmap using fun u : Matrix (Fin n) (Fin d) (AE F E) =>
    exists_mat_at hcm B.emb (fun w => Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ))
  have hRadd : ∀ u v, R (u + v) = R u + R v := by
    intro u v
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero])
      fun w => ?_
    rw [hRmap, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hRmap, hRmap]
    simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
  have hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u := by
    intro c u
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero])
      fun w => ?_
    rw [hRmap, map_smul_piInf, map_smul_piInf, hRmap]
    simp only [ Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  have hRR : ∀ u, At (evI F) u → R (R u) = -u := by
    intro u hu
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_
    rw [hRmap, Matrix.map_neg _ (map_neg _), hRmap]
    have hV := (hP.herm.cartan w).1
    have hW := (hP.skew.cartan w).1
    have hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]

  have hXh : ∀ w, ∀ i j, star (X.J.map (B.emb w).1 j i) = X.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.herm.herm]
  have hWs : ∀ w, ∀ i j, star (W.J.map (B.emb w).1 j i) = -W.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.skew.skew, map_neg]
  have hloc := fun w => GlobalTheory.T.tensorCartanInvolution_invariant_and_positive n d (X.J.map (B.emb w).1) (X.θ w) (W.J.map (B.emb w).1) (W.θ w) (hXh w)
    (hP.herm.cartan w) (hWs w) (hP.skew.cartan w)
  have key : ∀ a b : Matrix (Fin n) (Fin d) (AE F E),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) a b)) =
        ∑ w, -2 * (tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
          (b.map (piInf (B.emb w)))).re := by
    intro a b
    have ht := GlobalTheory.ThK.EvAt0.PlaneQ.trace_symp_neg_one F E σ hcm B.emb n d X.J W.J a b
    simp only [cA, incM] at ht
    rw [ht]
    rfl
  have hinv : ∀ a b w, tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((R a).map (piInf (B.emb w)))
      ((R b).map (piInf (B.emb w))) = tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
      (b.map (piInf (B.emb w))) := by
    intro a b w
    rw [hRmap, hRmap]
    exact (hloc w _ _).1
  have hpos : ∀ a w, a.map (piInf (B.emb w)) ≠ 0 → 0 < -(tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1)
      (a.map (piInf (B.emb w))) ((R a).map (piInf (B.emb w)))).re := by
    intro a w ha
    rw [hRmap]
    exact (hloc w _ (a.map (piInf (B.emb w)))).2 ha
  let J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    fun w => Psi M (R (Phi M w))
  have hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v := by
    intro t v hv
    rw [← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]
  let J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { toFun := J
      map_add' := fun w w' => by
        show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))
        rw [Phi_add, hRadd, Psi_add]
      map_smul' := fun t w => by
        show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))
        rw [Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }
  have hPsi0 : Psi M (0 : Matrix (Fin n) (Fin d) (AE F E)) = 0 := by
    have h := Psi_add M (0 : Matrix (Fin n) (Fin d) (AE F E)) 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  refine ⟨J₀, fun w => ?_, fun w w' => ?_, fun w hw => ?_, fun u u' hu hu' hmap => ?_⟩
  · show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w
    rw [Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]
  · show GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 (Psi M (R (Phi M w'))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w'))).1 (Psi M (R (Phi M w))).2 = _
    conv_rhs => rw [← Psi_Phi M w, ← Psi_Phi M w']
    rw [pair_Psi, pair_Psi, key, key]
    exact Finset.sum_congr rfl fun v _ => by rw [hinv]
  · have hw' := Psi_Phi M w
    have hat := at_Phi M w
    show 0 < GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) w.1 (Psi M (R (Phi M w))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 w.2
    generalize Phi M w = a at hw' hat ⊢
    subst hw'
    rw [pair_Psi, key]
    have hex : ∃ v, a.map (piInf (B.emb v)) ≠ 0 := by
      by_contra hn
      push_neg at hn
      have ha0 : a = 0 := eq_of_map_piInf hcm B.emb hat (fun c _ => smul_zero c)
        fun v => by rw [hn v, Matrix.map_zero _ (map_zero _)]
      exact hw (by rw [ha0, hPsi0])
    obtain ⟨v, hv⟩ := hex
    refine Finset.sum_pos' (fun v' _ => ?_) ⟨v, Finset.mem_univ _, by have := hpos a v hv; linarith⟩
    by_cases h0 : a.map (piInf (B.emb v')) = 0
    · rw [h0, tensC_zero_left, Complex.zero_re, mul_zero]
    · have := hpos a v' h0; linarith
  · change Psi M u' = Psi M (R (Phi M (Psi M u)))
    rw [Phi_Psi M hu]
    congr 1
    exact eq_of_map_piInf hcm B.emb hu' (hRat u) fun w => by rw [hmap, hRmap]

end GlobalTheory.GaussFockPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveComplexStructureDarbouxPairStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_complex_structure_darboux_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  first | exact @GlobalTheory.GaussFockPair.exists_pos_complex_structure | exact GlobalTheory.GaussFockPair.exists_pos_complex_structure | (intros; apply GlobalTheory.GaussFockPair.exists_pos_complex_structure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFockFormOfComplexStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFockFormOfComplexStructure
open scoped Matrix

namespace GlobalTheory

theorem siegel_fock_exists : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  intro V _ _ _ β J hsym hJJ hJ hpos
  set Φ : (V × V) →ₗ[ℝ] (V × V) :=
    LinearMap.inr ℝ V V ∘ₗ LinearMap.fst ℝ V V + J ∘ₗ LinearMap.inr ℝ V V ∘ₗ LinearMap.snd ℝ V V with hΦdef
  have hΦ : ∀ u : V × V, Φ u = (0, u.1) + J (0, u.2) := by
    intro u; simp [hΦdef]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hΦ] at hu
    have h1 : (J (0, u.2)).1 = 0 := by
      have := congrArg Prod.fst hu; simpa using this
    have hb : u.2 = 0 := by
      by_contra hne
      have := hpos (0, u.2) (by simpa using hne)
      simp [h1] at this
    have hJ0 : J (0, 0) = 0 := J.map_zero
    have ha : u.1 = 0 := by
      have := congrArg Prod.snd hu; simpa [hb, hJ0] using this
    exact Prod.ext ha hb
  set E := LinearEquiv.ofInjectiveEndo Φ hinj with hEdef
  have hE : ∀ w, Φ (E.symm w) = w := fun w => by
    show E (E.symm w) = w
    exact E.apply_symm_apply w
  have hJ0 : J (0, 0) = 0 := J.map_zero
  set A : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hAdef
  set B : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hBdef
  have hAB : ∀ p, E.symm (p, 0) = (A p, B p) := fun p => by simp [hAdef, hBdef]
  have hP0 : ∀ q, E.symm (0, q) = (q, 0) := fun q => by
    apply E.injective
    rw [E.apply_symm_apply]
    show (0, q) = Φ (q, 0)
    rw [hΦ]; simp [hJ0]
  have hsplit : ∀ w : V × V, E.symm w = (A w.1 + w.2, B w.1) := fun w => by
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    rw [hw, map_add (f := _), hAB, hP0]; simp
  have hJB : ∀ p, J (0, B p) = (p, -A p) := fun p => by
    have := hE (p, 0)
    rw [hAB, hΦ] at this
    have h2 : J (0, B p) = (p, 0) - (0, A p) := by rw [← this]; abel
    rw [h2]; simp
  have hPJ : ∀ w : V × V, E.symm (J w) = (-(E.symm w).2, (E.symm w).1) := fun w => by
    apply E.injective
    rw [E.apply_symm_apply]
    show J w = Φ _
    conv_lhs => rw [← hE w]
    rw [hΦ, hΦ, map_add (f := _), hJJ]
    ext <;> simp <;> abel
  have hAsym : ∀ x y, β x (A y) = β y (A x) := fun x y => by
    have := hJ (0, B x) (0, B y)
    rw [hJB, hJB] at this
    simp at this
    linarith
  have hBsym : ∀ x y, β x (B y) = β y (B x) := fun x y => by
    have := hJ (J (0, B x)) (0, B y)
    rw [hJJ, hJB, hJB] at this
    simp at this
    linarith
  have hBpos : ∀ x, x ≠ 0 → 0 < -β x (B x) := fun x hx => by
    have hne : ((0 : V), B x) ≠ 0 := by
      intro h0
      have h1 : J (0, B x) = 0 := by rw [h0]; exact J.map_zero
      rw [hJB] at h1
      exact hx (congrArg Prod.fst h1)
    have := hpos (0, B x) hne
    rw [hJB] at this
    simpa using this
  let Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ))
    (fun m₁ m₂ n => by simp; ring)
    (fun c m n => by simp; ring)
    (fun m n₁ n₂ => by simp; ring)
    (fun c m n => by simp; ring)
  let Q : V →L[ℝ] V →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q')
  have hQ : ∀ x y, Q x y = ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ) :=
    fun x y => rfl
  have hre : ∀ x, (Q x x).re = Real.pi * -β x (B x) := fun x => by
    rw [hQ]; simp
  have hscale : ∀ (t : ℝ) (y : V), Real.pi * -β (t • y) (B (t • y)) = t ^ 2 * (Real.pi * -β y (B y)) :=
    fun t y => by simp; ring
  have hcont : Continuous fun x => (Q x x).re := by fun_prop
  have hsym' : ∀ x y, Q x y = Q y x := fun x y => by rw [hQ, hQ, hAsym x y, hBsym x y]
  have hfock : ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) =
      Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := fun w x => by
    have e1 := hsplit (J w)
    rw [hPJ, hsplit w] at e1
    have h1 : A (J w).1 + (J w).2 = -(B w.1) := (congrArg Prod.fst e1).symm
    have h2 : B (J w).1 = A w.1 + w.2 := (congrArg Prod.snd e1).symm
    have hb1 : β x (A (J w).1) = -β x (B w.1) - β x (J w).2 := by
      have := congrArg (β x) h1; simp at this; linarith
    have hb2 : β x (B (J w).1) = β x (A w.1) + β x w.2 := by rw [h2]; simp
    rw [hQ, hQ, hb1, hb2]
    push_cast
    linear_combination (-((Real.pi : ℂ) * (β x (A w.1) : ℂ) + (Real.pi : ℂ) * (β x w.2 : ℂ))) * Complex.I_sq
  by_cases hs : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hs hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨Q, (Q u u).re, ?_, ?_, hsym', hfock⟩
    · rw [hre]; exact mul_pos Real.pi_pos (hBpos u hu0)
    · intro x
      by_cases hx : x = 0
      · subst hx; simp
      · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hu' : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
        have hm : (Q u u).re ≤ (Q (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := hmin hu'
        have key : Real.pi * -β x (B x) = ‖x‖ ^ 2 * (Real.pi * -β (‖x‖⁻¹ • x) (B (‖x‖⁻¹ • x))) := by
          rw [hscale]; field_simp
        rw [hre, hre] at hm
        rw [hre u, hre x, key]
        have := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖x‖)
        linarith
  · refine ⟨Q, 1, one_pos, ?_, hsym', hfock⟩
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      apply hs
      refine ⟨‖x‖⁻¹ • x, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFockFormOfComplexStructureStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_fock_form_of_complex_structure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  first | exact @GlobalTheory.siegel_fock_exists | exact GlobalTheory.siegel_fock_exists | (intros; apply GlobalTheory.siegel_fock_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussVacuumNondegenerateGaussianDualPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.GaussVacPair
open GlobalTheory.GaussFockJ GlobalTheory.ThK.EvAt0.PolD

theorem actsD_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}
    (h1 : ActsD (evI F) T f f₁) (h2 : ActsD (evI F) T f f₂) : f₁ = f₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) κ
  ext y
  have hr := hR f
  let x : κ → AF F := fun i => liftA (y i)
  have hx : At (evI F) x := fun c hc => funext fun i => smul_liftA hc (y i)
  have e := (h1 R hr x).unique (h2 R hr x)
  have hRx : R x = R 0 := by
    have := hr.1 0 x hx
    rwa [zero_add] at this
  have hl : (fun i => evI F (x i)) = y := funext fun i => evI_liftA (y i)
  simp only [tens, hl, hRx] at e
  exact mul_right_cancel₀ hR0 e

theorem exists_gauss_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨J₀, hJJ, hJω, hJpos, hJrel⟩ := GlobalTheory.T.exists_positive_complex_structure_darboux_pair F E σ B n d X W M χX χW om r s r' s' hP
  have hsym : ∀ x y : (Fin n × Fin d → mixedEmbedding.mixedSpace F), GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x y = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) y x := by
    intro x y
    simp only [GlobalTheory.GaussLine.pairInf_apply, mul_comm]
  obtain ⟨Q, c, hc, hQc, hQs, hQJ⟩ := GlobalTheory.T.exists_siegel_fock_form_of_complex_structure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) J₀ hsym hJJ hJω hJpos
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.T.exists_schwartz_eq_cexp_neg_form (Fin n × Fin d → mixedEmbedding.mixedSpace F) Q c hc hQc
  refine ⟨g, ⟨fun _ => 1, ?_⟩, Q, c, hc, hQc, hg⟩
  intro u u' hu hu' hrel f f' hf hf'
  have hrel' : ∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    rw [hrel w]
    simp
  have key : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) v → ∀ h : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ v) g h → ∀ x, h x = GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (Psi M v) g x := by
    intro v hv h hh x
    have h0 := actsD_Phi hψ M (Psi M v) g
    rw [Phi_Psi M hv] at h0
    rw [actsD_unique hh h0, dHeis_eq_dOp]
  have hJ : Psi M u' = J₀ (Psi M u) := hJrel u u' hu hu' hrel'
  have hd : ∀ (w : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w g x =
      -2 * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x w.2 : ℂ)) * g x := by
    intro w x
    rw [GlobalTheory.GaussLine.dHeis, hgd x w.1, hQs w.1 x]
    ring
  ext x
  rw [SchwartzMap.smul_apply, key u' hu' f' hf' x, key u hu f hf x, hJ, hd, hd, hQJ, smul_eq_mul]
  ring

end GlobalTheory.GaussVacPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussVacuumNondegenerateGaussianDualPairStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussVacuum_nondegenerate_gaussian_dualPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  first | exact @GlobalTheory.GaussVacPair.exists_gauss_vacuum | exact GlobalTheory.GaussVacPair.exists_gauss_vacuum | (intros; apply GlobalTheory.GaussVacPair.exists_gauss_vacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNondegenerate
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem mixedTracePairing_nondegenerate_left {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, trP F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same] at this

theorem mixedTracePairing_nondegenerate_right {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F) (hy : ∀ x, trP F κ x y = 0) : y = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hy (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this

theorem mixedTracePairing_nondegenerate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (trP F κ).Nondegenerate := by
  intro F _ _ κ _
  refine ⟨fun x hx => mixedTracePairing_nondegenerate_left (F := F) (κ := κ) x hx, fun y hy => mixedTracePairing_nondegenerate_right (F := F) (κ := κ) y hy⟩

end GlobalTheory.ArchSch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolDense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem mem_pol_of_isGauss (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) : f₀ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h

theorem mem_pol_of_actsD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h


open scoped Classical in
theorem pol_stable (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (v a : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h₁ : ∀ y, f₁ y = fderiv ℝ (⇑f) y v - 2 * Real.pi * Complex.I * (GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a : ℂ) * f y) :
    f₁ ∈ M.Pol ψ τ := by
  obtain ⟨u, hu, hD⟩ := GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq M ψ hψ (v, a)
  obtain ⟨D, hDa⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
  have e : D f = f₁ := by
    refine SchwartzMap.ext fun y => ?_
    rw [hD f (D f) (hDa f) y, h₁ y]
  exact e ▸ mem_pol_of_actsD M ψ τ hu hf (hDa f)


open scoped Classical in
theorem pol_dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨g, hg, Q, c, hc, hQ, hgQ⟩ := GlobalTheory.T.exists_gaussVacuum_nondegenerate_gaussian_dualPair F E σ B n d X W M χX χW om r s r' s' hP
  refine GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable _ _ g Q c hc hQ hgQ (mem_pol_of_isGauss M B.ψ B.emb hg) ?_ ?_
  · intro v f f₁ hf h₁
    refine pol_stable M B.ψ hψ B.emb v 0 hf fun y => ?_
    rw [h₁ y]
    simp [GlobalTheory.ArchUniq.trP]
  · intro ℓ f f₁ hf h₁
    have hnd := GlobalTheory.ArchSch.mixedTracePairing_nondegenerate F (Fin n × Fin d)
    obtain ⟨a, ha⟩ : ∃ a, ∀ y, GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a = ℓ y := by
      let e := (GlobalTheory.ArchSch.trP F (Fin n × Fin d)).flip.toDual hnd.flip
      refine ⟨e.symm ℓ.toLinearMap, fun y => ?_⟩
      calc GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y (e.symm ℓ.toLinearMap) = e (e.symm ℓ.toLinearMap) y := by
            simp only [e, LinearMap.BilinForm.toDual_def]; rfl
        _ = ℓ y := by rw [e.apply_symm_apply]; rfl
    have hmem : (-(2 * Real.pi * Complex.I)) • f₁ ∈ M.Pol B.ψ B.emb := by
      refine pol_stable M B.ψ hψ B.emb 0 a hf fun y => ?_
      simp [h₁ y, ha y]
      ring
    have hne : (-(2 * Real.pi * Complex.I)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := (M.Pol B.ψ B.emb).smul_mem (-(2 * Real.pi * Complex.I))⁻¹ hmem
    rwa [inv_smul_smul₀ hne] at this

end GlobalTheory.PolDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartzStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  first | exact @GlobalTheory.PolDense.pol_dense | exact GlobalTheory.PolDense.pol_dense | (intros; apply GlobalTheory.PolDense.pol_dense <;> assumption)
end
