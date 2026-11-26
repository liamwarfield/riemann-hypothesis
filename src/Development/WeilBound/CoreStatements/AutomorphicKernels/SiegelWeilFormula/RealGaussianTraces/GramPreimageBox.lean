module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.SecondCountableTens
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCJ

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.TraceReOfHerm
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.PsiNegTrPairGen
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.TraceAdd
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (y : E) : σ (σ y) = y := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2, hCM.2.2.2, star_star]

theorem sig_nt (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra h
  push Not at h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc := hCM.2.1.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  apply hc
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq]
  have := hCM.2.2.2 τ x
  rw [h x] at this
  exact this.symm

theorem trace_add (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (z : Ainf F ⊗[F] E) :
    algebraMap (Ainf F) (Ainf F ⊗[F] E) (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) = z + sigR (Ainf F) σ z := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
  exact Formalism.L2.Fam.ThC.alg_trace_gen σ
    (PI.OmLocU.SdB.trace_eq_add σ (sig_sig σ hCM) (sig_nt σ hCM) hCM.2.2.1) z

end PositivityTheory.SiegelWeilFormula.GReal
end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem th_half (θ : Ainf F ⊗[F] E →+* ℂ) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
  rw [← IsScalarTower.algebraMap_apply]
  have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  exact this

theorem th_trPair (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (trPair (Ainf F) S G)) = (((S.map θ * G.map θ).trace.re : ℝ) : ℂ) := by
  rw [trPair, map_mul, map_mul, th_half, trace_add σ hCM, map_add (f := _), hc]
  have e : θ (∑ a, ∑ c, S a c * G c a) = (S.map θ * G.map θ).trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, Matrix.mul_apply, map_sum, map_mul]
  rw [e, Complex.star_def, Complex.add_conj]
  push_cast
  ring

theorem tmul_one_eq (x : Ainf F) : (x ⊗ₜ[F] (1 : E)) = algebraMap (Ainf F) (Ainf F ⊗[F] E) x := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem psi_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ)) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, th_trPair σ hCM (θ i) (hP.conj i)]

theorem psi_neg_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (-trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (-(((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ))) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, map_neg, map_neg, th_trPair σ hCM (θ i) (hP.conj i)]

theorem map_isHerm (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (b : HermR (Ainf F) σ n) :
    ((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map θ).IsHermitian := by
  ext a c
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← hc]
  exact congrArg θ (b.2 a c)

theorem gramX_eq {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) :
    gramX ε x = xᴴ * Matrix.diagonal (sgn ε) * x := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, sgn]
  simp only [Finset.sum_filter, if_true, Bool.false_eq_true, if_false]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

theorem gramX_isHerm {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) : (gramX ε x).IsHermitian := by
  rw [gramX_eq, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  have hs : star (sgn ε) = sgn ε := by
    funext a
    simp only [Pi.star_apply, sgn]
    split_ifs <;> simp
  rw [hs]

end PositivityTheory.SiegelWeilFormula.GReal
end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_gramR (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    (gramR (Ainf F) σ J Y).map θ =
      (Matrix.of fun a j => θ (Y j a))ᴴ * (JR (Ainf F) J).map θ * Matrix.of fun a j => θ (Y j a) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramR, hR, hform, map_sum, map_mul, hc, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem of_eq_crd {M n : ℕ} (θ : Ainf F ⊗[F] E →+* ℂ) (fr : GL (Fin M) ℂ) (g : GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    (Matrix.of fun a j => θ (Y j a)) = fr.1 * crd θ fr g Y * (g⁻¹).1 := by
  simp only [crd, ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem map_gramR_crd (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) (i : ι) :
    (gramR (Ainf F) σ J Y).map (θ i) = (((g i)⁻¹).1)ᴴ * gramX (ε i) (crdAll θ fr g Y i) * ((g i)⁻¹).1 := by
  rw [map_gramR σ (θ i) (hP.conj i), of_eq_crd (θ i) (fr i) (g i)]
  have hg : gramX (ε i) (crdAll θ fr g Y i) =
      (crd (θ i) (fr i) (g i) Y)ᴴ * Matrix.diagonal (sgn (ε i)) * crd (θ i) (fr i) (g i) Y := gramX_eq _ _
  rw [hg, ← hfr i]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem trace_herm_mul {n : ℕ} (β y : WR.E n) :
    (herm β * herm y).trace = ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
  have key : ∀ i j, herm β i j * herm y j i + herm β j i * herm y i j =
      ((β i j : ℝ) : ℂ) * ((y i j : ℝ) : ℂ) + ((β j i : ℝ) : ℂ) * ((y j i : ℝ) : ℂ) := by
    intro i j
    apply Complex.ext <;> simp [herm] <;> ring
  have h2 : (2 : ℂ) * (herm β * herm y).trace = 2 * ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
    have e1 : (herm β * herm y).trace = ∑ i, ∑ j, herm β i j * herm y j i := by
      simp [Matrix.trace, Matrix.mul_apply]
    have e2 : (2 : ℂ) * ∑ i, ∑ j, herm β i j * herm y j i =
        ∑ i, ∑ j, (herm β i j * herm y j i + herm β j i * herm y i j) := by
      rw [two_mul]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    have e3 : (2 : ℂ) * ∑ a, ∑ b, ((β a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) =
        ∑ i, ∑ j, (((β i j : ℝ) : ℂ) * ((y i j : ℝ) : ℂ) + ((β j i : ℝ) : ℂ) * ((y j i : ℝ) : ℂ)) := by
      rw [two_mul]
      conv_lhs => arg 2; rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    rw [e1, e2, e3]
    simp only [key]
  exact mul_left_cancel₀ two_ne_zero h2

theorem trace_re_of_herm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((((A * B).trace).re : ℝ) : ℂ) = (A * B).trace := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace _) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]

theorem herm_ybAll (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) (i : ι) :
    herm (ybAll σ θ g b i) =
      ((g i)⁻¹).1 * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ :=
  herm_hinv _ (Matrix.isHermitian_mul_mul_conjTranspose _ (map_isHerm σ (θ i) (hP.conj i) b))

theorem herm_ygAll (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) (i : ι) :
    herm (ygAll σ θ g b i) =
      ((g i).1)ᴴ * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1 :=
  herm_hinv _ (Matrix.isHermitian_conjTranspose_mul_mul _ (map_isHerm σ (θ i) (hP.conj i) b))

end PositivityTheory.SiegelWeilFormula.GReal
end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tr4 {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ) : (B * (C * D * A)).trace = (A * B * C * D).trace := by
  rw [show A * B * C * D = A * (B * C * D) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm A]
  simp only [Matrix.mul_assoc]

theorem gl_mul_inv {n : ℕ} (g : GL (Fin n) ℂ) : g.1 * (g⁻¹).1 = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem gl_inv_mul {n : ℕ} (g : GL (Fin n) ℂ) : (g⁻¹).1 * g.1 = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem gl_conj_cancel {n : ℕ} (g : GL (Fin n) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) :
    (g.1)ᴴ * ((((g⁻¹).1)ᴴ * Q * (g⁻¹).1)) * g.1 = Q := by
  have h1 : (g.1)ᴴ * ((g⁻¹).1)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, gl_inv_mul, Matrix.conjTranspose_one]
  simp only [← Matrix.mul_assoc]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, gl_inv_mul, Matrix.mul_one]

theorem re_sum_cast {n : ℕ} (x y : WR.E n) :
    ((((∑ a, ∑ b, ((x a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) : ℂ).re : ℝ) : ℂ) =
      ∑ a, ∑ b, ((x a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ) := by
  have : (∑ a, ∑ b, ((x a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) = ((∑ a, ∑ b, x a b * y a b : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.ofReal_re]

theorem gram_mem (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ)
    (Y : Fin n → Fin M → Ainf F ⊗[F] E) : gramR (Ainf F) σ J Y ∈ HermR (Ainf F) σ n := by
  intro a b
  apply hP.bij.injective
  funext i
  show θ i (sigR _ σ (gramR (Ainf F) σ J Y b a)) = θ i (gramR (Ainf F) σ J Y a b)
  rw [hP.conj]
  have h := map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i
  have hh : ((gramR (Ainf F) σ J Y).map (θ i)).IsHermitian := by
    rw [h]; exact Matrix.isHermitian_conjTranspose_mul_mul _ (gramX_isHerm _ _)
  have := congrFun (congrFun hh a) b
  simpa [Matrix.conjTranspose_apply] using this

theorem phi_mul_psi (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (b : HermR (Ainf F) σ n) (Y : Fin n → Fin M → Ainf F ⊗[F] E) :
    phiInf θ l fr g P Y * psiInf F ψ (trPair (Ainf F) (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (gramR (Ainf F) σ J Y)) =
      ∏ i, (evX (P i) (crdAll θ fr g Y i) * gs (2 * Real.pi * |l i|) (crdAll θ fr g Y i) *
        Complex.exp (Complex.I * ((2 * Real.pi * l i : ℝ) : ℂ) *
          (herm (ybAll σ θ g b i) * gramX (ε i) (crdAll θ fr g Y i)).trace)) := by
  rw [psi_trPair_gen σ hCM ψ θ l hP, Finset.mul_sum, Complex.exp_sum]
  unfold phiInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have htr : ((((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (gramR (Ainf F) σ J Y).map (θ i)).trace.re : ℝ) : ℂ) =
      (herm (ybAll σ θ g b i) * gramX (ε i) (crdAll θ fr g Y i)).trace := by
    rw [map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i, tr4, ← herm_ybAll σ ψ θ l hP g b i]
    exact trace_re_of_herm (WR.I.herm_isHermitian _) (gramX_isHerm _ _)
  rw [htr]
  congr 2
  push_cast
  ring

theorem psi_neg_trPair (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (T b : HermR (Ainf F) σ n) :
    psiInf F ψ (-trPair (Ainf F) (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) =
      ∏ i, WR.chr (2 * Real.pi * l i) (ygAll σ θ g T i) (ybAll σ θ g b i) := by
  rw [psi_neg_trPair_gen σ hCM ψ θ l hP, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (herm (ygAll σ θ g T i) * herm (ybAll σ θ g b i)).trace =
      ((T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).trace := by
    rw [herm_ygAll σ ψ θ l hP g T i, herm_ybAll σ ψ θ l hP g b i]
    have h1 : (((g i)⁻¹).1)ᴴ * ((g i).1)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, gl_mul_inv, Matrix.conjTranspose_one]
    calc (((g i).1)ᴴ * (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1 *
          (((g i)⁻¹).1 * (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ)).trace
        = (((g i).1)ᴴ * ((T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ)).trace := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (g i).1, gl_mul_inv, Matrix.one_mul]
      _ = ((T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((((g i)⁻¹).1)ᴴ * ((g i).1)ᴴ)).trace := by
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [← e, trace_herm_mul, re_sum_cast, WR.chr]
  congr 1
  push_cast
  ring

theorem nuInf_eq (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (b : HermR (Ainf F) σ n) :
    nuInf θ g (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = ∏ i, WR.dP (ybAll σ θ g b i) := by
  unfold nuInf
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [WR.dP, herm_ybAll σ ψ θ l hP g b i]

theorem gram_preimage_box (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (hfr : IsFrames J θ ε fr)
    (g : ι → GL (Fin n) ℂ) (K : ι → Set (WR.E n)) :
    gramR (Ainf F) σ J ⁻¹' (Subtype.val '' (ygAll σ θ g ⁻¹' Set.univ.pi K)) =
      crdAll θ fr g ⁻¹' Set.univ.pi (fun i => gramX (ε i) ⁻¹' (herm '' K i)) := by
  ext Y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_univ_pi]
  constructor
  · rintro ⟨s, hs, hsY⟩ i
    refine ⟨ygAll σ θ g s i, hs i, ?_⟩
    rw [herm_ygAll σ ψ θ l hP g s i, hsY, map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i, gl_conj_cancel]
  · intro h
    refine ⟨⟨gramR (Ainf F) σ J Y, gram_mem σ ψ θ l hP J ε fr hfr g Y⟩, fun i => ?_, rfl⟩
    obtain ⟨k, hk, hkQ⟩ := h i
    have : ygAll σ θ g ⟨gramR (Ainf F) σ J Y, gram_mem σ ψ θ l hP J ε fr hfr g Y⟩ i = k := by
      rw [← hinv_herm k, hkQ]
      show hinv _ = _
      congr 1
      show ((g i).1)ᴴ * (gramR (Ainf F) σ J Y).map (θ i) * (g i).1 = _
      rw [map_gramR_crd σ ψ θ l hP J ε fr hfr g Y i, gl_conj_cancel]
    rw [this]
    exact hk

theorem psi_pairHerm (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (S T : HermR (Ainf F) σ n) :
    psiInf F ψ (pairHerm (Ainf F) σ n S T) = Complex.exp (2 * Real.pi * Complex.I *
      ∑ i, (l i : ℂ) * ∑ a, ∑ b, ((ybAll σ θ g S i a b : ℝ) : ℂ) * ((ygAll σ θ g T i a b : ℝ) : ℂ)) := by
  have e0 : pairHerm (Ainf F) σ n S T =
      trPair (Ainf F) (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := rfl
  rw [e0, psi_trPair_gen σ hCM ψ θ l hP]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have e : (herm (ybAll σ θ g S i) * herm (ygAll σ θ g T i)).trace =
      ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).trace := by
    rw [herm_ygAll σ ψ θ l hP g T i, herm_ybAll σ ψ θ l hP g S i]
    have h1 : (((g i)⁻¹).1)ᴴ * ((g i).1)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, gl_mul_inv, Matrix.conjTranspose_one]
    calc (((g i)⁻¹).1 * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (((g i)⁻¹).1)ᴴ *
          (((g i).1)ᴴ * (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1)).trace
        = (((g i)⁻¹).1 * ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * (g i).1)).trace := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (((g i)⁻¹).1)ᴴ, h1, Matrix.one_mul]
      _ = ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) *
            (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i) * ((g i).1 * ((g i)⁻¹).1)).trace := by
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [gl_mul_inv, Matrix.mul_one]
  rw [← e, trace_herm_mul, re_sum_cast]

theorem pairHerm_comm (σ : E →ₐ[F] E) {n : ℕ} (S T : HermR (Ainf F) σ n) :
    pairHerm (Ainf F) σ n S T = pairHerm (Ainf F) σ n T S := by
  simp only [pairHerm]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem det_herm_ygAll (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ} (g : ι → GL (Fin n) ℂ)
    (S : HermR (Ainf F) σ n) (hS : IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det) (i : ι) :
    (herm (ygAll σ θ g S i)).det ≠ 0 := by
  rw [herm_ygAll σ ψ θ l hP g S i, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h1 : ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).det ≠ 0 := by
    rw [show ((S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map (θ i)).det =
      θ i (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det from (RingHom.map_det _ _).symm]
    exact (hS.map (θ i)).ne_zero
  have h2 : ((g i).1).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (g i).isUnit).ne_zero
  exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr h2) h1) h2

end PositivityTheory.SiegelWeilFormula.GReal
