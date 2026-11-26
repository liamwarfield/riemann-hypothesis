module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.RealLift.QuadFock

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPlLin (w : ι) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun _ => LinearMap.id) w

theorem atPlLin_apply (w : ι) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := by
  simp only [atPlLin, MultilinearMap.toLinearMap_apply, PiTensorProduct.mapMultilinear_apply, atPl]

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  rw [← atPlLin_apply, map_zero]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]
    rfl

end Tensor

variable {P Q R S : ℕ}

theorem heisOp_smul (r : ℝ) (c : Matrix (Ix P Q) (Ix R S) ℂ) : heisOp (r • c) = (r : ℂ) • heisOp c := by
  unfold heisOp
  rw [smul_comm (r : ℂ) ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.smul_apply, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, smul_sub, smul_smul]
  congr 2 <;> ring

theorem heisOp_zero : heisOp (0 : Matrix (Ix P Q) (Ix R S) ℂ) = 0 := by
  simpa using heisOp_smul (P := P) (Q := Q) (R := R) (S := S) 0 0

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι) (M : Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w' => heisOp ((Pi.single w M : ι → Matrix (Ix P Q) (Ix R S) ℂ) w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ}

def sgn (a : Ix P Q) (b : Ix R S) : ℝ := (lineSign a b).re

theorem lineSign_eq_sgn (a : Ix P Q) (b : Ix R S) : lineSign a b = ((sgn a b : ℝ) : ℂ) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

theorem sgn_mul_self (a : Ix P Q) (b : Ix R S) : sgn a b * sgn a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single w (Matrix.single a b x)

theorem eS_apply (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (w' : ι) (a' : Ix P Q) (b' : Ix R S) :
    eS w a b x w' a' b' = if w' = w ∧ a' = a ∧ b' = b then x else 0 := by
  by_cases hw : w' = w
  · subst hw
    simp only [eS, Pi.single_eq_same, Matrix.single_apply, true_and]
    by_cases h : a' = a ∧ b' = b
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
  · simp [eS, hw]

theorem sum_eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [eS_apply]
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

theorem decomp (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [eS_apply, and_self, if_true, Complex.real_smul, mul_one]
    exact (Complex.re_add_im _).symm
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def cu (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem dual {l : Type} [Fintype l] (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

theorem cu_true_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, true) w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, false) w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, true) = (Pi.single w (Matrix.single a b Complex.I) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, false) = (Pi.single w (Matrix.single a b (1 : ℂ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem atPlLin_mul {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) (L L' : Module.End ℂ (V w)) :
    atPlLin w (L * L') = atPlLin w L * atPlLin w L' := by
  simp only [atPlLin_apply, atPl_mul]

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

theorem quad_fock : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  intro H1 H2 ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := H1 l (ι × Ix P Q × Ix R S × Bool) Z (fun i => φ (cu i)) (fun i => φ (cv i)) (dual φ hφ)
  have hop : sumPl (V := fun _ : ι => Pol P Q R S) (fun w => fockAct2 P Q R S (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
        (sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) +
          sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ))) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu_true_mul, cu_false_mul, cv_true, cv_false, sumPl_single,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [H2 P Q R S (Y w) (hY w)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add (f := _), atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear H1 H2 hq hop hφ hY
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.RealLift.QuadFock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadraticStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockToSchwartz_intertwines_metaplecticQuadratic : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  first | exact @GlobalTheory.RealLift.QuadFock.quad_fock | exact GlobalTheory.RealLift.QuadFock.quad_fock | (intros; apply GlobalTheory.RealLift.QuadFock.quad_fock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesBasisIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBoxLatticesProduct
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.LeftBasis

theorem isIntB_of_isIntB_of_repr {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) (v : HeightOneSpectrum ℤ)
    (h : ∀ k' k, algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' k') k) ∈ v.adicCompletionIntegers ℚ)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) (hy : IsIntB v b' y) : IsIntB v b y := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_tmul b' v y, map_sum, Finsupp.finsetSum_apply]
  refine sum_mem fun k' _ => ?_
  rw [repr_tmul_apply]
  exact mul_mem (hy k') (h k' k)

theorem isIntB_iff_eventually {M : Type} [Ring M] [Algebra ℚ M] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (b : Module.Basis κ ℚ M) (b' : Module.Basis κ' ℚ M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ y, IsIntB v b y ↔ IsIntB v b' y := by
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ' × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b' t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ',
      algebraMap ℚ (v.adicCompletion ℚ) (b'.repr (b t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv y => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  exact ⟨isIntB_of_isIntB_of_repr b' b v (fun k k' => hv.2 (k, k')) y,
    isIntB_of_isIntB_of_repr b b' v (fun k' k => hv.1 (k', k)) y⟩

theorem isIntB_sum_leftBasis_iff_eventually : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  intro L _ _ C _ _ ι r e he κ ℓ κ' b
  let Φl : (Fin r → L) →ₗ[ℚ] C :=
    ∑ i, (LinearMap.mulRight ℚ (e i)) ∘ₗ ι.toLinearMap ∘ₗ LinearMap.proj i
  have hΦl : ∀ c, Φl c = ∑ i, ι (c i) * e i := fun c => by
    simp [Φl, LinearMap.sum_apply]
  have hbij : Function.Bijective Φl := by
    refine ⟨fun c c' hcc => ?_, fun x => ?_⟩
    · obtain ⟨d, -, hd⟩ := he (Φl c)
      exact (hd c (hΦl c)).trans (hd c' (hcc.trans (hΦl c'))).symm
    · obtain ⟨d, hd, -⟩ := he x
      exact ⟨d, (hΦl d).trans hd.symm⟩
  let Φ := LinearEquiv.ofBijective Φl hbij
  let b' : Module.Basis (Σ _ : Fin r, κ) ℚ C := (Pi.basis fun _ : Fin r => ℓ).map Φ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  haveI : FiniteDimensional ℚ C := Module.Finite.of_basis b'
  haveI : Fintype κ' := FiniteDimensional.fintypeBasisIndex b
  have hsingle : ∀ (j : Fin r) (l : L), Φ (Pi.single j l) = ι l * e j := by
    intro j l
    show Φl _ = _
    rw [hΦl, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · simp
  have hrepr : ∀ (j : Fin r) (l : L) (i : Fin r) (a : κ),
      b'.repr (ι l * e j) ⟨i, a⟩ = ℓ.repr ((Pi.single j l : Fin r → L) i) a := by
    intro j l i a
    rw [← hsingle]
    simp [b', Module.Basis.map_repr, Pi.basis_repr]
  have hcoord : ∀ (v : HeightOneSpectrum ℤ) (j : Fin r) (z : v.adicCompletion ℚ ⊗[ℚ] L) (i : Fin r) (a : κ),
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
        (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι z * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr ((Pi.single j z : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) i) a := by
    intro v j z i a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s l =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, AlgHom.id_apply,
        repr_tmul_apply, hrepr]
      by_cases h : i = j
      · subst h; simp [repr_tmul_apply]
      · simp [h]
    | add x y hx hy =>
      rw [map_add (f := _), add_mul, LinearEquiv.map_add (e := _), Finsupp.add_apply, hx, hy, Pi.single_add, Pi.add_apply,
        LinearEquiv.map_add, Finsupp.add_apply]
  obtain ⟨S, hS⟩ := isIntB_iff_eventually b b'
  refine ⟨S, fun v hv β => ?_⟩
  have hy : ∀ (i : Fin r) (a : κ), (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b').repr
      (∑ j, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β j) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e j)) ⟨i, a⟩ =
      (Algebra.TensorProduct.basis (v.adicCompletion ℚ) ℓ).repr (β i) a := by
    intro i a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    simp_rw [hcoord]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finsupp.finsetSum_apply, ← map_sum]
    congr 2
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hS v hv]
  constructor
  · intro h i a
    rw [← hy]
    exact h ⟨i, a⟩
  · rintro h ⟨i, a⟩
    rw [hy]
    exact h i a

end GlobalTheory.AdicSpan.LeftBasis
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_all_places_basis_integral : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  first | (exact @GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (exact GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (intros; apply GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually  <;> assumption)
end
