module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrix
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory

theorem hTens_eq_trace {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (JAᵀ * (x * JB * (y.map c)ᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_mul_left {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S) :
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  unfold symp
  congr 2
  rw [hTens_eq_trace, hTens_eq_trace, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBaseChangeMatrixStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_base_change_matrix : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S),
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  first | exact @GlobalTheory.symp_mul_left | exact GlobalTheory.symp_mul_left | (intros; apply GlobalTheory.symp_mul_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticExtensionSymplecticCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticExtensionSymplecticCoordinates
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PairCoords

def pairBil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {d : ℕ}
    (K : Matrix (Fin d) (Fin d) S) : LinearMap.BilinForm R (Fin d → S) :=
  LinearMap.mk₂ R (fun b a => Algebra.trace R S (-∑ j, ∑ l, b j * K j l * c (a l)))
    (fun b b' a => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add, map_add (f := _)])
    (fun r b a => by
      simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, ← smul_neg, map_smul, smul_eq_mul])
    (fun b a a' => by
      simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, neg_add])
    (fun r b a => by
      simp only [Pi.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum, ← smul_neg, smul_eq_mul])

theorem pairBil_apply {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {d : ℕ}
    (K : Matrix (Fin d) (Fin d) S) (b a : Fin d → S) :
    pairBil c K b a = Algebra.trace R S (-∑ j, ∑ l, b j * K j l * c (a l)) := rfl

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CharZero F]

theorem eq_zero_of_pairBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {K : Matrix (Fin d) (Fin d) E}
    (hK : K.det ≠ 0) (b : Fin d → E) (hb : ∀ a, pairBil σ K b a = 0) : b = 0 := by
  have h1 : b ᵥ* K = 0 := by
    funext l
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    have := hb (Pi.single l (σ (-e)) : Fin d → E)
    rw [pairBil_apply] at this
    rw [Algebra.traceForm_apply, ← this]
    congr 1
    have hs : ∀ j, ∑ l', b j * K j l' * σ ((Pi.single l (σ (-e)) : Fin d → E) l') = b j * K j l * -e := fun j => by
      rw [Finset.sum_eq_single l]
      · simp [hσ]
      · intro l' _ h
        simp [Pi.single_apply, h]
      · simp
    simp only [hs, Matrix.vecMul, dotProduct, Pi.zero_apply, Finset.sum_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc b = b ᵥ* (K * K⁻¹) := by rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hK), Matrix.vecMul_one]
    _ = (b ᵥ* K) ᵥ* K⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [h1, Matrix.zero_vecMul]

theorem nondegenerate_pairBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {K : Matrix (Fin d) (Fin d) E}
    (hK : K.det ≠ 0) : (pairBil σ K).Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (fun b hb => eq_zero_of_pairBil σ hσ hK b hb)

end Field

end GlobalTheory.PairCoords

namespace GlobalTheory.PairCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_inclR (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) =
    algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem pairBil_incV (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) (v w : Fin d → E) :
    pairBil (cA σ) (incM F K) (incV F v) (incV F w) = algebraMap F (AF F) (pairBil σ K v w) := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [pairBil_apply, pairBil_apply, ← trace_inclR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [incV, incM, Matrix.map_apply, hc, map_mul, map_sum, map_neg]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.PairCoords

theorem GlobalTheory.PairCoords.exists_pair_coords : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (K : Matrix (Fin d) (Fin d) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 →
    ∃ p q : (Fin d → AE F E) ≃ₗ[AF F] (Fin 2 × Fin d → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  intro F E _ _ _ _ _ σ d K hσ h2 hK hdet
  classical
  have hrk : Module.finrank F (Fin d → E) = 2 * d := by
    rw [Module.finrank_pi_fintype]
    simp [h2, mul_comm]
  let β : Module.Basis (Fin 2 × Fin d) F (Fin d → E) :=
    (Module.finBasisOfFinrankEq F (Fin d → E) hrk).reindex finProdFinEquiv.symm
  let hnd := GlobalTheory.PairCoords.nondegenerate_pairBil σ hσ hdet
  let β₂ := (GlobalTheory.PairCoords.pairBil σ K).dualBasis hnd β
  let e := TensorProduct.piRight F (AF F) (AF F) (fun _ : Fin d => E)
  have hinc : ∀ v : Fin d → E, e ((1 : AF F) ⊗ₜ[F] v) = incV F v := fun v => by
    funext i
    rfl
  let B₁ := (β.baseChange (AF F)).map e
  let B₂ := (β₂.baseChange (AF F)).map e
  have hB₁ : ∀ l, B₁ l = incV F (β l) := fun l => by
    simp only [B₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hB₂ : ∀ l, B₂ l = incV F (β₂ l) := fun l => by
    simp only [B₂, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hk : ∀ k l, GlobalTheory.PairCoords.pairBil (cA σ) (incM F K) (B₂ k) (B₁ l) = if l = k then 1 else 0 := by
    intro k l
    rw [hB₁, hB₂, GlobalTheory.PairCoords.pairBil_incV, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have h1 : ∀ a b, B₂.equivFun b ⬝ᵥ B₁.equivFun a =
      Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l)) := by
    intro a b
    rw [← GlobalTheory.PairCoords.pairBil_apply]
    conv_rhs => rw [← B₂.sum_equivFun b, ← B₁.sum_equivFun a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcc := GlobalTheory.PairCoords.cA_cA σ hσ
  have hK' : ∀ j l, cA σ (incM F K j l) = -incM F K l j := fun j l => by
    show inclR (F := F) (AF F) (σ (K j l)) = -inclR (F := F) (AF F) (K l j)
    rw [hK l j, map_neg]
  have h2' : ∀ a b : Fin d → AE F E, Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l)) =
      Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l)) := by
    intro a b
    let eA : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofBijective (cA σ) (Function.Involutive.bijective hcc)
    rw [← Algebra.trace_eq_of_algEquiv eA (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))]
    congr 1
    show _ = cA σ _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hcc, hK', ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hrat : ∀ (b : Module.Basis (Fin 2 × Fin d) F (Fin d → E)) (a : Fin d → E),
      ((b.baseChange (AF F)).map e).equivFun (incV F a) = fun k => algebraMap F (AF F) (b.repr a k) := by
    intro b a
    funext k
    rw [← hinc, Module.Basis.equivFun_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
  exact ⟨B₁.equivFun, B₂.equivFun, h1, fun a b => (h1 a b).trans (h2' a b),
    fun a => ⟨_, hrat β a⟩, fun a => ⟨_, hrat β₂ a⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticExtensionSymplecticCoordinatesStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_extension_symplectic_coordinates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (K : Matrix (Fin d) (Fin d) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 →
    ∃ p q : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ≃ₗ[AF F] (Fin 2 × Fin d → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  first | exact @GlobalTheory.PairCoords.exists_pair_coords | exact GlobalTheory.PairCoords.exists_pair_coords | (intros; apply GlobalTheory.PairCoords.exists_pair_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameExtendsToBlockBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameExtendsToBlockBasis
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelSet.PerpBasis

theorem exists_ker_basis {E : Type} [Field E] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E) (h : G * B * (G * B) = 1) :
    ∃ (n₀ : ℕ) (Z : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ ι) (Fin n) E),
      n₀ + Fintype.card ι = n ∧ Q * Matrix.fromCols Z B = 1 ∧ Matrix.fromCols Z B * Q = 1 ∧ G * Z = 0 := by
  set K := LinearMap.ker G.mulVecLin with hK
  let b := Module.finBasis E K
  let Z : Matrix (Fin n) (Fin (Module.finrank E K)) E := Matrix.of fun i j => (b j : Fin n → E) i
  have hZv : ∀ a, Z *ᵥ a = ((∑ j, a j • b j : K) : Fin n → E) := by
    intro a
    ext i
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hGZv : ∀ a, G *ᵥ (Z *ᵥ a) = 0 := by
    intro a
    rw [hZv]
    exact (∑ j, a j • b j : K).2
  have hGZ : G * Z = 0 := by
    ext i j
    have := congrFun (hGZv (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hsurj : LinearMap.range G.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨(B * (G * B)) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, h, Matrix.one_mulVec]
  have hdim : Module.finrank E K + Fintype.card ι = n := by
    have := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
    rw [hsurj] at this
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    rw [hK]
    omega
  have hinj : Function.Injective (Matrix.toLin' (Matrix.fromCols Z B)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    rw [Matrix.toLin'_apply, Matrix.fromCols_mulVec] at hv
    have h1 : (G * B) *ᵥ (v ∘ Sum.inr) = 0 := by
      have := congrArg (G *ᵥ ·) hv
      simp only [Matrix.mulVec_add, hGZv, zero_add, Matrix.mulVec_zero] at this
      rw [← Matrix.mulVec_mulVec]; exact this
    have h2 : v ∘ Sum.inr = 0 := by
      have := congrArg ((G * B) *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [h, Matrix.one_mulVec] at this
    rw [h2, Matrix.mulVec_zero, add_zero, hZv] at hv
    have h3 : (∑ j, (v ∘ Sum.inl) j • b j : K) = 0 := Subtype.ext hv
    have h4 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
    ext x
    rcases x with x | x
    · exact h4 x
    · exact congrFun h2 x
  let e := LinearMap.linearEquivOfInjective _ hinj (by simp [hdim])
  have he : (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.toLin' (Matrix.fromCols Z B) := by
    ext1 x; rfl
  have he' : LinearMap.toMatrix' (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.fromCols Z B := by rw [he, LinearMap.toMatrix'_toLin']
  refine ⟨_, Z, LinearMap.toMatrix' (e.symm : (Fin n → E) →ₗ[E] (Fin (Module.finrank E K) ⊕ ι → E)),
    hdim, ?_, ?_, hGZ⟩
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem gram_eq_map (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {a b : Type}
    (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) A * ((1 : E) • J.map σ) * B).map σ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply, hσ]

theorem gram_eq_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j)
    {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) B * ((1 : E) • J.map σ) * A)ᵀ := by
  have : J.map σ = Jᵀ := by ext i j; simp [hJ]
  rw [this]
  simp only [Formalism.UG.cT, one_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rfl

end

theorem exists_perp_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ hdet r₀ X Y hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have gxx : Xᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.xx]; simp
  have gyy : Yᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.yy]; simp
  have gyx : Yᵀ * J * X.map σ = 1 := by rw [gram_eq_transpose σ J hJ, hW.xy]; simp
  have gxy : Xᵀ * J * Y.map σ = 1 := by
    rw [gram_eq_map σ hσ J, hW.xy]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * X = 1 := by
    have := gram_eq_transpose σ J hJ X Y
    rw [gxy] at this
    rw [← Matrix.transpose_transpose (_ * X), ← this, Matrix.transpose_one]
  have hGB : Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ)) * Matrix.fromCols X Y =
      Matrix.fromBlocks 0 1 1 0 := by
    rw [Matrix.fromRows_mul_fromCols, hW.xx, hW.yy, hW.xy, hyx]
  obtain ⟨n₀, Z, Q, hn, hQP, hPQ, hGZ⟩ := exists_ker_basis
    (Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ))) (Matrix.fromCols X Y)
    (by rw [hGB, Matrix.fromBlocks_multiply]; simp)
  rw [Matrix.fromRows_mul] at hGZ
  have hXZ : Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inl i)) j
  have hYZ : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inr i)) j
  have gzx : Zᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hXZ]; simp
  have gzy : Zᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hYZ]; simp
  have gxz : Xᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hXZ]; exact Matrix.map_zero _ (map_zero σ)
  have gyz : Yᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hYZ]; exact Matrix.map_zero _ (map_zero σ)
  have hgram : (Matrix.fromCols Z (Matrix.fromCols X Y))ᵀ * J *
      (Matrix.fromCols Z (Matrix.fromCols X Y)).map σ =
      Matrix.fromBlocks (Zᵀ * J * Z.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) := by
    simp only [Matrix.transpose_fromCols, Matrix.fromCols_map]
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul,
      gxx, gyy, gyx, gxy, gzx, gzy, gxz, gyz]
    simp
  refine ⟨n₀, Z, Q, by simpa using hn, hQP, hPQ, hgram, ?_, ?_, hXZ, hYZ⟩
  · set P := Matrix.fromCols Z (Matrix.fromCols X Y) with hP
    have hJu : IsUnit J.det := hdet.isUnit
    have h1 : P.map σ * Q.map σ = 1 := by
      rw [← Matrix.map_mul, hPQ]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
    have h2 : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h3 : (Pᵀ * J * P.map σ) * (Q.map σ * J⁻¹ * Qᵀ) = 1 := by
      calc _ = Pᵀ * (J * ((P.map σ * Q.map σ) * J⁻¹)) * Qᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.one_mul, Matrix.mul_nonsing_inv _ hJu, Matrix.mul_one, h2]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, hgram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at h4
    intro h0
    rw [h0] at h4
    simp at h4
  · intro i j
    have h1 := congrFun (congrFun (gram_eq_map σ hσ J Z Z) j) i
    have h2 := congrFun (congrFun (gram_eq_transpose σ J hJ Z Z) i) j
    rw [h1, h2, Matrix.map_apply, hσ, Matrix.transpose_apply]

end GlobalTheory.SiegelSet.PerpBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameExtendsToBlockBasisStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_extends_to_block_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  first | exact @GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | exact GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | (intros; apply GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingBlockReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingBlockReduction
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WeilM

theorem symp_fromBlocks_hyperbolic :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (r₀ : ℕ) (J₀ : Matrix α α S) (K : Matrix β β S)
    (z z' : Matrix (α ⊕ (Fin r₀ ⊕ Fin r₀)) β S),
    symp c ξ (Matrix.fromBlocks J₀ 0 0 (Matrix.fromBlocks 0 1 1 0)) K z z' =
      symp c ξ J₀ K (Matrix.of fun i l => z (Sum.inl i) l) (Matrix.of fun i l => z' (Sum.inl i) l) +
      ∑ i, (Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inl i)) j * K j l * c (z' (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inr i)) j * K j l * c (z' (Sum.inr (Sum.inl i)) l))) := by
  intro R S _ _ _ c ξ α β _ _ _ _ r₀ J₀ K z z'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [symp, hTens, ← map_add (f := _), ← map_sum, ← mul_add, ← Finset.mul_sum]
  congr 2
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.of_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib]
  congr 1
  rw [add_comm]
  congr 1 <;>
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Matrix.one_apply]

end GlobalTheory.WeilM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingBlockReductionStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_pairing_block_reduction : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (r₀ : ℕ) (J₀ : Matrix α α S) (K : Matrix β β S)
    (z z' : Matrix (α ⊕ (Fin r₀ ⊕ Fin r₀)) β S),
    symp c ξ (Matrix.fromBlocks J₀ 0 0 (Matrix.fromBlocks 0 1 1 0)) K z z' =
      symp c ξ J₀ K (Matrix.of fun i l => z (Sum.inl i) l) (Matrix.of fun i l => z' (Sum.inl i) l) +
      ∑ i, (Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inl i)) j * K j l * c (z' (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inr i)) j * K j l * c (z' (Sum.inr (Sum.inl i)) l))) := by
  first | exact @GlobalTheory.WeilM.symp_fromBlocks_hyperbolic | exact GlobalTheory.WeilM.symp_fromBlocks_hyperbolic | (intros; apply GlobalTheory.WeilM.symp_fromBlocks_hyperbolic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinates
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
noncomputable section

namespace GlobalTheory.TorusAdapted

section Coords

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n₀ r₀ d : ℕ}

def top (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A) : Matrix (Fin n₀) (Fin d) A :=
  Matrix.of fun i l => u (Sum.inl i) l

def blockCo (e₀ : Matrix (Fin n₀) (Fin d) A ≃ₗ[R] (Fin n₀ × Fin d → R) × (Fin n₀ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) :
    Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A ≃ₗ[R]
      ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → R) × ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → R) where
  toFun u := (Sum.elim (e₀ (top u)).1 (fun k => q (u (Sum.inr (Sum.inr k.1))) k.2),
    Sum.elim (e₀ (top u)).2 (fun k => p (u (Sum.inr (Sum.inl k.1))) k.2))
  invFun fg := Matrix.of fun r l => Sum.elim (fun i => e₀.symm (fg.1 ∘ Sum.inl, fg.2 ∘ Sum.inl) i l)
    (Sum.elim (fun i => p.symm (fun k => fg.2 (Sum.inr (i, k))) l) (fun i => q.symm (fun k => fg.1 (Sum.inr (i, k))) l)) r
  map_add' u u' := by
    have ht : top (u + u') = top u + top u' := rfl
    have hr : ∀ r, (u + u') r = u r + u' r := fun _ => rfl
    rw [ht]
    ext (k | k) <;> simp [hr]
  map_smul' a u := by
    have ht : top (a • u) = a • top u := rfl
    have hr : ∀ r, (a • u) r = a • u r := fun _ => rfl
    rw [ht]
    ext (k | k) <;> simp [hr]
  left_inv u := by
    ext (i | i | i) l
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_comp_inl]
      rw [show ((e₀ (top u)).1, (e₀ (top u)).2) = e₀ (top u) from rfl, LinearEquiv.symm_apply_apply]
      rfl
    · simp
    · simp
  right_inv fg := by
    rcases fg with ⟨f, g⟩
    set U : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A := Matrix.of fun r l => Sum.elim
      (fun i => e₀.symm (f ∘ Sum.inl, g ∘ Sum.inl) i l) (Sum.elim (fun i => p.symm (fun k => g (Sum.inr (i, k))) l)
        (fun i => q.symm (fun k => f (Sum.inr (i, k))) l)) r with hU
    have ht : top U = e₀.symm (f ∘ Sum.inl, g ∘ Sum.inl) := by ext i l; simp [top, hU]
    have hx : ∀ i, U (Sum.inr (Sum.inl i)) = p.symm (fun k => g (Sum.inr (i, k))) := fun i => by funext l; simp [hU]
    have hy : ∀ i, U (Sum.inr (Sum.inr i)) = q.symm (fun k => f (Sum.inr (i, k))) := fun i => by funext l; simp [hU]
    show (Sum.elim (e₀ (top U)).1 (fun k => q (U (Sum.inr (Sum.inr k.1))) k.2),
      Sum.elim (e₀ (top U)).2 (fun k => p (U (Sum.inr (Sum.inl k.1))) k.2)) = (f, g)
    simp only [ht, hx, hy, LinearEquiv.apply_symm_apply]
    ext (k | ⟨i, k⟩) <;> simp

theorem blockCo_apply (e₀ : Matrix (Fin n₀) (Fin d) A ≃ₗ[R] (Fin n₀ × Fin d → R) × (Fin n₀ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A) :
    blockCo e₀ p q u = (Sum.elim (e₀ (top u)).1 (fun k => q (u (Sum.inr (Sum.inr k.1))) k.2),
      Sum.elim (e₀ (top u)).2 (fun k => p (u (Sum.inr (Sum.inl k.1))) k.2)) := rfl

def mulLeftE {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] (Q : Matrix m' m A)
    (P : Matrix m m' A) (h1 : P * Q = 1) (h2 : Q * P = 1) : Matrix m (Fin d) A ≃ₗ[R] Matrix m' (Fin d) A where
  toFun w := Q * w
  invFun z := P * z
  map_add' := Matrix.mul_add Q
  map_smul' a w := Matrix.mul_smul Q a w
  left_inv w := by
    show P * (Q * w) = w
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  right_inv z := by
    show Q * (P * z) = z
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end Coords

theorem infScale_one (F : Type) [Field F] [NumberField F] : GlobalTheory.TorusTheta.infScale F 1 = 1 := by
  unfold GlobalTheory.TorusTheta.infScale
  rw [map_one, map_one]
  rfl

end GlobalTheory.TorusAdapted

namespace GlobalTheory.TorusAdapted

theorem adapted_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∃ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) ∧
      ∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (AE F E), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWF
  have hB := hP.base
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hP.herm.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hW' : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hP.skew.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  obtain ⟨n₀, Z₀, Q, hn, hQP, hPQ, hG, hJ₀, hJ₀h, hZx, hZy⟩ := GlobalTheory.T.witt_frame_extends_to_block_basis F E σ hB.cm n X.J hP.herm.herm hX' r₀ Xf Yf hWF
  set P := Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) with hPdef
  obtain ⟨co₀, hco₀⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hJ₀h hP.skew.skew hJ₀ hW'
  obtain ⟨p, q, hpq, hpq', hpr, hqr⟩ := GlobalTheory.T.quadratic_extension_symplectic_coordinates σ d W.J hσ h2 hP.skew.skew hW'
  have hinc : ∀ {a b c : Type} [Fintype b] (U : Matrix a b E) (V : Matrix b c E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have h1 : incM F P * incM F Q = 1 := by
    rw [← hinc, hPQ]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F Q * incM F P = 1 := by
    rw [← hinc, hQP]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let eb := blockCo (R := AF F) (r₀ := r₀) co₀.e p q
  let mQ : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E) :=
    mulLeftE (incM F Q) (incM F P) h1 h1'
  have hcard : Fintype.card ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d))) = Fintype.card (Fin n × Fin d) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [← hn]; ring
  let ε := Fintype.equivOfCardEq hcard
  let e := mQ.trans (eb.trans (LinearEquiv.prodCongr (LinearEquiv.funCongrLeft (AF F) (AF F) ε.symm)
    (LinearEquiv.funCongrLeft (AF F) (AF F) ε.symm)))
  have he : ∀ z, e z = ((eb (incM F Q * z)).1 ∘ ε.symm, (eb (incM F Q * z)).2 ∘ ε.symm) := fun z => rfl

  have hGinc : (incM F P)ᵀ * incM F X.J * (incM F P).map (cA σ) =
      Matrix.fromBlocks (incM F (Z₀ᵀ * X.J * Z₀.map σ)) 0 0 (Matrix.fromBlocks 0 1 1 0) := by
    rw [show (incM F P)ᵀ * incM F X.J * (incM F P).map (cA σ) = incM F (Pᵀ * X.J * P.map σ) by rw [hinc, hinc]; rfl, hG]
    simp [incM, Matrix.fromBlocks_map]
  have hform₀ : ∀ x y, symp (R := AF F) (cA σ) (-1) (incM F (Z₀ᵀ * X.J * Z₀.map σ)) (incM F W.J) x y =
      (co₀.e x).1 ⬝ᵥ (co₀.e y).2 - (co₀.e y).1 ⬝ᵥ (co₀.e x).2 := co₀.form
  have hdot : ∀ f g : (Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → AF F, (f ∘ ε.symm) ⬝ᵥ (g ∘ ε.symm) = f ⬝ᵥ g :=
    fun f g => by
      simp only [dotProduct, Function.comp]
      exact Equiv.sum_comp ε.symm (fun k => f k * g k)
  have hform : ∀ w₁ w₂, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w₁ w₂ =
      (e w₁).1 ⬝ᵥ (e w₂).2 - (e w₂).1 ⬝ᵥ (e w₁).2 := by
    intro w₁ w₂
    have e1 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w₁ w₂ =
        symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F P * (incM F Q * w₁)) (incM F P * (incM F Q * w₂)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.one_mul]
    have key : ∀ i, Algebra.trace (AF F) (AE F E) (-1 * ∑ j, ∑ l, (incM F Q * w₁) (Sum.inr (Sum.inl i)) j *
          incM F W.J j l * cA σ ((incM F Q * w₂) (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace (AF F) (AE F E) (-1 * ∑ j, ∑ l, (incM F Q * w₁) (Sum.inr (Sum.inr i)) j *
          incM F W.J j l * cA σ ((incM F Q * w₂) (Sum.inr (Sum.inl i)) l)) =
        q ((incM F Q * w₁) (Sum.inr (Sum.inr i))) ⬝ᵥ p ((incM F Q * w₂) (Sum.inr (Sum.inl i))) -
          q ((incM F Q * w₂) (Sum.inr (Sum.inr i))) ⬝ᵥ p ((incM F Q * w₁) (Sum.inr (Sum.inl i))) := fun i => by
      rw [neg_one_mul, neg_one_mul, map_neg, ← hpq', ← hpq]; ring
    rw [e1, GlobalTheory.T.symplectic_form_base_change_matrix, hGinc, GlobalTheory.T.symplectic_pairing_block_reduction, hform₀, he, he, hdot, hdot, blockCo_apply, blockCo_apply]
    simp only [key, sumElim_dotProduct_sumElim, top]
    simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_sub_distrib]
    ring

  refine ⟨⟨e, hform⟩, fun j => Sum.elim (fun _ => (none : Option (Fin r₀))) (fun k => some k.1) (ε.symm j), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y₀, z₀, h₀⟩ := hco₀ (top (Q * x))
    choose yq hyq using fun i => hqr ((Q * x) (Sum.inr (Sum.inr i)))
    choose yp hyp using fun i => hpr ((Q * x) (Sum.inr (Sum.inl i)))
    refine ⟨Sum.elim y₀ (fun k => yq k.1 k.2) ∘ ε.symm, Sum.elim z₀ (fun k => yp k.1 k.2) ∘ ε.symm, ?_⟩
    have ht : top (incM F (Q * x)) = (top (Q * x)).map (inclR (F := F) (AF F)) := rfl
    have hr : ∀ r, incM F (Q * x) r = incV F ((Q * x) r) := fun _ => rfl
    rw [he, ← hinc, blockCo_apply, ht, h₀]
    simp only [hr, hyq, hyp]
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> simp only [Function.comp_apply] <;>
      generalize ε.symm j = k' <;> rcases k' with k | ⟨i, k⟩ <;> simp
  · intro i
    rw [Finset.card_filter, ← Equiv.sum_comp ε]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
      Option.some.injEq, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  · intro t ht a hT a' ha' z
    have hm : mat a' = ((HA.mat (AF F) σ ((1 : E) • X.J.map σ) a : GL (Fin n) (AE F E)) :
        Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [show mat a' = ((a' : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) from rfl, ha']
    obtain ⟨hx, hy, h0⟩ := GlobalTheory.T.torus_element_acts_on_frame_columns F E σ hB.cm n ((1 : E) • X.J.map σ) r₀ Xf Yf t ht a hT
    generalize ((HA.mat (AF F) σ ((1 : E) • X.J.map σ) a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = m
      at hx hy h0 hm
    have hc : ∀ C : Matrix (Fin n) (Fin r₀) E, Formalism.UG.cT (σ : E →+* E) C * ((1 : E) • X.J.map σ) * Z₀ = 0 → ∀ c,
        (Formalism.UG.cT (σ : E →+* E) C * ((1 : E) • X.J.map σ)) *ᵥ (fun k => Z₀ k c) = 0 := fun C hC c => by
      funext i; exact congrFun (congrFun hC i) c
    have hZ : m * incM F Z₀ = incM F Z₀ := by
      ext r c
      exact congrFun (h0 (fun k => Z₀ k c) (hc Xf hZx c) (hc Yf hZy c)) r
    have hPc : incM F P = Matrix.fromCols (incM F Z₀) (Matrix.fromCols (incM F Xf) (incM F Yf)) := by
      ext r (c | c | c) <;> rfl
    set Dm : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (AE F E) := Matrix.fromBlocks 1 0 0
      (Matrix.fromBlocks (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) 0 0
        (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹))) with hDm
    have hMP : m * incM F P = incM F P * Dm := by
      rw [hPc, Matrix.mul_fromCols, Matrix.mul_fromCols, hZ, hx, hy, hDm, Matrix.fromCols_mul_fromBlocks,
        Matrix.fromCols_mul_fromBlocks]
      simp
    have hQm : incM F Q * (m * z) = Dm * (incM F Q * z) := by
      calc incM F Q * (m * z) = incM F Q * (m * (incM F P * (incM F Q * z))) := by
            rw [← Matrix.mul_assoc (incM F P), h1, Matrix.one_mul]
        _ = incM F Q * (m * incM F P) * (incM F Q * z) := by simp only [Matrix.mul_assoc]
        _ = Dm * (incM F Q * z) := by rw [hMP, ← Matrix.mul_assoc (incM F Q) (incM F P) Dm, h1', Matrix.one_mul]
    have hD1 : ∀ u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E), top (Dm * u) = top u := fun u => by
      ext i l; simp [top, hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    have hD2 : ∀ (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E)) i,
        (Dm * u) (Sum.inr (Sum.inl i)) = GlobalTheory.TorusTheta.infScale F (t i) • u (Sum.inr (Sum.inl i)) := fun u i => by
      funext l; simp [hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply, Algebra.smul_def]
    have hD3 : ∀ (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E)) i,
        (Dm * u) (Sum.inr (Sum.inr i)) = GlobalTheory.TorusTheta.infScale F (t i)⁻¹ • u (Sum.inr (Sum.inr i)) := fun u i => by
      funext l; simp [hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply, Algebra.smul_def]
    rw [hm, he, he, hQm, blockCo_apply, blockCo_apply, hD1]
    simp only [hD2, hD3, map_smul]
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> simp only [Function.comp_apply] <;>
      generalize ε.symm j = k' <;> rcases k' with k | ⟨i, k⟩ <;> simp [infScale_one]

end GlobalTheory.TorusAdapted
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinatesStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∃ (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) ∧
      ∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j) := by
  first | exact @GlobalTheory.TorusAdapted.adapted_torus | exact GlobalTheory.TorusAdapted.adapted_torus | (intros; apply GlobalTheory.TorusAdapted.adapted_torus <;> assumption)
end
