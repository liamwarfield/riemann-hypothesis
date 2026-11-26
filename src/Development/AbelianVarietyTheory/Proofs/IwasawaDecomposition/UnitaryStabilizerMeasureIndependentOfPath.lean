module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapPairsContinuousDensityNearDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureIsRestrictedProductLocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureOrthogonalBasesPlaneCompare
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepMeasureOrthogonalBasisSwapLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepMeasureOrthogonalBasisSwapLocal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeEx.SwapLoc

theorem dens_compare {V T : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure V) (τ : Measure T) [SigmaFinite τ] [τ.IsOpenPosMeasure]
    (g : V → T) (Γ : V ≃ₜ V) (Φ : T ≃ₜ T) (hg : ∀ X, g (Γ X) = Φ (g X))
    (c₁ c₂ : ℝ≥0) (hμ : μ = c₁ • μ.map Γ) (hτ : τ = c₂ • τ.map Φ) (φ : V → ℝ)
    (U₁ U₂ : Set T) (D₁ D₂ : T → ℝ) (t : T) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (ht₁ : t ∈ U₁) (ht₂ : Φ t ∈ U₂) (hD₁ : ContinuousOn D₁ U₁) (hD₂ : ContinuousOn D₂ U₂)
    (h0₁ : 0 ≤ D₁ t) (h0₂ : 0 ≤ D₂ (Φ t))
    (h₁ : ∀ S ⊆ U₁, MeasurableSet S →
      ∫⁻ X in g ⁻¹' S, ENNReal.ofReal (φ (Γ X)) ∂μ = ∫⁻ t in S, ENNReal.ofReal (D₁ t) ∂τ)
    (h₂ : ∀ S ⊆ U₂, MeasurableSet S →
      ∫⁻ X in g ⁻¹' S, ENNReal.ofReal (φ X) ∂μ = ∫⁻ t in S, ENNReal.ofReal (D₂ t) ∂τ) :
    (c₂ : ℝ) * D₂ (Φ t) = c₁ * D₁ t := by
  set W : Set T := U₁ ∩ Φ ⁻¹' U₂ with hW
  have hWo : IsOpen W := hU₁.inter (hU₂.preimage Φ.continuous)
  have k₁ : ContinuousOn (fun s => ENNReal.ofReal ((c₁ : ℝ) * D₁ s)) W :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (hD₁.mono Set.inter_subset_left))
  have k₂ : ContinuousOn (fun s => ENNReal.ofReal ((c₂ : ℝ) * D₂ (Φ s))) W :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (hD₂.comp Φ.continuous.continuousOn fun s hs => hs.2))
  have hae : (fun s => ENNReal.ofReal ((c₂ : ℝ) * D₂ (Φ s))) =ᵐ[τ.restrict W]
      fun s => ENNReal.ofReal ((c₁ : ℝ) * D₁ s) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (k₂.aemeasurable hWo.measurableSet)
      (k₁.aemeasurable hWo.measurableSet) fun s hs _ => ?_
    rw [Measure.restrict_restrict hs]
    set S := s ∩ W with hS
    have hSm : MeasurableSet S := hs.inter hWo.measurableSet
    have e₁ := h₁ S (fun z hz => hz.2.1) hSm
    have e₂ := h₂ (Φ '' S) (by rintro _ ⟨z, hz, rfl⟩; exact hz.2.2)
      (Φ.measurableEmbedding.measurableSet_image.2 hSm)
    have a₁ : ∫⁻ X in g ⁻¹' (Φ '' S), ENNReal.ofReal (φ X) ∂μ =
        c₁ * ∫⁻ X in g ⁻¹' S, ENNReal.ofReal (φ (Γ X)) ∂μ := by
      conv_lhs => rw [hμ]
      rw [Measure.restrict_smul, lintegral_smul_measure, Γ.measurableEmbedding.restrict_map,
        Γ.measurableEmbedding.lintegral_map]
      have : Γ ⁻¹' (g ⁻¹' (Φ '' S)) = g ⁻¹' S := by
        ext X
        simp only [Set.mem_preimage, hg]
        exact Φ.injective.mem_set_image
      rw [this]; rfl
    have a₂ : ∫⁻ t in Φ '' S, ENNReal.ofReal (D₂ t) ∂τ =
        c₂ * ∫⁻ t in S, ENNReal.ofReal (D₂ (Φ t)) ∂τ := by
      conv_lhs => rw [hτ]
      rw [Measure.restrict_smul, lintegral_smul_measure, Φ.measurableEmbedding.restrict_map,
        Φ.measurableEmbedding.lintegral_map, Set.preimage_image_eq _ Φ.injective]
      rfl
    simp only [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      ← a₂, ← e₂, a₁, e₁]
  have := Measure.eqOn_open_of_ae_eq hae hWo k₂ k₁ (show t ∈ W from ⟨ht₁, ht₂⟩)
  exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg c₂.2 h0₂) (mul_nonneg c₁.2 h0₁)).1 this

theorem lrAct_one_apply {S : Type} [CommRing S] {n M : ℕ} (γ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) (a : Fin n) (i : Fin M) :
    lrAct 1 γ X a i = ∑ c, X c i * γ c a := by
  simp [lrAct]

theorem lrAct_one_mul {S : Type} [CommRing S] {n M : ℕ} (γ δ : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) : lrAct 1 δ (lrAct 1 γ X) = lrAct 1 (γ * δ) X := by
  funext a i
  simp only [lrAct_one_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lrAct_one_one {S : Type} [CommRing S] {n M : ℕ}
    (X : Fin n → Fin M → S) : lrAct 1 1 X = X := by
  funext a i
  simp [lrAct_one_apply, Matrix.one_apply]

theorem continuous_lrAct_one {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (γ : Matrix (Fin n) (Fin n) S) :
    Continuous (lrAct (M := M) 1 γ) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [lrAct_one_apply]
  fun_prop

def lrHomeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (γ δ : Matrix (Fin n) (Fin n) S) (h₁ : γ * δ = 1) (h₂ : δ * γ = 1) :
    (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S) where
  toFun := lrAct 1 γ
  invFun := lrAct 1 δ
  left_inv X := by rw [lrAct_one_mul, h₁, lrAct_one_one]
  right_inv X := by rw [lrAct_one_mul, h₂, lrAct_one_one]
  continuous_toFun := continuous_lrAct_one γ
  continuous_invFun := continuous_lrAct_one δ

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)

theorem hR_incl {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (y i)) = inclR R (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hR, hE, Formalism.UG.hform, map_sum, JR, sigR, inclR]

theorem qR_incl [CharZero F] (h2 : Module.finrank F E = 2) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin M → E) (a : F) (h : hE σ J x x = algebraMap F E a) :
    qR R σ J (fun i => inclR R (x i)) = algebraMap F R a := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have e : inclR (F := F) R (algebraMap F E a) = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  rw [qR, hR_incl, h, e, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2))]
  rw [Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  have : algebraMap F R (1 / 2) * ((2 : ℕ) : R) = 1 := by
    rw [← map_natCast (algebraMap F R), ← map_mul]; norm_num
  rw [this, one_mul]

theorem hE_mulVec {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin M') E)
    (y : Fin M' → E) :
    hE σ J (B.mulVec y) (B.mulVec y) = hE σ (Formalism.UG.cT (σ : E →+* E) B * J * B) y y := by
  have k : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (u v : Fin n → E),
      hE σ A u v = (fun i => σ (u i)) ⬝ᵥ A.mulVec v := by
    intro n A u v
    simp [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have : (fun i => σ (B.mulVec y i)) = Matrix.vecMul (fun i => σ (y i)) (Formalism.UG.cT (σ : E →+* E) B) := by
    funext i
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, mul_comm]
  rw [k, k, this, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem hE_mulVec_zero {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin M') E)
    (x : Fin M → E) (h : ∀ j, hE σ J x (fun i => B i j) = 0) (y : Fin M' → E) :
    hE σ J x (B.mulVec y) = 0 := by
  have : hE σ J x (B.mulVec y) = ∑ j, hE σ J x (fun i => B i j) * y j := by
    simp only [hE, Formalism.UG.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin M')))]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  simp [this, h]

theorem unitaryOrthogonalComplement_gram_step [CharZero F] (h2 : Module.finrank F E = 2) {M : ℕ}
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (y : Fin M → E) (b : F)
    (h : StepData σ J x a B J') (hy : hE σ J' y y = algebraMap F E b) :
    gram3 R σ J (ratTup (F := F) R ![x 0, B.mulVec y]) = (algebraMap F R a, 0, algebraMap F R b) := by
  obtain ⟨-, -, hx, hB, hJ, -⟩ := h
  refine Prod.ext (qR_incl R σ h2 J (x 0) a hx) (Prod.ext ?_ (qR_incl R σ h2 J (B.mulVec y) b ?_))
  · have := hR_incl R σ J (x 0) (B.mulVec y)
    rw [hE_mulVec_zero σ J B (x 0) hB, map_zero] at this
    exact this
  · rw [hE_mulVec, ← hJ, hy]

theorem ratTup_lrAct {n M : ℕ} (γ : Matrix (Fin n) (Fin n) E) (X : Fin n → Fin M → E) :
    ratTup (F := F) R (lrAct 1 γ X) = lrAct 1 (γ.map (inclR R)) (ratTup (F := F) R X) := by
  funext a i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ratTup, lrAct_one_apply, map_sum]

end Alg

theorem twoStep_swap_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∃ u : E, u ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m₁ m₂ : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m₁' m₂' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a₁) m₁ → FibAt R σ J₁' (tupMeas lam 1 M) ν (algebraMap F R b₁) m₁' → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a₂) m₂ → FibAt R σ J₂' (tupMeas lam 1 M) ν (algebraMap F R b₂) m₂' → TwoStep R σ J x₁ B₁ m₁ m₁' N₁ → TwoStep R σ J x₂ B₂ m₂ m₂' N₂ → N₂ = modu (R ⊗[F] E) (inclR R u) • N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R))) := by
  intro F E _ _ _ _ _ σ hσ M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ hS₁ hS₂ hb₁ hb₂ hy₁ hy₂ hγ
  have hP₁ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x₁ a₁ B₁ J₁' hS₁).1
  have hP₂ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x₂ a₂ B₂ J₂' hS₂).1
  have hd : (γ : Matrix (Fin 2) (Fin 2) E).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  set d := (γ : Matrix (Fin 2) (Fin 2) E).det with hdd
  have hw₁ : (consCol x₁ B₁).det / algebraMap F E a₁ ≠ 0 :=
    div_ne_zero hP₁ ((map_ne_zero _).2 hS₁.2.1)
  have hw₂ : (consCol x₂ B₂).det / algebraMap F E a₂ ≠ 0 :=
    div_ne_zero hP₂ ((map_ne_zero _).2 hS₂.2.1)
  set w₁ := (consCol x₁ B₁).det / algebraMap F E a₁ with hw₁d
  set w₂ := (consCol x₂ B₂).det / algebraMap F E a₂ with hw₂d
  have hu : d ^ (M + 1) * w₁ / (d ^ 2 * w₂) ≠ 0 := by positivity
  refine ⟨d ^ (M + 1) * w₁ / (d ^ 2 * w₂), hu, ?_⟩
  have hue : d ^ (M + 1) * w₁ / (d ^ 2 * w₂) * (d ^ 2 * w₂) = d ^ (M + 1) * w₁ :=
    div_mul_cancel₀ _ (by positivity)
  generalize d ^ (M + 1) * w₁ / (d ^ 2 * w₂) = u at hu hue ⊢
  intro R _ _ _ _ _ _ _ _ _ hR lam ν m₁ m₂ m₁' m₂' N₁ N₂ hlam hν f₁ f₁' f₂ f₂' t₁ t₂
  obtain ⟨hart, hred, -⟩ := nice_tensor F E R hR
  obtain ⟨hpos, hmul, hone, -⟩ := modu_basic (R ⊗[F] E)
  have un : ∀ {z : E}, z ≠ 0 → IsUnit (inclR (F := F) R z) := fun hz => (IsUnit.mk0 _ hz).map _
  have unF : ∀ {z : F}, z ≠ 0 → IsUnit (algebraMap F R z) := fun hz => (IsUnit.mk0 _ hz).map _
  have mm : ∀ {z w : E}, z ≠ 0 → w ≠ 0 → modu (R ⊗[F] E) (inclR R (z * w)) =
      modu (R ⊗[F] E) (inclR R z) * modu (R ⊗[F] E) (inclR R w) := fun hz hw => by
    rw [map_mul, hmul _ _ (un hz) (un hw)]
  have mp : ∀ k : ℕ, modu (R ⊗[F] E) (inclR R (d ^ k)) = modu (R ⊗[F] E) (inclR R d) ^ k := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, mm (pow_ne_zero _ hd) hd, ih, pow_succ]
  have key : modu (R ⊗[F] E) (inclR R u) * (modu (R ⊗[F] E) (inclR R d) ^ 2 *
      modu (R ⊗[F] E) (inclR R w₂)) =
      modu (R ⊗[F] E) (inclR R d) ^ (M + 1) * modu (R ⊗[F] E) (inclR R w₁) := by
    rw [← mp, ← mp, ← mm (pow_ne_zero _ hd) hw₂, ← mm (pow_ne_zero _ hd) hw₁,
      ← mm hu (by positivity), hue]
  have fin₁ : IsFiniteMeasureOnCompacts N₁ :=
    GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hσ R hR M J x₁ a₁ B₁ J₁' m₁ m₁' N₁ hS₁
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J x₁ a₁ lam ν m₁ hS₁.1 hS₁.2.1 hS₁.2.2.1 hlam hν f₁).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J _ ν _ m₁ hν (unF hS₁.2.1) f₁).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J₁' _ ν _ m₁' hν (unF hb₁) f₁').2.1
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J₁' y₁ b₁ lam ν m₁' hS₁.2.2.2.2.2 hb₁ hy₁ hlam hν f₁').1 t₁
  have fin₂ : IsFiniteMeasureOnCompacts N₂ :=
    GlobalTheory.T.twoStep_pair_measure_finite_on_compacts F E σ hσ R hR M J x₂ a₂ B₂ J₂' m₂ m₂' N₂ hS₂
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J x₂ a₂ lam ν m₂ hS₂.1 hS₂.2.1 hS₂.2.2.1 hlam hν f₂).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J _ ν _ m₂ hν (unF hS₂.2.1) f₂).2.1
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR _ J₂' _ ν _ m₂' hν (unF hb₂) f₂').2.1
      (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J₂' y₂ b₂ lam ν m₂' hS₂.2.2.2.2.2 hb₂ hy₂ hlam hν f₂').1 t₂
  let Γ : (Fin 2 → Fin (M + 1) → R ⊗[F] E) ≃ₜ (Fin 2 → Fin (M + 1) → R ⊗[F] E) :=
    lrHomeo ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R))
      (((γ⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).map (inclR R))
      (by rw [← Matrix.map_mul, Units.mul_inv]; simp) (by rw [← Matrix.map_mul, Units.inv_mul]; simp)
  change N₂ = modu (R ⊗[F] E) (inclR R u) • N₁.map Γ
  obtain ⟨Φ, hΦ, hτ⟩ := GlobalTheory.T.haar_measure_gram_GL2_action_tensor F E σ hσ R lam ν γ hlam hν
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) R)).det = inclR R d :=
    ((inclR (F := F) R).map_det _).symm
  have hμ := GlobalTheory.T.vectorTupleProductMeasure_two_sided_action (R ⊗[F] E) hart hred lam hlam 2 (M + 1) 1
    ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R)) (by simp) (by rw [hdet]; exact un hd)
  rw [hdet, Matrix.det_one, hone, one_pow, one_mul] at hμ
  have g₁ := unitaryOrthogonalComplement_gram_step R σ hσ.2.2.1 J x₁ a₁ B₁ J₁' (y₁ 0) b₁ hS₁ hy₁
  have g₂ := unitaryOrthogonalComplement_gram_step R σ hσ.2.2.1 J x₂ a₂ B₂ J₂' (y₂ 0) b₂ hS₂ hy₂
  rw [hγ, ratTup_lrAct, hΦ _ J hS₁.1, g₁] at g₂
  have fin₃ : IsFiniteMeasureOnCompacts (N₁.map Γ) := Measure.IsFiniteMeasureOnCompacts.map N₁ Γ
  have : TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin (M + 1) → R ⊗[F] E) :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology _
  have r₂ : N₂.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have r₁ : (N₁.map Γ).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f => ?_
  have fc : Continuous fun X => (f X : ℝ) := NNReal.continuous_coe.comp f.continuous
  have fs : HasCompactSupport fun X => (f X : ℝ) :=
    f.hasCompactSupport.comp_left (g := fun r : ℝ≥0 => (r : ℝ)) rfl
  obtain ⟨U₂, D₂, o₂, e₂, c₂, n₂, i₂, v₂⟩ := GlobalTheory.T.gramMap_pairs_continuous_density_near_diagonal F E σ hσ R hR M J x₂ a₂ B₂ J₂' y₂ b₂ lam ν
    m₂ m₂' N₂ hS₂ hb₂ hy₂ hlam hν f₂ f₂' t₂ (fun X => (f X : ℝ)) fc fs (fun X => (f X).2)
  obtain ⟨U₁, D₁, o₁, e₁, c₁, n₁, i₁, v₁⟩ := GlobalTheory.T.gramMap_pairs_continuous_density_near_diagonal F E σ hσ R hR M J x₁ a₁ B₁ J₁' y₁ b₁ lam ν
    m₁ m₁' N₁ hS₁ hb₁ hy₁ hlam hν f₁ f₁' t₁ (fun X => (f (Γ X) : ℝ)) (fc.comp Γ.continuous)
    (fs.comp_homeomorph Γ) (fun X => (f (Γ X)).2)
  have cmp := dens_compare (tupMeas lam 2 (M + 1)) (ν.prod (lam.prod ν)) (gram3 R σ J) Γ Φ
    (hΦ _ J hS₁.1) _ _ hμ hτ (fun X => (f X : ℝ)) U₁ U₂ D₁ D₂ _ o₁ o₂ e₁ (g₂ ▸ e₂) c₁ c₂
    (n₁ _ e₁) (n₂ _ (g₂ ▸ e₂)) i₁ i₂
  rw [g₂, v₁, v₂] at cmp
  rw [integral_smul_nnreal_measure, Γ.measurableEmbedding.integral_map, NNReal.smul_def, smul_eq_mul]
  have p₁ : (0 : ℝ) < modu (R ⊗[F] E) (inclR R d) := (hpos _ (un hd)).1
  have p₂ : (0 : ℝ) < modu (R ⊗[F] E) (inclR R w₂) := (hpos _ (un hw₂)).1
  have key' := congrArg (fun r : ℝ≥0 => (r : ℝ)) key
  simp only [NNReal.coe_mul, NNReal.coe_pow] at key' cmp
  refine mul_left_cancel₀ (mul_pos (pow_pos p₁ 2) p₂).ne' ?_
  rw [mul_assoc, cmp, ← mul_assoc, ← key']
  ring

end GlobalTheory.GaugeEx.SwapLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepMeasureOrthogonalBasisSwapLocalStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoStepMeasure_orthogonalBasis_swap_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∃ u : E, u ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m₁ m₂ : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m₁' m₂' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a₁) m₁ → FibAt R σ J₁' (tupMeas lam 1 M) ν (algebraMap F R b₁) m₁' → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a₂) m₂ → FibAt R σ J₂' (tupMeas lam 1 M) ν (algebraMap F R b₂) m₂' → TwoStep R σ J x₁ B₁ m₁ m₁' N₁ → TwoStep R σ J x₂ B₂ m₂ m₂' N₂ → N₂ = modu (R ⊗[F] E) (inclR R u) • N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R))) := by
  first | exact @GlobalTheory.GaugeEx.SwapLoc.twoStep_swap_local | exact GlobalTheory.GaugeEx.SwapLoc.twoStep_swap_local | (intros; apply GlobalTheory.GaugeEx.SwapLoc.twoStep_swap_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureOrthogonalBasesPlaneCompare
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem twoStep_isProd_of_isStdX (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
    (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (y : Fin 1 → Fin M → E) (c : F) (hS : StepData σ J x a B J') (hc : c ≠ 0)
    (hy : hE σ J' (y 0) (y 0) = algebraMap F E c)
    (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E))
    (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E))
    (hν : IsStdX s σ J a ν) (hν' : IsStdX s σ J' c ν') (hN : TwoStep (AF F) σ J x B ν ν' N) :
    ∃ mi mi' Ni, ∃ (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E))
      (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
      (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)),
      FibAt (Ainf F) σ J (tupMeas s.lamI 1 (M + 1)) s.nuI (algebraMap F _ a) mi ∧
      FibAt (Ainf F) σ J' (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ c) mi' ∧
      TwoStep (Ainf F) σ J x B mi mi' Ni ∧
      (∀ v, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 (M + 1)) (s.nuV v) (algebraMap F _ a) (mv v)) ∧
      (∀ v, FibAt (Fv F v) σ J' (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ c) (mv' v)) ∧
      (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) ∧ IsProd b N Ni Nv := by
  obtain ⟨mi, mv, hfi, hfv, hP⟩ := hν
  obtain ⟨mi', mv', hfi', hfv', hP'⟩ := hν'
  have hJ : IsHermND σ J := hS.1
  have ha : a ≠ 0 := hS.2.1
  have hx : hE σ J (x 0) (x 0) = algebraMap F E a := hS.2.2.1
  have hJ' : IsHermND σ J' := hS.2.2.2.2.2
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F
  have oi := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) hNi (M + 1) J x a s.lamI s.nuI mi hJ ha hx
    s.haar_lamI s.haar_nuI hfi
  have oi' := GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Ainf F) hNi M J' y c s.lamI s.nuI mi' hJ' hc hy
    s.haar_lamI s.haar_nuI hfi'
  have ov := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) (M + 1) J x a (s.lamV v) (s.nuV v)
    (mv v) hJ ha hx (s.haar_lamV v) (s.haar_nuV v) (hfv v)
  have ov' := fun v => GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) M J' y c (s.lamV v) (s.nuV v)
    (mv' v) hJ' hc hy (s.haar_lamV v) (s.haar_nuV v) (hfv' v)
  obtain ⟨Ni, hTi, -⟩ := GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hCM (Ainf F) M J x a B J' mi mi' hS oi.2.1 hP.1.1
    hP'.1.1 oi'.1
  have hTv : ∀ v, ∃ N', TwoStep (Fv F v) σ J x B (mv v) (mv' v) N' := fun v =>
    (GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hCM (Fv F v) M J x a B J' (mv v) (mv' v) hS (ov v).2.1 (hP.1.2.1 v)
      (hP'.1.2.1 v) (ov' v).1).exists
  choose Nv hTv using hTv
  exact ⟨mi, mi', Ni, mv, mv', Nv, hfi, hfi', hTi, hfv, hfv', hTv,
    GlobalTheory.T.adelicTwoStepMeasure_isRestrictedProduct_local F E σ hCM d b M J x a B J' ν mi mv ν' mi' mv' N Ni Nv hS hP hP' oi.2.1
      (fun v => (ov v).2.1) oi'.1 (fun v => (ov' v).1) hTi hTv hN⟩

private theorem prInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (e : E) : prInf (inclR (AF F) e) = inclR (Ainf F) e := by
  show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, map_one]; rfl)

private theorem prV_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) : prV v (inclR (AF F) e) = inclR (Fv F v) e := by
  show (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
      ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e)) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one, map_one]; rfl)

theorem twoStep_adelic_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∀ (ν₁ ν₂ : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν₁' ν₂' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)), IsStdX s σ J a₁ ν₁ → IsStdX s σ J₁' b₁ ν₁' → IsStdX s σ J a₂ ν₂ → IsStdX s σ J₂' b₂ ν₂' → TwoStep (AF F) σ J x₁ B₁ ν₁ ν₁' N₁ → TwoStep (AF F) σ J x₂ B₂ ν₂ ν₂' N₂ → N₂ = N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)))) := by
  intro F E _ _ _ _ _ σ hCM d b s M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ hS₁ hS₂ hb₁ hb₂ hy₁
    hy₂ hγ ν₁ ν₂ ν₁' ν₂' N₁ N₂ hν₁ hν₁' hν₂ hν₂' hN₁ hN₂
  obtain ⟨u, hu, hloc⟩ := GlobalTheory.T.twoStepMeasure_orthogonalBasis_swap_local F E σ hCM M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ
    hS₁ hS₂ hb₁ hb₂ hy₁ hy₂ hγ
  obtain ⟨mi₁, mi₁', Ni₁, mv₁, mv₁', Nv₁, hfi₁, hfi₁', hTi₁, hfv₁, hfv₁', hTv₁, hP₁⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₁ a₁ B₁ J₁' y₁ b₁ hS₁ hb₁ hy₁ ν₁ ν₁' N₁
      hν₁ hν₁' hN₁
  obtain ⟨mi₂, mi₂', Ni₂, mv₂, mv₂', Nv₂, hfi₂, hfi₂', hTi₂, hfv₂, hfv₂', hTv₂, hP₂⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₂ a₂ B₂ J₂' y₂ b₂ hS₂ hb₂ hy₂ ν₂ ν₂' N₂
      hν₂ hν₂' hN₂
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F

  have ei := hloc (Ainf F) hNi s.lamI s.nuI mi₁ mi₂ mi₁' mi₂' Ni₁ Ni₂ s.haar_lamI s.haar_nuI
    hfi₁ hfi₁' hfi₂ hfi₂' hTi₁ hTi₂
  have ev := fun v => hloc (Fv F v) (hNv v) (s.lamV v) (s.nuV v) (mv₁ v) (mv₂ v) (mv₁' v)
    (mv₂' v) (Nv₁ v) (Nv₂ v) (s.haar_lamV v) (s.haar_nuV v) (hfv₁ v) (hfv₁' v) (hfv₂ v)
    (hfv₂' v) (hTv₁ v) (hTv₂ v)

  have hmap := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 2 (M + 1) N₁ Ni₁ Nv₁ 1
    (Matrix.GeneralLinearGroup.map (inclR (AF F)) γ) hP₁
  have hγA : ((Matrix.GeneralLinearGroup.map (inclR (AF F)) γ : GL (Fin 2) (AF F ⊗[F] E)) :
      Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) = (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)) :=
    rfl
  have hγi : ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map prInf =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Ainf F)) := by
    ext i j; exact prInf_inclR_eq _
  have hγv : ∀ v, ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map (prV v) =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)) := by
    intro v; ext i j; exact prV_inclR_eq v _
  have h1i : (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map prInf = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1v : ∀ v, (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map (prV v) = 1 :=
    fun v => Matrix.map_one _ (map_zero _) (map_one _)
  rw [hγA] at hmap
  simp only [Units.val_one, h1i, h1v, hγi, hγv] at hmap

  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.product_formula_haarModulus_cmField_element F E σ hCM u hu
  have hsc := GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 2 (M + 1) _ _ _ (modu (Ainf F ⊗[F] E) (inclR (Ainf F) u))
    (fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)) hmap hfin
  simp only [hprod, one_smul] at hsc
  have hv : Nv₂ = fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) •
      (Nv₁ v).map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)))) := funext ev
  rw [← ei, ← hv] at hsc
  exact ((GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 2 (M + 1) N₂ Ni₂ Nv₂ hP₂).2.2.1 _ hsc).symm

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureOrthogonalBasesPlaneCompareStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTwoStepMeasure_orthogonalBases_plane_compare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∀ (ν₁ ν₂ : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν₁' ν₂' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)), IsStdX s σ J a₁ ν₁ → IsStdX s σ J₁' b₁ ν₁' → IsStdX s σ J a₂ ν₂ → IsStdX s σ J₂' b₂ ν₂' → TwoStep (AF F) σ J x₁ B₁ ν₁ ν₁' N₁ → TwoStep (AF F) σ J x₂ B₂ ν₂ ν₂' N₂ → N₂ = N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)))) := by
  first | exact @GlobalTheory.GaugeEx.twoStep_adelic_swap | exact GlobalTheory.GaugeEx.twoStep_adelic_swap | (intros; apply GlobalTheory.GaugeEx.twoStep_adelic_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerMeasureIndependentOfPath
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

noncomputable section

namespace GlobalTheory.GaugeSquare

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem consCol_mulVec {M : ℕ} (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E)
    (c : E) (w : Fin M → E) :
    (consCol x B) *ᵥ (Fin.cons (α := fun _ => E) c w) = c • x 0 + B *ᵥ w := by
  funext i
  simp [consCol, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

theorem decomp {M : ℕ} {x : Fin 1 → Fin (M + 1) → E} {B : Matrix (Fin (M + 1)) (Fin M) E}
    (h : (consCol x B).det ≠ 0) (v : Fin (M + 1) → E) : ∃ (c : E) (w : Fin M → E),
    v = c • x 0 + B *ᵥ w := by
  have hu : IsUnit (consCol x B).det := isUnit_iff_ne_zero.2 h
  refine ⟨((consCol x B)⁻¹ *ᵥ v) 0, Fin.tail ((consCol x B)⁻¹ *ᵥ v), ?_⟩
  rw [← consCol_mulVec, Fin.cons_self_tail, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]

theorem indep {M : ℕ} {x : Fin 1 → Fin (M + 1) → E} {B : Matrix (Fin (M + 1)) (Fin M) E}
    (h : (consCol x B).det ≠ 0) {c : E} {w : Fin M → E} (h0 : c • x 0 + B *ᵥ w = 0) :
    c = 0 ∧ w = 0 := by
  rw [← consCol_mulVec] at h0
  have := Matrix.eq_zero_of_mulVec_eq_zero h h0
  exact ⟨congrFun this 0, funext fun i => congrFun this i.succ⟩

theorem leftInv {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    {a : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
    (h : StepData σ J x a B J') : ∃ L : Matrix (Fin M) (Fin (M + 1)) E, L * B = 1 := by
  obtain ⟨-, -, -, -, h5, -, h6⟩ := h
  refine ⟨J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J), ?_⟩
  rw [Matrix.mul_assoc, ← h5, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h6)]

def rowP (σ : E →ₐ[F] E) {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (v : Fin M → E) : Fin N → E := (fun i => σ (v i)) ᵥ* (J * D)

theorem rowP_apply {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (v : Fin M → E) (j : Fin N) : rowP σ J D v j = hE σ J v (fun i => D i j) := by
  simp [rowP, hE, Formalism.UG.hform, Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem rowP_mul {M N K : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin N) E)
    (C : Matrix (Fin N) (Fin K) E) (v : Fin M → E) : rowP σ J (B * C) v = rowP σ J B v ᵥ* C := by
  simp [rowP, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rowP_mulVec {M N K : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (B : Matrix (Fin M) (Fin K) E) (w : Fin K → E) :
    rowP σ J D (B *ᵥ w) = (fun i => σ (w i)) ᵥ* (Formalism.UG.cT (σ : E →+* E) B * J * D) := by
  have : (fun i => σ ((B *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* Formalism.UG.cT (σ : E →+* E) B := by
    funext i
    simp [Formalism.UG.cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [rowP, this, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem rowPairing_add {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (v w : Fin M → E) : rowP σ J D (v + w) = rowP σ J D v + rowP σ J D w := by
  rw [rowP, rowP, rowP, ← Matrix.add_vecMul]
  congr 1
  funext i
  simp

theorem rowPairing_smul {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (D : Matrix (Fin M) (Fin N) E)
    (c : E) (v : Fin M → E) : rowP σ J D (c • v) = σ c • rowP σ J D v := by
  rw [rowP, rowP, ← Matrix.smul_vecMul]
  congr 1
  funext i
  simp

section Two

variable {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E} {x : Fin 1 → Fin (M + 1 + 1) → E}
  {a : F} {B : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E} {J₁ : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
  {y : Fin 1 → Fin (M + 1) → E} {b : F} {C : Matrix (Fin (M + 1)) (Fin M) E}
  {J₀ : Matrix (Fin M) (Fin M) E}

theorem perp_fst (h : StepData σ J x a B J₁) : rowP σ J (B * C) (x 0) = 0 := by
  have : rowP σ J B (x 0) = 0 := funext fun j => by rw [rowP_apply]; exact h.2.2.2.1 j
  rw [rowP_mul, this, Matrix.zero_vecMul]

theorem perp_snd (h : StepData σ J x a B J₁) (h' : StepData σ J₁ y b C J₀) :
    rowP σ J (B * C) (B *ᵥ y 0) = 0 := by
  have : rowP σ J₁ C (y 0) = 0 := funext fun j => by rw [rowP_apply]; exact h'.2.2.2.1 j
  rw [rowP_mulVec, ← Matrix.mul_assoc, ← h.2.2.2.2.1]
  exact this

theorem span_perp (h : StepData σ J x a B J₁) (h' : StepData σ J₁ y b C J₀)
    (hd : (consCol x B).det ≠ 0) (hd' : (consCol y C).det ≠ 0) {v : Fin (M + 1 + 1) → E}
    (hv : rowP σ J (B * C) v = 0) : ∃ c c' : E, v = c • x 0 + c' • B *ᵥ y 0 := by
  obtain ⟨c, w, rfl⟩ := decomp hd v
  obtain ⟨c', u, rfl⟩ := decomp hd' w
  refine ⟨c, c', ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at hv ⊢
  rw [rowPairing_add, rowPairing_add, rowPairing_smul, rowPairing_smul, perp_fst h, perp_snd h h', rowP_mulVec] at hv
  have e : Formalism.UG.cT (σ : E →+* E) (B * C) * J * (B * C) = J₀ := by
    rw [h'.2.2.2.2.1, h.2.2.2.2.1, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at hv
  simp only [smul_zero, zero_add] at hv
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero h'.2.2.2.2.2.2 hv
  have hu : u = 0 := funext fun i => by simpa using congrFun h0 i
  simp [hu]

theorem indep_two (h' : StepData σ J₁ y b C J₀) (hd : (consCol x B).det ≠ 0) {c c' : E}
    (h0 : c • x 0 + c' • B *ᵥ y 0 = 0) : c = 0 ∧ c' = 0 := by
  rw [← Matrix.mulVec_smul] at h0
  obtain ⟨h1, h2⟩ := indep hd h0
  refine ⟨h1, ?_⟩
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exfalso
    have h4 := h'.2.2.1
    rw [h3] at h4
    simp only [hE, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h4
    exact h'.2.1 ((map_eq_zero _).1 h4.symm)

end Two

theorem lrAct_lrAct {S : Type} [CommRing S] {n M : ℕ} (γ γ' : Matrix (Fin n) (Fin n) S)
    (X : Fin n → Fin M → S) : lrAct 1 γ' (lrAct 1 γ X) = lrAct 1 (γ * γ') X := by
  funext a i
  simp only [lrAct, Matrix.one_mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lrAct_one {S : Type} [CommRing S] {n M : ℕ} (X : Fin n → Fin M → S) : lrAct 1 1 X = X := by
  funext a i
  simp [lrAct, Matrix.one_apply]

theorem lrAct_two {M : ℕ} (γ : Matrix (Fin 2) (Fin 2) E) (u v : Fin M → E) (a : Fin 2) :
    lrAct 1 γ ![u, v] a = γ 0 a • u + γ 1 a • v := by
  funext i
  simp [lrAct, Fin.sum_univ_two, mul_comm]

theorem exists_gamma {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E}
    {x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E} {a₁ a₂ : F}
    {B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E}
    {J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {y₁ y₂ : Fin 1 → Fin (M + 1) → E} {b₁ b₂ : F}
    {C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E} {J₀ : Matrix (Fin M) (Fin M) E}
    (h₁ : StepData σ J x₁ a₁ B₁ J₁) (h₁' : StepData σ J₁ y₁ b₁ C₁ J₀)
    (h₂ : StepData σ J x₂ a₂ B₂ J₂) (h₂' : StepData σ J₂ y₂ b₂ C₂ J₀) (hBC : B₁ * C₁ = B₂ * C₂)
    (d₁ : (consCol x₁ B₁).det ≠ 0) (d₁' : (consCol y₁ C₁).det ≠ 0)
    (d₂ : (consCol x₂ B₂).det ≠ 0) :
    ∃ γ : GL (Fin 2) E, ![x₂ 0, B₂.mulVec (y₂ 0)] =
      lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] := by
  obtain ⟨p, q, hp⟩ := span_perp h₁ h₁' d₁ d₁' (v := x₂ 0) (by rw [hBC]; exact perp_fst h₂)
  obtain ⟨r, t, hr⟩ := span_perp h₁ h₁' d₁ d₁' (v := B₂ *ᵥ y₂ 0) (by rw [hBC]; exact perp_snd h₂ h₂')
  have hdet : (!![p, r; q, t] : Matrix (Fin 2) (Fin 2) E).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have e0 : p * v 0 + r * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
    have e1 : q * v 0 + t * v 1 = 0 := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
    have : v 0 • x₂ 0 + v 1 • B₂ *ᵥ y₂ 0 = 0 := by
      rw [hp, hr]
      have : v 0 • (p • x₁ 0 + q • B₁ *ᵥ y₁ 0) + v 1 • (r • x₁ 0 + t • B₁ *ᵥ y₁ 0) =
          (p * v 0 + r * v 1) • x₁ 0 + (q * v 0 + t * v 1) • B₁ *ᵥ y₁ 0 := by module
      rw [this, e0, e1]; simp
    obtain ⟨f0, f1⟩ := indep_two h₂' d₂ this
    apply hv0
    funext i
    fin_cases i
    · exact f0
    · exact f1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  funext a
  rw [lrAct_two]
  fin_cases a
  · simpa using hp
  · simpa using hr

end Alg

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

abbrev mt {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))

theorem smul_apply' {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) (a : Fin n) : (g • X) a = mt R g *ᵥ X a := rfl

theorem mt_mul {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g h : HA R σ J) :
    mt R (g * h) = mt R g * mt R h := rfl

theorem mt_inj {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {g h : HA R σ J} (e : mt R g = mt R h) :
    g = h := Subtype.ext (Units.ext e)

theorem smul_lrAct {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA R σ J)
    (γ : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    g • lrAct 1 γ X = lrAct 1 γ (g • X) := by
  funext a i
  simp only [smul_apply', lrAct, Matrix.one_mulVec]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem ratTup_lrAct {M n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (X : Fin n → Fin M → E) :
    ratTup (F := F) R (lrAct 1 γ X) = lrAct 1 (γ.map (inclR (F := F) R)) (ratTup (F := F) R X) := by
  funext a i
  simp [ratTup, lrAct]

theorem ratTup_one {M N : ℕ} (x : Fin 1 → Fin M → E) (B : Matrix (Fin M) (Fin N) E)
    (y : Fin 1 → Fin N → E) :
    ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 = B.map (inclR (F := F) R) *ᵥ ratTup (F := F) R y 0 := by
  funext i
  simp [ratTup, Matrix.mulVec, dotProduct]

theorem mem_stab {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (x : Fin 1 → Fin M → E) (g : HA R σ J) :
    g ∈ Hstab R σ J x ↔ mt R g *ᵥ ratTup (F := F) R x 0 = ratTup (F := F) R x 0 := by
  constructor
  · intro h
    exact congrFun (MulAction.mem_stabilizer_iff.1 h) 0
  · intro h
    refine MulAction.mem_stabilizer_iff.2 (funext fun a => ?_)
    rw [Subsingleton.elim a 0]
    exact h

theorem cancel_mat {M N K : ℕ} {B : Matrix (Fin M) (Fin N) E} {L : Matrix (Fin N) (Fin M) E}
    (hL : L * B = 1) {P Q : Matrix (Fin N) (Fin K) (R ⊗[F] E)}
    (h : B.map (inclR (F := F) R) * P = B.map (inclR (F := F) R) * Q) : P = Q := by
  have e : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.one_mul P, ← Matrix.one_mul Q, ← e, Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem cancel_vec {M N : ℕ} {B : Matrix (Fin M) (Fin N) E} {L : Matrix (Fin N) (Fin M) E}
    (hL : L * B = 1) {P Q : Fin N → R ⊗[F] E}
    (h : B.map (inclR (F := F) R) *ᵥ P = B.map (inclR (F := F) R) *ᵥ Q) : P = Q := by
  have e : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← Matrix.one_mulVec P, ← Matrix.one_mulVec Q, ← e, ← Matrix.mulVec_mulVec, h,
    Matrix.mulVec_mulVec]

variable {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E} {x : Fin 1 → Fin (M + 1 + 1) → E}
  {B : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E} {J₁ : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
  {y : Fin 1 → Fin (M + 1) → E} {C : Matrix (Fin (M + 1)) (Fin M) E}
  {J₀ : Matrix (Fin M) (Fin M) E}

def emb (e : Hstab R σ J x ≃* HA R σ J₁) (e' : Hstab R σ J₁ y ≃* HA R σ J₀) :
    HA R σ J₀ →* HA R σ J :=
  (Hstab R σ J x).subtype.comp (e.symm.toMonoidHom.comp
    ((Hstab R σ J₁ y).subtype.comp e'.symm.toMonoidHom))

variable {R} {e : Hstab R σ J x ≃* HA R σ J₁} {e' : Hstab R σ J₁ y ≃* HA R σ J₀}

theorem emb_apply (h : HA R σ J₀) :
    emb R e e' h = (e.symm (e'.symm h : HA R σ J₁) : HA R σ J) := rfl

theorem symm_rel (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (g : HA R σ J₁) :
    mt R (e.symm g : HA R σ J) * B.map (inclR (F := F) R) = B.map (inclR (F := F) R) * mt R g := by
  have := he (e.symm g)
  rw [e.apply_symm_apply] at this
  exact this

theorem emb_rel (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (he' : ∀ g : Hstab R σ J₁ y, FrameRelR R σ J₁ J₀ C (g : HA R σ J₁) (e' g)) (h : HA R σ J₀) :
    mt R (emb R e e' h) * (B * C).map (inclR (F := F) R) = (B * C).map (inclR (F := F) R) * mt R h := by
  have h2 := he' (e'.symm h)
  rw [e'.apply_symm_apply] at h2
  rw [emb_apply, Matrix.map_mul, ← Matrix.mul_assoc, symm_rel he, Matrix.mul_assoc, Matrix.mul_assoc]
  exact congrArg _ h2

theorem pair_eq (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (g : HA R σ J) (g' : HA R σ J₁) :
    pairOf R σ J B (g • ratTup (F := F) R x) g (g' • ratTup (F := F) R y) =
      (g * (e.symm g' : HA R σ J)) • ratTup (F := F) R ![x 0, B *ᵥ y 0] := by
  funext a
  fin_cases a
  · show mt R g *ᵥ ratTup (F := F) R x 0 = mt R (g * _) *ᵥ ratTup (F := F) R x 0
    rw [mt_mul, ← Matrix.mulVec_mulVec, (mem_stab R x _).1 (e.symm g').2]
  · show mt R g *ᵥ (B.map (inclR (F := F) R) *ᵥ (mt R g' *ᵥ ratTup (F := F) R y 0)) =
      mt R (g * _) *ᵥ ratTup (F := F) R ![x 0, B *ᵥ y 0] 1
    rw [ratTup_one, mt_mul]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [symm_rel he]

theorem emb_fix (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g))
    (h : HA R σ J₀) :
    emb R e e' h • ratTup (F := F) R ![x 0, B *ᵥ y 0] = ratTup (F := F) R ![x 0, B *ᵥ y 0] := by
  funext a
  fin_cases a
  · exact (mem_stab R x _).1 (e.symm (e'.symm h : HA R σ J₁)).2
  · show mt R (emb R e e' h) *ᵥ ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 =
      ratTup (F := F) R ![x 0, B *ᵥ y 0] 1
    rw [ratTup_one, Matrix.mulVec_mulVec, emb_apply, symm_rel he, ← Matrix.mulVec_mulVec,
      (mem_stab R y _).1 (e'.symm h).2]

theorem emb_surj {L : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) E} (hL : L * B = 1)
    (he : ∀ g : Hstab R σ J x, FrameRelR R σ J J₁ B (g : HA R σ J) (e g)) (g : HA R σ J)
    (hg : g • ratTup (F := F) R ![x 0, B *ᵥ y 0] = ratTup (F := F) R ![x 0, B *ᵥ y 0]) :
    ∃ h, emb R e e' h = g := by
  have h0 : g ∈ Hstab R σ J x := (mem_stab R x _).2 (congrFun hg 0)
  have h1 : e ⟨g, h0⟩ ∈ Hstab R σ J₁ y := by
    refine (mem_stab R y _).2 (cancel_vec R hL ?_)
    have h2 : mt R g *ᵥ ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 =
      ratTup (F := F) R ![x 0, B *ᵥ y 0] 1 := congrFun hg 1
    have h3 : mt R g * B.map (inclR (F := F) R) = B.map (inclR (F := F) R) * mt R (e ⟨g, h0⟩) := he ⟨g, h0⟩
    rw [ratTup_one, Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec] at h2
    exact h2
  refine ⟨e' ⟨_, h1⟩, ?_⟩
  rw [emb_apply, e'.symm_apply_apply, e.symm_apply_apply]

end Grp

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem exists_sec (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin M → E) : ∃ s, IsSec R σ J x s := by
  classical
  refine ⟨fun y => if h : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h.choose else 1, ?_⟩
  intro y hy
  simp only [dif_pos hy]
  exact hy.choose_spec

theorem meas_avg [FiniteDimensional F E] {M N : ℕ} {J : Matrix (Fin N) (Fin N) E}
    {J₀ : Matrix (Fin M) (Fin M) E} (μ₀ : Measure (HA (AF F) σ J₀)) [μ₀.IsHaarMeasure]
    {ι : HA (AF F) σ J₀ → HA (AF F) σ J} (hι : Continuous ι) {f : HA (AF F) σ J → ℝ≥0∞}
    (hf : Measurable f) {t : (Fin 2 → Fin N → AF F ⊗[F] E) → HA (AF F) σ J} (ht : Measurable t) :
    Measurable fun X => ∫⁻ h, f (t X * ι h) ∂μ₀ := by
  refine Measurable.lintegral_prod_right' (f := fun p : _ × _ => f (t p.1 * ι p.2)) ?_
  exact hf.comp ((ht.comp measurable_fst).mul (hι.measurable.comp measurable_snd))

theorem unfold_two [FiniteDimensional F E] {d : ℕ} {bb : Module.Basis (Fin d) F E} {s : StdMeas bb}
    {M : ℕ} {J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E} {x : Fin 1 → Fin (M + 1 + 1) → E}
    {a : F} {B : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E} {J₁ : Matrix (Fin (M + 1)) (Fin (M + 1)) E}
    {y : Fin 1 → Fin (M + 1) → E} {b : F} {C : Matrix (Fin (M + 1)) (Fin M) E}
    {J₀ : Matrix (Fin M) (Fin M) E} (h₁ : StepData σ J x a B J₁)
    {e : Hstab (AF F) σ J x ≃* HA (AF F) σ J₁} {e' : Hstab (AF F) σ J₁ y ≃* HA (AF F) σ J₀}
    (he : ∀ g : Hstab (AF F) σ J x, FrameRelR (AF F) σ J J₁ B (g : HA (AF F) σ J) (e g))
    (he' : ∀ g : Hstab (AF F) σ J₁ y, FrameRelR (AF F) σ J₁ J₀ C (g : HA (AF F) σ J₁) (e' g))
    (ce : Continuous e.symm) (ce' : Continuous e'.symm)
    {μ₀ : Measure (HA (AF F) σ J₀)} [μ₀.IsHaarMeasure] {μ₁ : Measure (HA (AF F) σ J₁)}
    {τ : Measure (HA (AF F) σ J)}
    (r' : StepRel s σ J₁ y b C J₀ μ₁ μ₀) (r : StepRel s σ J x a B J₁ τ μ₁)
    {ν : Measure (Fin 1 → Fin (M + 1 + 1) → AF F ⊗[F] E)}
    {ν' : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)}
    (hν : IsStdX s σ J a ν) (hν' : IsStdX s σ J₁ b ν')
    (oν : OnOrbit (AF F) σ J x ν) (oν' : OnOrbit (AF F) σ J₁ y ν')
    {N : Measure (Fin 2 → Fin (M + 1 + 1) → AF F ⊗[F] E)} (hN : TwoStep (AF F) σ J x B ν ν' N)
    {f : HA (AF F) σ J → ℝ≥0∞} (hf : Measurable f)
    {t : (Fin 2 → Fin (M + 1 + 1) → AF F ⊗[F] E) → HA (AF F) σ J} (ht : Measurable t)
    (hs : ∀ Y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) ![x 0, B *ᵥ y 0] = Y) →
      t Y • ratTup (F := F) (AF F) ![x 0, B *ᵥ y 0] = Y) :
    ∫⁻ g, f g ∂τ = ∫⁻ X, ∫⁻ h, f (t X * emb (AF F) e e' h) ∂μ₀ ∂N := by
  obtain ⟨L, hL⟩ := leftInv h₁
  obtain ⟨u, hu⟩ := exists_sec (σ := σ) (AF F) J x
  obtain ⟨u', hu'⟩ := exists_sec (σ := σ) (AF F) J₁ y
  have c1 : Continuous fun g : HA (AF F) σ J₁ => (e.symm g : HA (AF F) σ J) :=
    continuous_subtype_val.comp ce
  have c2 : Continuous fun g : HA (AF F) σ J₀ => (e'.symm g : HA (AF F) σ J₁) :=
    continuous_subtype_val.comp ce'
  have cι : Continuous (emb (AF F) e e') := c1.comp c2
  rw [hN _ (meas_avg μ₀ cι hf ht) u hu, r ν hν e he f hf u hu]
  refine lintegral_congr_ae ?_
  have a1 : ∀ᵐ z ∂ν, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = z := ae_iff.2 oν
  have a2 : ∀ᵐ z ∂ν', ∃ g : HA (AF F) σ J₁, g • ratTup (F := F) (AF F) y = z := ae_iff.2 oν'
  filter_upwards [a1] with z hz
  have m1 : Measurable fun h' : Hstab (AF F) σ J x => f (u z * (h' : HA (AF F) σ J)) :=
    hf.comp (measurable_subtype_coe.const_mul _)
  have m2 : Measurable fun g : HA (AF F) σ J₁ => f (u z * (e.symm g : HA (AF F) σ J)) :=
    hf.comp (c1.measurable.const_mul _)
  rw [lintegral_map m1 ce.measurable, r' ν' hν' e' he' _ m2 u' hu']
  refine lintegral_congr_ae ?_
  filter_upwards [a2] with z' hz'
  have m3 : Measurable fun h' : Hstab (AF F) σ J₁ y =>
      f (u z * (e.symm (u' z' * (h' : HA (AF F) σ J₁)) : HA (AF F) σ J)) :=
    m2.comp (measurable_subtype_coe.const_mul _)
  rw [lintegral_map m3 ce'.measurable]
  have hp : pairOf (AF F) σ J B z (u z) z' =
      (u z * (e.symm (u' z') : HA (AF F) σ J)) • ratTup (F := F) (AF F) ![x 0, B *ᵥ y 0] := by
    rw [← pair_eq he, hu z hz, hu' z' hz']
  set g := u z * (e.symm (u' z') : HA (AF F) σ J) with hg
  have h3 := hs _ ⟨g, hp.symm⟩
  obtain ⟨h₀, hh₀⟩ := emb_surj (e' := e') hL he (g⁻¹ * t (pairOf (AF F) σ J B z (u z) z'))
    (by rw [mul_smul, h3, hp, inv_smul_smul])
  have h4 : t (pairOf (AF F) σ J B z (u z) z') = g * emb (AF F) e e' h₀ := by
    rw [hh₀, mul_inv_cancel_left]
  rw [h4, ← lintegral_mul_left_eq_self _ h₀]
  refine lintegral_congr fun h => ?_
  simp only [hg, emb_apply, map_mul, Subgroup.coe_mul, mul_assoc]

theorem square : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E) (μ₀ : Measure (HA (AF F) σ J₀)) (μ₁ : Measure (HA (AF F) σ J₁)) (μ₂ : Measure (HA (AF F) σ J₂)) (τ₁ τ₂ : Measure (HA (AF F) σ J)), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → μ₀.IsHaarMeasure → StepRel s σ J₁ y₁ b₁ C₁ J₀ μ₁ μ₀ → StepRel s σ J x₁ a₁ B₁ J₁ τ₁ μ₁ → StepRel s σ J₂ y₂ b₂ C₂ J₀ μ₂ μ₀ → StepRel s σ J x₂ a₂ B₂ J₂ τ₂ μ₂ → τ₁ = τ₂ := by
  intro F E _ _ _ _ _ σ hσ d b s M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ μ₀ μ₁ μ₂ τ₁ τ₂ hM
    h₁ h₁' h₂ h₂' hBC hμ r₁' r₁ r₂' r₂
  obtain ⟨d₁, ⟨e₁, he₁, -⟩, c₁⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J x₁ a₁ B₁ J₁ h₁
  obtain ⟨d₁', ⟨e₁', he₁', -⟩, c₁'⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J₁ y₁ b₁ C₁ J₀ h₁'
  obtain ⟨d₂, ⟨e₂, he₂, -⟩, c₂⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J x₂ a₂ B₂ J₂ h₂
  obtain ⟨d₂', ⟨e₂', he₂', -⟩, c₂'⟩ := GlobalTheory.FrameStep.frameStep F E σ hσ (AF F) _ J₂ y₂ b₂ C₂ J₀ h₂'
  obtain ⟨ν₁, n₁, -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J a₁ (by omega) h₁.1 h₁.2.1
  obtain ⟨ν₁', n₁', -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J₁ b₁ (by omega) h₁'.1 h₁'.2.1
  obtain ⟨ν₂, n₂, -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J a₂ (by omega) h₂.1 h₂.2.1
  obtain ⟨ν₂', n₂', -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ d b s _ J₂ b₂ (by omega) h₂'.1 h₂'.2.1
  obtain ⟨-, -, o₁, f₁, -⟩ := GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J x₁ a₁ ν₁ h₁.1 h₁.2.1 h₁.2.2.1 n₁
  obtain ⟨-, i₁', o₁', f₁', -⟩ :=
    GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J₁ y₁ b₁ ν₁' h₁'.1 h₁'.2.1 h₁'.2.2.1 n₁'
  obtain ⟨-, -, o₂, f₂, -⟩ := GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J x₂ a₂ ν₂ h₂.1 h₂.2.1 h₂.2.2.1 n₂
  obtain ⟨-, i₂', o₂', f₂', -⟩ :=
    GlobalTheory.T.stdHermitianFibreMeasure_invariant_orbit_finite_nonzero F E σ hσ d b s _ J₂ y₂ b₂ ν₂' h₂'.1 h₂'.2.1 h₂'.2.2.1 n₂'
  obtain ⟨N₁, t₁, -⟩ := GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hσ (AF F) _ J x₁ a₁ B₁ J₁ ν₁ ν₁' h₁ o₁ f₁ f₁' i₁'
  obtain ⟨N₂, t₂, -⟩ := GlobalTheory.T.existsUnique_unitaryTwoStepPairMeasure F E σ hσ (AF F) _ J x₂ a₂ B₂ J₂ ν₂ ν₂' h₂ o₂ f₂ f₂' i₂'
  obtain ⟨γ, hγ⟩ := exists_gamma h₁ h₁' h₂ h₂' hBC d₁ d₁' d₂
  have hN := GlobalTheory.T.adelicTwoStepMeasure_orthogonalBases_plane_compare F E σ hσ d b s _ J x₁ a₁ B₁ J₁ x₂ a₂ B₂ J₂ y₁ y₂ b₁ b₂ γ h₁ h₂ h₁'.2.1
    h₂'.2.1 h₁'.2.2.1 h₂'.2.2.1 hγ ν₁ ν₂ ν₁' ν₂' N₁ N₂ n₁ n₁' n₂ n₂' t₁ t₂
  set G : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E) :=
    (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) (AF F)) with hG
  set G' : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E) :=
    ((γ⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) (AF F)) with hG'
  have g1 : G * G' = 1 := by
    rw [hG, hG', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have g2 : G' * G = 1 := by
    rw [hG, hG', ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : ratTup (F := F) (AF F) ![x₂ 0, B₂ *ᵥ y₂ 0] =
      lrAct 1 G (ratTup (F := F) (AF F) ![x₁ 0, B₁ *ᵥ y₁ 0]) := by
    rw [hγ, ratTup_lrAct]
  have cG : ∀ P : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E),
      Measurable (lrAct (M := M + 1 + 1) 1 P) := by
    intro P
    refine Continuous.measurable (continuous_pi fun a => continuous_pi fun i => ?_)
    simp only [lrAct, Matrix.one_mulVec]
    fun_prop
  have hι : ∀ h, emb (AF F) e₂ e₂' h = emb (AF F) e₁ e₁' h := by
    intro h
    obtain ⟨L, hL⟩ := leftInv h₁
    obtain ⟨L', hL'⟩ := leftInv h₁'
    have k1 := emb_fix (e' := e₂') he₂ h
    rw [hX, smul_lrAct] at k1
    have k2 := congrArg (lrAct 1 G') k1
    rw [lrAct_lrAct, lrAct_lrAct, g1, lrAct_one, lrAct_one] at k2
    obtain ⟨h', hh'⟩ := emb_surj (e' := e₁') hL he₁ _ k2
    have k3 := emb_rel he₁ he₁' h'
    have k4 := emb_rel he₂ he₂' h
    rw [← hBC, ← hh', k3] at k4
    have hLL : (L' * L) * (B₁ * C₁) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, hL']
    rw [← hh', mt_inj _ (cancel_mat _ hLL k4)]
  obtain ⟨-, t, mt₁, ht⟩ := GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section (HA (AF F) σ J) (Fin 2 → Fin (M + 1 + 1) → AF F ⊗[F] E)
    (ratTup (F := F) (AF F) ![x₁ 0, B₁ *ᵥ y₁ 0])
  have mt₂ : Measurable fun Y => t (lrAct 1 G' Y) := mt₁.comp (cG G')
  have ht₂ : ∀ Y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) ![x₂ 0, B₂ *ᵥ y₂ 0] = Y) →
      t (lrAct 1 G' Y) • ratTup (F := F) (AF F) ![x₂ 0, B₂ *ᵥ y₂ 0] = Y := by
    rintro Y ⟨g, rfl⟩
    rw [hX, smul_lrAct, smul_lrAct, lrAct_lrAct, g1, lrAct_one, ht _ ⟨g, rfl⟩]
  have cι : Continuous (emb (AF F) e₂ e₂') :=
    (continuous_subtype_val.comp (c₂ e₂ he₂).2).comp (continuous_subtype_val.comp (c₂' e₂' he₂').2)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [unfold_two h₁ he₁ he₁' (c₁ e₁ he₁).2 (c₁' e₁' he₁').2 r₁' r₁ n₁ n₁' o₁ o₁' t₁ hf mt₁ ht,
    unfold_two h₂ he₂ he₂' (c₂ e₂ he₂).2 (c₂' e₂' he₂').2 r₂' r₂ n₂ n₂' o₂ o₂' t₂ hf mt₂ ht₂,
    hN, lintegral_map (meas_avg μ₀ cι hf mt₂) (cG G)]
  simp only [lrAct_lrAct, g1, lrAct_one, hι]

end Main

end GlobalTheory.GaugeSquare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerMeasureIndependentOfPathStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryStabilizer_measure_independent_of_path : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E) (μ₀ : Measure (HA (AF F) σ J₀)) (μ₁ : Measure (HA (AF F) σ J₁)) (μ₂ : Measure (HA (AF F) σ J₂)) (τ₁ τ₂ : Measure (HA (AF F) σ J)), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → μ₀.IsHaarMeasure → StepRel s σ J₁ y₁ b₁ C₁ J₀ μ₁ μ₀ → StepRel s σ J x₁ a₁ B₁ J₁ τ₁ μ₁ → StepRel s σ J₂ y₂ b₂ C₂ J₀ μ₂ μ₀ → StepRel s σ J x₂ a₂ B₂ J₂ τ₂ μ₂ → τ₁ = τ₂ := by
  first | exact @GlobalTheory.GaugeSquare.square | exact GlobalTheory.GaugeSquare.square | (intros; apply GlobalTheory.GaugeSquare.square <;> assumption)
end
