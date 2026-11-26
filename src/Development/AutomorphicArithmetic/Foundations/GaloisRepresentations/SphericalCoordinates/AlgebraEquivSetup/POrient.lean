module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E]

def ev1 (σ : E →+* ℂ) : ℝ ⊗[ℚ] E →ₐ[ℝ] ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ ℂ) σ.toRatAlgHom (fun _ _ => Commute.all _ _)

def evM {n : ℕ} (σ : E →+* ℂ) : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (σ.mapMatrix).toRatAlgHom
    (fun x _ => Algebra.commute_algebraMap_left x _)

theorem realTensorEvalAlgHom_tmul (σ : E →+* ℂ) (r : ℝ) (x : E) : ev1 σ (r ⊗ₜ x) = r • σ x := by
  simp [ev1, Algebra.ofId_apply, Algebra.smul_def]

theorem evM_tmul {n : ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Matrix (Fin n) (Fin n) E) :
    evM σ (r ⊗ₜ x) = r • x.map σ := by
  unfold evM
  refine (Algebra.TensorProduct.lift_tmul _ _ _ r x).trans ?_
  rw [Algebra.smul_def]
  rfl

theorem evM_conj {n : ℕ} (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    evM (ComplexEmbedding.conjugate σ) z = (evM σ z).map (starRingEnd ℂ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [evM_tmul, evM_tmul]
    ext i j
    simp [ComplexEmbedding.conjugate_coe_eq]
  | add a b ha hb => rw [map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (map_add _)]

def Th {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V] (β : V →ₗ[ℚ] (Fin n → E)) :
    ℝ ⊗[ℚ] V →ₗ[ℝ] (K × Fin n → ℂ) :=
  LinearMap.liftBaseChange ℝ
    { toFun := fun w k => f k.1 (β w k.2)
      map_add' := fun a b => by ext k; simp
      map_smul' := fun q a => by ext k; simp [map_rat_smul] }

theorem Th_tmul {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (r : ℝ) (w : V) (k : K × Fin n) :
    Th f β (r ⊗ₜ w) k = r • f k.1 (β w k.2) := by
  simp [Th]

private theorem th_actOn_tmul_eq_evM_mulVec {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (r s : ℝ) (m : Matrix (Fin n) (Fin n) E) (w : V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w)) (τ, i) = (evM (f τ) (r ⊗ₜ m) *ᵥ fun j => Th f β (s ⊗ₜ w) (τ, j)) i := by
  have hl : actOn rep ℝ (r ⊗ₜ m) = algebraMap ℝ _ r * (Module.End.baseChangeHom ℚ ℝ V) (rep m) := by
    unfold actOn
    exact Algebra.TensorProduct.lift_tmul _ _ _ r m
  have ha : actOn rep ℝ (r ⊗ₜ m) (s ⊗ₜ w) = (r * s) ⊗ₜ rep m w := by
    rw [hl, Module.End.mul_apply, Module.algebraMap_end_apply]
    show r • LinearMap.baseChange ℝ (rep m) (s ⊗ₜ w) = _
    rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  rw [ha, Th_tmul, evM_tmul, hβ]
  simp only [Th_tmul]
  rw [RingHom.map_mulVec]
  simp [Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem Th_act {K : Type} (f : K → (E →+* ℂ)) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℚ V]
    (β : V →ₗ[ℚ] (Fin n → E)) (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V)
    (hβ : ∀ x z, β (rep x z) = x *ᵥ β z) (y : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) (x : ℝ ⊗[ℚ] V) (τ : K) (i : Fin n) :
    Th f β (actOn rep ℝ y x) (τ, i) = (evM (f τ) y *ᵥ fun j => Th f β x (τ, j)) i := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    induction x using TensorProduct.induction_on with
    | zero =>
      simp
      exact (congrFun (Matrix.mulVec_zero _) i).symm
    | tmul s w => exact th_actOn_tmul_eq_evM_mulVec f β rep hβ r s m w τ i
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply, ha, hb]
      have : (fun j => Th f β (a + b) (τ, j)) = (fun j => Th f β a (τ, j)) + (fun j => Th f β b (τ, j)) := by
        ext j
        simp
      rw [this, Matrix.mulVec_add, Pi.add_apply]
  | add c d hc hd =>
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), Pi.add_apply, hc, hd, map_add (f := _), Matrix.add_mulVec, Pi.add_apply]

variable [IsCMField E]

theorem evM_star {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (hH : (H.map (IsCMField.complexConj E : E →+* E))ᵀ = H)
    (hdet : H.det ≠ 0) (σ : E →+* ℂ) (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    gramAt H σ * evM σ (starT (hermStar H hdet) ℝ z).unop = (evM σ z)ᴴ * gramAt H σ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) E,
      (M.map (IsCMField.complexConj E : E →+* E)).map σ = (M.map σ).map (starRingEnd ℂ) := by
    intro M
    ext i j
    simp [IsCMField.complexEmbedding_complexConj]
  have hHc : (H.map (IsCMField.complexConj E : E →+* E)).map σ = gramAt H σ := by
    have h1 := congrArg Matrix.transpose hH
    rw [Matrix.transpose_transpose] at h1
    rw [h1, gramAt, Matrix.transpose_map]
  have hu : IsUnit (H.map (IsCMField.complexConj E : E →+* E)).det := by
    rw [show (H.map (IsCMField.complexConj E : E →+* E)).det = (IsCMField.complexConj E : E →+* E) H.det from
      (RingHom.map_det _ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  have hG : IsUnit (gramAt H σ).det := by
    rw [gramAt, Matrix.det_transpose, show (H.map σ).det = σ H.det from (RingHom.map_det σ H).symm]
    exact ((map_ne_zero _).mpr hdet).isUnit
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, hermStar_apply, evM_tmul, evM_tmul, Matrix.map_mul, Matrix.map_mul,
      map_nonsingInv σ hu, hHc, Matrix.transpose_map, hc x, Matrix.conjTranspose_smul]
    have hx : ((x.map σ).map (starRingEnd ℂ))ᵀ = (x.map σ)ᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [hx, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_mul, star_trivial, Matrix.smul_mul]
  | add a b ha hb =>
    rw [map_add (f := _), MulOpposite.unop_add, map_add (f := _), map_add (f := _), Matrix.mul_add, ha, hb,
      Matrix.conjTranspose_add, Matrix.add_mul]

theorem term_pos (D h z : ℂ) (hD : D.re = 0) (hD' : D.im < 0) (hi : h.im = 0) (hr : h.re ≠ 0) :
    0 ≤ (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re ∧
    (z ≠ 0 → 0 < (D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z).re) := by
  have hz : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have e : D * h * ((if 0 < h.re then Complex.I else -Complex.I) * z) * (starRingEnd ℂ) z =
      D * h * (if 0 < h.re then Complex.I else -Complex.I) * (Complex.normSq z : ℂ) := by
    rw [← hz]
    ring
  rw [e]
  have hc : (D * h * (if 0 < h.re then Complex.I else -Complex.I)).re = |D.im| * |h.re| := by
    split_ifs with hp
    · simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_pos hp]
      ring
    · have hn : h.re < 0 := lt_of_le_of_ne (not_lt.mp hp) hr
      simp [Complex.mul_re, Complex.mul_im, hD, hi]
      rw [abs_of_neg hD', abs_of_neg hn]
      ring
  have hpos : 0 < |D.im| * |h.re| := mul_pos (abs_pos.mpr hD'.ne) (abs_pos.mpr hr)
  rw [Complex.re_mul_ofReal, hc]
  refine ⟨mul_nonneg hpos.le (Complex.normSq_nonneg z), fun hz0 => ?_⟩
  exact mul_pos hpos (Complex.normSq_pos.mpr hz0)

end UpperTheory.Gal.W2.Seed.Ori
end
end

section -- merged from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorBijectiveCmType
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private theorem func_repr {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℂ) →ₗ[ℝ] ℝ) :
    ∃ a : ι → ℂ, ∀ z, f z = ∑ τ, (a τ * z τ).re := by
  refine ⟨fun τ => (f (Pi.single τ 1) : ℂ) - Complex.I * (f (Pi.single τ Complex.I) : ℂ), fun z => ?_⟩
  have h1 : z = ∑ τ, ((z τ).re • (Pi.single τ 1 : ι → ℂ) + (z τ).im • (Pi.single τ Complex.I : ι → ℂ)) := by
    ext k
    have hk : ∀ τ, ((z τ).re • (Pi.single τ 1 : ι → ℂ) + (z τ).im • (Pi.single τ Complex.I : ι → ℂ)) k =
        if k = τ then z k else 0 := by
      intro τ
      by_cases h : k = τ
      · subst h
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, if_true]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, h]
    rw [Finset.sum_apply]
    simp only [hk]
    simp
  conv_lhs => rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_add (f := _), map_smul, map_smul]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

private theorem family_inj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E)
    (him : (A.τ₀ (A.ω : E)).im ≠ 0) :
    Function.Injective (Sum.elim (fun τ : Phi A => (τ.1 : E →* ℂ))
      (fun τ : Phi A => ((ComplexEmbedding.conjugate τ.1 : E →+* ℂ) : E →* ℂ))) := by
  have hval : ∀ (τ τ' : Phi A), (∀ x, τ.1 x = (starRingEnd ℂ) (τ'.1 x)) → False := by
    intro τ τ' h
    have h1 := h (A.ω : E)
    rw [τ.2, τ'.2] at h1
    exact him (Complex.conj_eq_iff_im.1 h1.symm)
  rintro (τ | τ) (τ' | τ') h
  · congr 1
    apply Subtype.ext
    ext x
    exact congrArg (fun g : E →* ℂ => g x) h
  · exfalso
    refine hval τ τ' fun x => ?_
    exact congrArg (fun g : E →* ℂ => g x) h
  · exfalso
    refine hval τ' τ fun x => ?_
    exact (congrArg (fun g : E →* ℂ => g x) h).symm
  · congr 1
    apply Subtype.ext
    ext x
    have h1 : (starRingEnd ℂ) (τ.1 x) = (starRingEnd ℂ) (τ'.1 x) := congrArg (fun g : E →* ℂ => g x) h
    exact (starRingEnd ℂ).injective h1

theorem UpperTheory.cmField_real_tensor_bijective_cmType :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E), Function.Bijective (fun (z : ℝ ⊗[ℚ] E) (τ : Phi A) => ev1 τ.1 z) := by
  intro hT E _ _ _ A
  classical
  obtain ⟨-, -, h3, him⟩ := hT E A
  haveI : Fintype (Phi A) := Fintype.ofFinite _
  let L : ℝ ⊗[ℚ] E →ₗ[ℝ] (Phi A → ℂ) := LinearMap.pi (fun τ => (ev1 τ.1).toLinearMap)
  have hL : ∀ z τ, L z τ = ev1 τ.1 z := fun _ _ => rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := (LinearMap.range L).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    obtain ⟨a, ha⟩ := func_repr f
    have hzero : ∀ x : E, ∑ τ : Phi A, (a τ * τ.1 x).re = 0 := by
      intro x
      have h1 : f (L ((1 : ℝ) ⊗ₜ x)) = 0 := LinearMap.mem_ker.1 (hf ⟨_, rfl⟩)
      rw [ha] at h1
      simpa [hL, realTensorEvalAlgHom_tmul] using h1
    have hli := (linearIndependent_monoidHom E ℂ).comp _ (family_inj A him)
    have hc := Fintype.linearIndependent_iff.1 hli
      (Sum.elim a (fun τ => (starRingEnd ℂ) (a τ))) (by
        ext x
        rw [Finset.sum_apply, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Function.comp, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have h2 : ∀ τ : Phi A, a τ * τ.1 x + (starRingEnd ℂ) (a τ) * (starRingEnd ℂ) (τ.1 x) =
            ((2 * (a τ * τ.1 x).re : ℝ) : ℂ) := by
          intro τ
          rw [← map_mul, Complex.add_conj]
        have h3 : ∑ τ : Phi A, (a τ * τ.1 x + (starRingEnd ℂ) (a τ) * (starRingEnd ℂ) (τ.1 x)) = 0 := by
          simp only [h2]
          rw [← Complex.ofReal_sum, ← Finset.mul_sum, hzero]
          simp
        rw [← h3, Finset.sum_add_distrib]
        rfl)
    apply hf0
    refine LinearMap.ext fun z => ?_
    rw [ha]
    have h0 : ∀ τ, a τ = 0 := fun τ => hc (Sum.inl τ)
    simp [h0]
  have hcard : Fintype.card (Phi A) = Fintype.card (InfinitePlace E) :=
    Fintype.card_congr (Equiv.ofBijective (fun τ : Phi A => InfinitePlace.mk τ.1)
      ⟨fun τ τ' h => (h3 _).unique rfl h.symm, fun v => (h3 v).exists⟩)
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] E) = Module.finrank ℝ (Phi A → ℂ) := by
    rw [Module.finrank_baseChange, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hcard, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← InfinitePlace.card_add_two_mul_card_eq_rank, IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩
end

section -- merged from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmTypeTraceEmbeddingInjectiveOfLinearEquiv
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

theorem UpperTheory.cmType_trace_embedding_injective_of_linearEquiv :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (β : V ≃ₗ[ℚ] (Fin n → E)), Function.Injective (Th (fun τ : Phi A => τ.1) (β : V →ₗ[ℚ] (Fin n → E))) := by
  intro hT E _ _ _ A n V _ _ β z z' h
  have hb := (UpperTheory.cmField_real_tensor_bijective_cmType hT A).1
  set B : V →ₗ[ℚ] (Fin n → E) := (β : V →ₗ[ℚ] (Fin n → E)) with hBdef
  have key : ∀ j (y : ℝ ⊗[ℚ] V) (τ : Phi A), Th (fun τ : Phi A => τ.1) B y (τ, j) =
      ev1 τ.1 ((LinearMap.proj j ∘ₗ B).baseChange ℝ y) := by
    intro j y τ
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      rw [Th_tmul, LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul]
      rfl
    | add a b ha hb' =>
      rw [map_add (f := _), Pi.add_apply, ha, hb', map_add (f := _), map_add (f := _)]
  have hj : ∀ j, (LinearMap.proj j ∘ₗ B).baseChange ℝ z = (LinearMap.proj j ∘ₗ B).baseChange ℝ z' := by
    intro j
    apply hb
    funext τ
    simp only
    rw [← key, ← key, h]
  have hsum : ∀ y : ℝ ⊗[ℚ] (Fin n → E), y = ∑ j, (LinearMap.single ℚ (fun _ : Fin n => E) j).baseChange ℝ
      ((LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r v =>
      simp only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sum]
      congr 1
      simp [Finset.univ_sum_single v]
    | add a b ha hb' =>
      conv_lhs => rw [ha, hb']
      simp only [map_add (f := _), ← Finset.sum_add_distrib]
  have hc : ∀ j (y : ℝ ⊗[ℚ] V), (LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ (B.baseChange ℝ y) =
      (LinearMap.proj j ∘ₗ B).baseChange ℝ y := by
    intro j y
    rw [LinearMap.baseChange_comp]
    rfl
  have hB : B.baseChange ℝ z = B.baseChange ℝ z' := by
    rw [hsum (B.baseChange ℝ z), hsum (B.baseChange ℝ z')]
    simp only [hc, hj]
  have hid : ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ).comp (B.baseChange ℝ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hBdef, LinearEquiv.symm_comp, LinearMap.baseChange_id]
  have hl : ∀ x, ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ) (B.baseChange ℝ x) = x :=
    fun x => LinearMap.congr_fun hid x
  rw [← hl z, ← hl z', hB]
end

section -- merged from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorMatrixBijectiveCmType
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private noncomputable def entL {E : Type} [Field E] [NumberField E] {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) E →ₗ[ℚ] E where
  toFun x := x i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def sgL {E : Type} [Field E] [NumberField E] {n : ℕ} (i j : Fin n) :
    E →ₗ[ℚ] Matrix (Fin n) (Fin n) E where
  toFun x := Matrix.single i j x
  map_add' a b := by simp [Matrix.single_add]
  map_smul' q a := by simp [Matrix.smul_single]

private theorem evaluation_baseChange_entry {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* ℂ) (i j : Fin n)
    (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    ev1 σ ((entL i j).baseChange ℝ z) = evM σ z i j := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]
    change r • σ (x i j) = _
    simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Matrix.add_apply]

private theorem evM_sg {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* ℂ) (i j : Fin n)
    (w : ℝ ⊗[ℚ] E) :
    evM σ ((sgL i j).baseChange ℝ w) = Matrix.single i j (ev1 σ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul, evM_tmul]
    ext a b
    simp [sgL, Matrix.single_apply]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.single_add]

private theorem sum_sg_ent {E : Type} [Field E] [NumberField E] {n : ℕ}
    (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) :
    z = ∑ i, ∑ j, (sgL i j).baseChange ℝ ((entL i j).baseChange ℝ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp [TensorProduct.tmul_sum, entL, sgL]
    rfl
  | add a b ha hb =>
    conv_lhs => rw [ha, hb]
    simp only [map_add (f := _), ← Finset.sum_add_distrib]

theorem UpperTheory.cmField_real_tensor_matrix_bijective_cmType :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Function.Bijective (fun (z : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E) (τ : Phi A) => evM τ.1 z) := by
  intro hT E _ _ _ A n
  have hb := UpperTheory.cmField_real_tensor_bijective_cmType hT A
  constructor
  · intro z₁ z₂ h
    have hent : ∀ i j, (entL i j).baseChange ℝ z₁ = (entL (E := E) i j).baseChange ℝ z₂ := by
      intro i j
      apply hb.1
      funext τ
      have := congrFun h τ
      simp only at this ⊢
      rw [evaluation_baseChange_entry, evaluation_baseChange_entry, this]
    rw [sum_sg_ent z₁, sum_sg_ent z₂]
    simp only [hent]
  · intro f
    choose w hw using fun i j => hb.2 (fun τ => f τ i j)
    refine ⟨∑ i, ∑ j, (sgL i j).baseChange ℝ (w i j), ?_⟩
    funext τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, evM_sg]
    have hw' : ∀ i j, ev1 τ.1 (w i j) = f τ i j := fun i j => congrFun (hw i j) τ
    simp only [hw']
    exact (Matrix.matrix_eq_sum_single (f τ)).symm
end

section -- merged from Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldHermitianFormBaseChangeRealEqSum
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private noncomputable def R {K : Type} [Fintype K] (c u v : K → ℂ) : ℝ :=
  ∑ k, 2 * (c k * u k * (starRingEnd ℂ) (v k)).re

private theorem R_add_l {K : Type} [Fintype K] (c u u' v : K → ℂ) :
    R c (u + u') v = R c u v + R c u' v := by
  unfold R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, mul_add, add_mul, Complex.add_re]

private theorem R_add_r {K : Type} [Fintype K] (c u v v' : K → ℂ) :
    R c u (v + v') = R c u v + R c u v' := by
  unfold R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, map_add (f := _), mul_add, add_mul, Complex.add_re]

private theorem R_smul_l {K : Type} [Fintype K] (c u v : K → ℂ) (r : ℝ) :
    R c (r • u) v = r * R c u v := by
  simp only [R, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : c k * (r • u) k * (starRingEnd ℂ) (v k) = (r : ℂ) * (c k * u k * (starRingEnd ℂ) (v k)) := by
    simp only [Pi.smul_apply, Complex.real_smul]; ring
  rw [h, Complex.re_ofReal_mul]; ring

private theorem R_smul_r {K : Type} [Fintype K] (c u v : K → ℂ) (r : ℝ) :
    R c u (r • v) = r * R c u v := by
  simp only [R, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : c k * u k * (starRingEnd ℂ) ((r • v) k) = (r : ℂ) * (c k * u k * (starRingEnd ℂ) (v k)) := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
  rw [h, Complex.re_ofReal_mul]; ring

private theorem core0 (hT : TraceType) {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (a b : Fin n → 𝓞 E) :
    ((A.EF n a b : ℤ) : ℝ) = ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
      (starRingEnd ℂ) (k.1.1 (b k.2 : E))).re := by
  rw [Arith.EF_apply, ← Rat.cast_intCast, Arith.trd_spec, (hT E A).1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum, ← Complex.re_sum]
  congr 2
  push_cast
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Arith.bar_eq, Finset.mul_sum, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem e1 {E : Type} [Field E] [NumberField E] {n : ℕ} (q : ℚ) (a : Fin n → 𝓞 E) :
    (1 : ℝ) ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] a) = (q : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] a)) := by
  rw [show (q ⊗ₜ[ℤ] a : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) = q • ((1 : ℚ) ⊗ₜ[ℤ] a) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Rat.smul_one_eq_cast]

private theorem core1 (hT : TraceType) {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] (Fin n → E)) (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (w w' : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    (((A.EF n).baseChange ℚ w w' : ℚ) : ℝ) =
      R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
        (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ w)) (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ w')) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [R]
  | add a b ha hb =>
    rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), LinearMap.add_apply, Rat.cast_add, ha, hb, R_add_l]
  | tmul q a =>
    induction w' using TensorProduct.induction_on with
    | zero => simp [R]
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), Rat.cast_add, ha, hb, R_add_r]
    | tmul t b =>
      rw [LinearMap.BilinForm.baseChange_tmul, e1 q a, e1 t b, map_smul, map_smul, R_smul_l, R_smul_r]
      have h : R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
          (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ ((1 : ℚ) ⊗ₜ a)))
          (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ ((1 : ℚ) ⊗ₜ b))) = ((A.EF n a b : ℤ) : ℝ) := by
        rw [core0 hT A n a b]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Th_tmul, one_smul, hβ]
      rw [h]
      simp [Rat.smul_def, zsmul_eq_mul]
      ring

theorem UpperTheory.cmField_hermitianForm_baseChange_real_eq_sum :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] (Fin n → E)), (∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) → ∀ x y : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)), ((A.EF n).baseChange ℚ).baseChange ℝ x y = ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Th (fun τ : Phi A => τ.1) β x k * (starRingEnd ℂ) (Th (fun τ : Phi A => τ.1) β y k)).re := by
  intro hT E _ _ _ A n β hβ x y
  change _ = R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
    (Th (fun τ : Phi A => τ.1) β x) (Th (fun τ : Phi A => τ.1) β y)
  induction x using TensorProduct.induction_on with
  | zero => simp [R]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, ha, hb, R_add_l]
  | tmul r w =>
    induction y using TensorProduct.induction_on with
    | zero => simp [R]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, R_add_r]
    | tmul s w' =>
      have e : ∀ (r : ℝ) (w : ℚ ⊗[ℤ] (Fin n → 𝓞 E)), r ⊗ₜ[ℚ] w = r • ((1 : ℝ) ⊗ₜ[ℚ] w) := by
        intro r w
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.BilinForm.baseChange_tmul, e r w, e s w', map_smul, map_smul, R_smul_l, R_smul_r, ← core1 hT A n β hβ w w',
        Rat.smul_def]
      simp only [mul_comm, mul_left_comm, mul_assoc]
end

noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def dv (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : ℂ :=
  if 0 < (σ (A.hd n i : E)).re then Complex.I else -Complex.I

private theorem hd_ne (hS : HdSign) (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : (σ (A.hd n i : E)).re ≠ 0 := by
  obtain ⟨-, -, h1, h2⟩ := hS E A n σ i
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0
  · exact (h1 h).ne'
  · exact (h2 h).ne

private theorem dv_sq (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : dv A n σ i * dv A n σ i = -1 := by
  unfold dv; split_ifs <;> simp

private theorem dv_conj (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) :
    (starRingEnd ℂ) (dv A n σ i) = -dv A n σ i := by
  unfold dv; split_ifs <;> simp

private theorem gram_diag (A : Arith E) (n : ℕ) (σ : E →+* ℂ) :
    gramAt (A.H n) σ = Matrix.diagonal fun i => σ (A.hd n i : E) := by
  ext i j
  simp only [gramAt, Arith.H, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem real_abs (h : ℂ) (hi : h.im = 0) (hr : h.re ≠ 0) :
    -Complex.I * (h * (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) ∧
    Complex.I * (h * (starRingEnd ℂ) (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) := by
  have hh : h = ((h.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
  split_ifs with hp
  · rw [abs_of_pos hp]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hp) hr)]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp

open scoped ComplexOrder in
private theorem posDiag {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (Matrix.diagonal fun i => ((a i : ℝ) : ℂ)).PosDef := by
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact Complex.zero_lt_real.mpr (ha i)

open scoped Classical ComplexOrder in
private theorem orient_core (hT : TraceType) (hS : HdSign) (A : Arith E) (n : ℕ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) (hrep : RepOK A n rep) :
    ∃ J : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E, J * J = -1 ∧
      (starT (hermStar (A.H n) (A.det_ne n)) ℝ J).unop = -J ∧
      (∀ x, x ≠ 0 → 0 < ((A.EF n).baseChange ℚ).baseChange ℝ (actOn rep ℝ J x) x) ∧
      ∀ v : InfinitePlace E, ((if v.embedding (A.ω : E) = A.τ₀ (A.ω : E) then -Complex.I else Complex.I) •
        (gramAt (A.H n) v.embedding * evM v.embedding J)).PosDef := by
  obtain ⟨J, hJ⟩ := (cmField_real_tensor_matrix_bijective_cmType hT A n).2 (fun τ : Phi A => Matrix.diagonal (dv A n τ.1))
  have hJτ : ∀ τ : Phi A, evM τ.1 J = Matrix.diagonal (dv A n τ.1) := fun τ => congrFun hJ τ
  have hne : ∀ (σ : E →+* ℂ) (i : Fin n), σ (A.hd n i : E) ≠ 0 := fun σ i h0 =>
    hd_ne hS A n σ i (by rw [h0]; simp)
  obtain ⟨β, hβ1, hβ2⟩ := hrep
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    rw [map_mul, map_neg, map_one, hJτ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [dv_sq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    have key := evM_star (A.H n) (A.herm n) (A.det_ne n) τ.1 J
    rw [gram_diag, hJτ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at key
    rw [map_neg, hJτ]
    ext i j
    have hk := congrFun (congrFun key i) j
    rw [Matrix.diagonal_mul] at hk
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.neg_apply] at hk ⊢
      apply mul_left_cancel₀ (hne τ.1 i)
      rw [hk, Complex.star_def, dv_conj]
      ring
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply, neg_zero] at hk ⊢
      exact (mul_eq_zero.mp hk).resolve_left (hne τ.1 i)
  · intro x hx
    rw [cmField_hermitianForm_baseChange_real_eq_sum hT A n (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) hβ1]
    have hterm : ∀ k : Phi A × Fin n,
        Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) (actOn rep ℝ J x) k =
          dv A n k.1.1 k.2 * Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k := by
      rintro ⟨τ, i⟩
      rw [Th_act (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) rep hβ2 J x τ i,
        hJτ, Matrix.mulVec_diagonal]
    have hz : ∃ k, Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      apply cmType_trace_embedding_injective_of_linearEquiv hT A n β
      rw [map_zero]
      funext k
      exact hc k
    obtain ⟨k₀, hk₀⟩ := hz
    have tp := fun (τ : Phi A) (i : Fin n) (z : ℂ) => term_pos (τ.1 A.δ) (τ.1 (A.hd n i : E)) z
      (hS E A n τ.1 i).2.1 (A.δ_sign τ.1 τ.2) (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)
    apply Finset.sum_pos'
    · rintro ⟨τ, i⟩ -
      rw [hterm]
      unfold dv
      exact mul_nonneg two_pos.le (tp τ i _).1
    · refine ⟨k₀, Finset.mem_univ _, ?_⟩
      obtain ⟨τ, i⟩ := k₀
      rw [hterm]
      unfold dv
      exact mul_pos two_pos ((tp τ i _).2 hk₀)
  · intro v
    obtain ⟨τ, hτv, -⟩ := (hT E A).2.2.1 v
    subst hτv
    have hω := (hT E A).2.2.2
    rcases InfinitePlace.embedding_mk_eq (τ : E →+* ℂ) with he | he
    · rw [he, if_pos τ.2, gram_diag, hJτ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (-Complex.I • fun i => τ.1 (A.hd n i : E) * dv A n τ.1 i) =
          fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).1
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)
    · have hc : ¬ (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.ω : E) = A.τ₀ (A.ω : E) := by
        intro h
        rw [ComplexEmbedding.conjugate_coe_eq, τ.2] at h
        exact hω (Complex.conj_eq_iff_im.mp h)
      rw [he, if_neg hc, gram_diag, evM_conj, hJτ, Matrix.diagonal_map (map_zero _),
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (Complex.I • fun i => (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.hd n i : E) *
          (starRingEnd ℂ) (dv A n τ.1 i)) = fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ComplexEmbedding.conjugate_coe_eq]
        rw [Complex.conj_eq_iff_im.mpr (hS E A n τ.1 i).1]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).2
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)

end UpperTheory.Gal.W2.Seed.Ori

theorem UpperTheory.Gal.W2.Seed.pOrient :
    TraceType → HdSign → Orient := by
  intro hT hS E _ _ _ A n hn hs p _ P rep hrep
  exact UpperTheory.Gal.W2.Seed.Ori.orient_core hT hS A n rep hrep
