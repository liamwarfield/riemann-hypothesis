module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameOfPeriodLinear
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePeriod

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
lemma eq_of_hermC_eq (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0)
    (v w : Fin r → ℂ) (h : ∀ u, FD.hermC τ Gm v u = FD.hermC τ Gm w u) : v = w := by
  classical
  have hd : (τ.mapMatrix Gm).det ≠ 0 := by
    rw [← RingHom.map_det]; exact (map_ne_zero τ).2 hG
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hd
  rw [sub_vecMul, sub_eq_zero]
  funext b
  have := h (Pi.single b 1)
  simpa [FD.hermC, Pi.single_apply, apply_ite, vecMul, dotProduct] using this

lemma loc_compare (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0) (q : ℕ)
    (M M' K : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0)
    (hK : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0)
    (h : ∀ u, locPer τ Gm q M' u = K *ᵥ locPer τ Gm q M u) :
    (∀ a c : Fin r, (a : ℕ) < q → K a c = (M⁻¹ * M') c a) ∧
      ∀ a c : Fin r, q ≤ (a : ℕ) → K a c = (M⁻¹ * M')⁻¹ a c := by
  classical
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  constructor
  · intro a c ha
    have h1 : FD.col M' a = ∑ e, K a e • FD.col M e := by
      apply eq_of_hermC_eq τ Gm hG
      intro u
      have := congrFun (h u) a
      rw [locPer_apply, if_pos ha] at this
      rw [this, FD.hermC_sum_left, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases he : (e : ℕ) < q
      · rw [if_pos he]
      · rw [hK a e (by simp [ha, he])]; simp
    rw [← FD.Data.mulVec_eq_sum_col] at h1
    have h2 : M⁻¹ *ᵥ FD.col M' a = K a := by
      rw [h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [← h2]
    rfl
  · intro a c ha
    have ha' : ¬ (a : ℕ) < q := not_lt.2 ha
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    have h1 := congrFun (h (M *ᵥ Pi.single c 1)) a
    rw [locPer_apply, if_neg ha', mulVec_mulVec] at h1
    have h2 : (K *ᵥ locPer τ Gm q M (M *ᵥ Pi.single c 1)) a = (K *ᵥ Pi.single c 1) a := by
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : (e : ℕ) < q
      · rw [hK a e (by simp [ha', he])]; simp
      · rw [locPer_apply, if_neg he, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [h2] at h1
    simpa using h1.symm

lemma allPer_scale {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (c : Ψ → ℂ) (y : Ψ → Fin r → ℂ) (k : Fin g) :
    allPer Gm q x idx (fun τ => c τ • y τ) k =
      (if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) * allPer Gm q x idx y k := by
  rw [allPer_apply, allPer_apply, locPer_apply, locPer_apply]
  split_ifs
  · rw [FD.hermC_smul_right]
  · rw [mulVec_smul]; rfl

lemma block_of_allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x x' : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (h : Matrix (Fin g) (Fin g) ℂ)
    (hs : Function.Surjective (allPer Gm q x idx))
    (hh : ∀ y, allPer Gm q x' idx y = h *ᵥ allPer Gm q x idx y) (k k' : Fin g)
    (hk : ¬ ((idx k).1 = (idx k').1 ∧ (((idx k).2 : ℕ) < q ↔ ((idx k').2 : ℕ) < q))) : h k k' = 0 := by
  classical
  have key : ∀ c : Ψ → ℂ, ((if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) -
      (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1)) * h k k' = 0 := by
    intro c
    obtain ⟨y, hy⟩ := hs (Pi.single k' 1)
    have h1 := congrFun (hh (fun τ => c τ • y τ)) k
    rw [allPer_scale, hh, hy] at h1
    have h2 : allPer Gm q x idx (fun τ => c τ • y τ) = Pi.single k'
        (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1) := by
      funext l
      rw [allPer_scale, hy]
      by_cases hl : l = k'
      · subst hl; simp
      · simp [hl]
    rw [h2] at h1
    simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, mul_one] at h1
    linear_combination h1
  by_cases h1 : (idx k).1 = (idx k').1
  · have h2 := key (fun _ => Complex.I)
    have hI : (2 * Complex.I) ≠ 0 := by simp
    by_cases ha : ((idx k).2 : ℕ) < q <;> by_cases hb : ((idx k').2 : ℕ) < q
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
    · rw [if_pos ha, if_neg hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination -h2
    · rw [if_neg ha, if_pos hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination h2
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
  · have h2 := key (Pi.single (idx k).1 1)
    simpa [Ne.symm h1] using h2

theorem frame_of_period_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ (P : D.La →+ (Fin g → ℂ)), ∀ x ∈ FD.GG Ψ Gm D.q, ∀ x' ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ (P' : D.La →+ (Fin g → ℂ)), (∀ v k, P' v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x' (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x' (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ h : Matrix (Fin g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) → ∃ b : FD.Frame Ψ r, x' = FD.rmul x b ∧ (∀ τ (a c : Fin r), (c : ℕ) < D.q → D.q ≤ (a : ℕ) → b τ a c = 0) ∧ (∀ k k', (idx k).1 = (idx k').1 → ((idx k).2 : ℕ) < D.q → ((idx k').2 : ℕ) < D.q → h k k' = b (idx k).1 (idx k').2 (idx k).2) ∧ (∀ k k', (idx k).1 = (idx k').1 → D.q ≤ ((idx k).2 : ℕ) → D.q ≤ ((idx k').2 : ℕ) → h k k' = (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx k').2) ∧ ∀ k k', ty k ≠ ty k' → h k k' = 0 := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, hdet, hEF⟩ P x hx x' hx' hP P' hP' h hh
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => (exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2).1
  have hbij := allPer_bijective Gm D.q x idx hloc
  have hQ : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  have hQ' : ∀ v, P' v = allPer Gm D.q x' idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP' v k
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hall : ∀ y, allPer Gm D.q x' idx y = h *ᵥ allPer Gm D.q x idx y := by
    have : allPer Gm D.q x' idx = (h.mulVecLin.restrictScalars ℝ) ∘ₗ allPer Gm D.q x idx := by
      apply b.ext
      intro i
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (hb (b i)).1 (Submodule.subset_span ⟨i, rfl⟩)
      rw [← hv, ← hQ', hh, hQ]
      rfl
    intro y
    rw [this]; rfl
  have hblock := block_of_allPer Gm D.q x x' idx h hbij.2 hall
  let K : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    Matrix.of fun a c => h (idx.symm (τ, a)) (idx.symm (τ, c))
  have hK0 : ∀ τ (a c : Fin r), ¬ ((a : ℕ) < D.q ↔ (c : ℕ) < D.q) → K τ a c = 0 := by
    intro τ a c hac
    apply hblock
    simpa using hac
  have hK : ∀ (τ : Ψ) u, locPer τ.1 Gm D.q (FD.mat x' τ) u =
      K τ *ᵥ locPer τ.1 Gm D.q (FD.mat x τ) u := by
    intro τ u
    funext a
    have h1 := congrFun (allPer_symm Gm D.q x' idx (fun _ => u) τ) a
    rw [← h1, hall, mulVec, mulVec, dotProduct, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single τ]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← allPer_symm Gm D.q x idx (fun _ => u) τ]
      rfl
    · intro σ _ hσ
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hblock, zero_mul]
      simp [hσ.symm]
    · simp
  have hc := fun τ : Ψ => loc_compare τ.1 Gm hdet D.q (FD.mat x τ) (FD.mat x' τ) (K τ) (hx τ).1 (hx' τ).1
    (hK0 τ) (hK τ)
  have hhK : ∀ k k', (idx k).1 = (idx k').1 → h k k' = K (idx k).1 (idx k).2 (idx k').2 := by
    intro k k' e
    simp only [K, of_apply]
    conv_rhs => rw [Prod.mk.eta, e, Prod.mk.eta]
    simp
  refine ⟨fun τ => ((FD.mat x τ)⁻¹ * FD.mat x' τ : Matrix (Fin r) (Fin r) ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (FD.mat x τ) (FD.mat x' τ)
      (isUnit_iff_ne_zero.2 (hx τ).1)).symm
  · intro τ a c hcq ha
    exact ((hc τ).1 c a hcq).symm.trans (hK0 τ c a (by simp [hcq, ha]))
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).1 _ _ h1
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).2 _ _ h1
  · intro k k' hne
    apply hblock
    rintro ⟨e1, e2⟩
    apply hne
    rw [hty, hty, e1]
    simp only [e2]

end

end GlobalTheory.FramePeriod
end

open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameFibre

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem exists_smul_eq {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hspan : Submodule.span E (Set.range φ) = ⊤) (u : Fin r → E) :
    ∃ (c : 𝓞 E) (v : L), c ≠ 0 ∧ (c : E) • u = φ v := by
  have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ⟨1, v, one_ne_zero, by simp⟩
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, v, hc, hv⟩ := hx
    obtain ⟨d, w, hd, hw⟩ := hy
    refine ⟨c * d, d • v + c • w, mul_ne_zero hc hd, ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← hv, ← hw]
    ext k
    simp [Algebra.smul_def]
    ring
  | smul a x _ hx =>
    obtain ⟨c, v, hc, hv⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd0
    refine ⟨c * d, n • v, mul_ne_zero hc hd0, ?_⟩
    rw [map_smul, ← hv]
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
    rw [Algebra.smul_def]
    field_simp

theorem exists_matrix {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (ψ : L →ₗ[𝓞 E] (Fin r → E)) : ∃ A : Matrix (Fin r) (Fin r) E, ∀ v, A *ᵥ φ v = ψ v := by
  haveI : IsLocalizedModule (𝓞 E)⁰ φ :=
    { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s
      surj := fun u => by
        obtain ⟨c, v, hc, hv⟩ := exists_smul_eq φ hspan u
        exact ⟨(v, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hv⟩
      exists_of_eq := fun h => ⟨1, by rw [hφ h]⟩ }
  have hb := IsLocalizedModule.isBaseChange (𝓞 E)⁰ E φ
  exact ⟨LinearMap.toMatrix' (hb.lift ψ), fun v => by
    rw [LinearMap.toMatrix'_mulVec, hb.lift_eq]⟩

theorem exists_gl {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (gam : L ≃ₗ[𝓞 E] L) : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ (gam v) := by
  obtain ⟨A, hA⟩ := exists_matrix φ hφ hspan (φ ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := exists_matrix φ hφ hspan (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA', Matrix.one_mulVec,
      LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩

theorem eq_zero_of_trace (t : E) (ht : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * t) = 0) : t = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 t fun e => ?_
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  have h : Algebra.trace ℚ E ((k • e) * t) = 0 := ht ⟨k • e, hki⟩
  rw [smul_mul_assoc, map_zsmul, smul_eq_zero] at h
  rw [Algebra.traceForm_apply, mul_comm]
  exact h.resolve_left hk

variable [IsCMField E]

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (c d : E) (x y : Fin r → E) :
    FD.herm G (c • x) (d • y) = c * FD.cc d * FD.herm G x y := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_of_trace {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hspan : Submodule.span E (Set.range φ) = ⊤) (G A : Matrix (Fin r) (Fin r) E) (ξ : E) (hξ : ξ ≠ 0)
    (h : ∀ v w, Algebra.trace ℚ E (ξ * FD.herm G (A *ᵥ φ v) (A *ᵥ φ w)) =
      Algebra.trace ℚ E (ξ * FD.herm G (φ v) (φ w))) (x y : Fin r → E) :
    FD.herm G (A *ᵥ x) (A *ᵥ y) = FD.herm G x y := by
  have h1 : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ v w, FD.herm G (A *ᵥ φ v) (A *ᵥ φ w) = FD.herm G (φ v) (φ w) := by
    intro v w
    apply mul_left_cancel₀ hξ
    rw [← sub_eq_zero]
    refine eq_zero_of_trace _ fun a => ?_
    have h2 := h (a • v) w
    have h3 : φ (a • v) = (a : E) • φ v := by rw [map_smul]; rfl
    have h4 := herm_smul_smul G (a : E) 1 (A *ᵥ φ v) (A *ᵥ φ w)
    have h5 := herm_smul_smul G (a : E) 1 (φ v) (φ w)
    rw [one_smul, h1, mul_one] at h4 h5
    rw [h3, Matrix.mulVec_smul, h4, h5] at h2
    rw [mul_sub, map_sub, mul_left_comm, h2, mul_left_comm, sub_self]
  obtain ⟨c, v, hc, hv⟩ := exists_smul_eq φ hspan x
  obtain ⟨d, w, hd, hw⟩ := exists_smul_eq φ hspan y
  have h2 := key v w
  rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, herm_smul_smul, herm_smul_smul] at h2
  refine mul_left_cancel₀ (mul_ne_zero ?_ ?_) h2
  · simpa using hc
  · exact (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)

theorem lact_mem_GG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {q : ℕ} {γ : GL (Fin r) E}
    (hγ : ∀ u v, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      FD.herm G u v) {x : FD.Frame Ψ r} (hx : x ∈ FD.GG Ψ G q) : FD.lact γ x ∈ FD.GG Ψ G q := by
  intro τ
  have e1 : FD.mat (FD.lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * FD.mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map τ.1.mapMatrix)
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero hu.ne_zero (hx τ).1
  · have h := (hx τ).2 i
    have e2 : FD.gram τ.1 G (FD.mat (FD.lact γ x) τ) = FD.gram τ.1 G (FD.mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
    unfold FD.dmin at h ⊢
    rwa [e2]

theorem exists_level_block_of_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ x ∈ FD.GG Ψ Gm (U.Di i).q, ∀ x' ∈ FD.GG Ψ Gm (U.Di i).q, U.u i (Pf x) = U.u i (Pf x') → ∃ (γ : GL (Fin r) E) (b : FD.Frame Ψ r), FD.IsUStab Gm (LinearMap.range φ) γ ∧ (∀ v, ∃ w, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ v + l.M • φ w) ∧ (∀ v, ∃ w, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ v + l.A • φ w) ∧ x' = FD.rmul (FD.lact γ x) b ∧ ∀ τ (a c : Fin r), (c : ℕ) < (U.Di i).q → (U.Di i).q ≤ (a : ℕ) → b τ a c = 0 := by
  classical
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hlat hr hPf x hx x' hx' hu
  have hper := (FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hlat hr).2
  obtain ⟨gam, h, hiso, hhalf, hA, hh⟩ :=
    (U.fibre i _ _ ((hper x hx).2 _ (hPf x)) ((hper x' hx').2 _ (hPf x'))).1 hu
  have hM := LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hhalf
  obtain ⟨γ, hγ⟩ := exists_gl φ hlat.1 hlat.2.1 gam
  have hξ0 : ξ ≠ 0 := by
    have hcm := FramePeriod.cmType H Ψ hΨ
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
      by_cases h : ComplexEmbedding.conjugate s ∈ Ψ
      · exact ⟨_, h⟩
      · exact ⟨s, (hcm s).2 h⟩
    rintro rfl
    simpa using hpos τ hτ
  have hun := herm_of_trace φ hlat.2.1 Gm γ ξ hξ0 fun v w => by
    rw [hγ, hγ, ← hlat.2.2.2.2, ← hlat.2.2.2.2, hiso]
  have hmove := (per_move E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hlat).2.1 x γ (Pf x)
    (Pf (FD.lact γ x)) hun (hPf x) (hPf _)
  obtain ⟨b, hb, hb0, -⟩ := FramePeriod.frame_of_period_linear E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty
    hξ hpos hlat (Pf (FD.lact γ x)) _ (lact_mem_GG hun hx) x' hx' (hPf _) (Pf x') (hPf _)
    (LinearMap.toMatrix' h.toLinearMap) fun v => by
      obtain ⟨a, rfl⟩ := gam.surjective v
      rw [LinearMap.toMatrix'_mulVec, hh, hmove a (gam a) (hγ a).symm]
      rfl
  refine ⟨γ, b, ⟨hun, fun y => ⟨?_, ?_⟩⟩, fun v => ?_, fun v => ?_, hb, hb0⟩
  · rintro ⟨v, rfl⟩
    exact ⟨gam v, (hγ v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨gam.symm v, ?_⟩
    apply (Matrix.mulVec_injective_of_isUnit γ.isUnit)
    rw [hγ, LinearEquiv.apply_symm_apply, hv]
  · obtain ⟨e, he⟩ := hM v
    exact ⟨e, by rw [hγ, he, map_add (f := _), map_nsmul]⟩
  · obtain ⟨e, he⟩ := hA v
    exact ⟨e, by rw [hγ, he, map_add (f := _), map_nsmul]⟩

end GlobalTheory.FrameFibre
