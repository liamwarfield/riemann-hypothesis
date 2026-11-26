module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleLatticeFamilyHermitianWeilAction
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperator
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelOperatorHermitianEisensteinSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominator
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominator
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Emb

noncomputable section

section Corner

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

def cor (c : R) (A : Matrix (Fin N) (Fin N) R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (A i') j) i

theorem cor_mul (a b : R) (A B : Matrix (Fin N) (Fin N) R) :
    cor a A * cor b B = cor (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cor_add (a b : R) (A B : Matrix (Fin N) (Fin N) R) :
    cor a A + cor b B = cor (a + b) (A + B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor]

theorem cor_neg (a : R) (A : Matrix (Fin N) (Fin N) R) : -cor a A = cor (-a) (-A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor]

theorem cor_one : cor (1 : R) (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor, Matrix.one_apply, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1)))]

theorem cor_zero : cor (0 : R) (0 : Matrix (Fin N) (Fin N) R) = 0 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor]

theorem cor_map (f : R →+* S) (a : R) (A : Matrix (Fin N) (Fin N) R) :
    (cor a A).map f = cor (f a) (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor]

theorem cor_conjTranspose (a : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (cor a A)ᴴ = cor (conj a) Aᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor, Matrix.conjTranspose_apply]

theorem cor_mulVec (a : R) (A : Matrix (Fin N) (Fin N) R) (x : R) (v : Fin N → R) :
    cor a A *ᵥ (Fin.cons x v : Fin (N + 1) → R) = (Fin.cons (a * x) (A *ᵥ v) : Fin (N + 1) → R) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [cor, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem cons_dot (x y : R) (v w : Fin N → R) :
    (Fin.cons x v : Fin (N + 1) → R) ⬝ᵥ (Fin.cons y w : Fin (N + 1) → R) = x * y + v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ]

theorem cor_inv (A : Matrix (Fin N) (Fin N) ℂ) (h : A.det ≠ 0) : (cor 1 A)⁻¹ = cor 1 A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [cor_mul, one_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h), cor_one]

theorem det_cor_den (C D : Matrix (Fin N) (Fin N) R) (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    (cor 0 C * Z + cor 1 D).det = (C * Z.submatrix Fin.succ Fin.succ + D).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have e : (cor 0 C * Z + cor 1 D).submatrix Fin.succ (Fin.succAbove 0) = C * Z.submatrix Fin.succ Fin.succ + D := by
    ext i j
    simp [cor, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [e]
  simp [cor, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_cor_one (D : Matrix (Fin N) (Fin N) R) : (cor 1 D).det = D.det := by
  simpa using det_cor_den (0 : Matrix (Fin N) (Fin N) R) D 0

theorem posDef_cor_one (A : Matrix (Fin N) (Fin N) ℂ) (h : A.PosDef) : (cor 1 A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, cor_conjTranspose, h.1.eq]
    simp
  · obtain ⟨a, v, rfl⟩ : ∃ (a : ℂ) (v : Fin N → ℂ), x = Fin.cons a v :=
      ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have hs : star (Fin.cons a v : Fin (N + 1) → ℂ) = Fin.cons (star a) (star v) := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [cor_mulVec, hs, cons_dot, one_mul]
    by_cases hv : v = 0
    · subst hv
      have ha : a ≠ 0 := by
        rintro rfl; exact hx (by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp)
      simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero]
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast Complex.normSq_pos.mpr ha
    · have h1 : 0 ≤ star a * a := by
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact_mod_cast Complex.normSq_nonneg a
      exact add_pos_of_nonneg_of_pos h1 (h.dotProduct_mulVec_pos hv)

theorem imH_cor (A : Matrix (Fin N) (Fin N) ℂ) : imH (cor I A) = cor 1 (imH A) := by
  unfold imH
  rw [cor_conjTranspose]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [cor]
  field_simp
  rw [Complex.I_sq]
  ring

end Corner

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

def emb (γ : M2 E N) : M2 E (N + 1) :=
  Matrix.fromBlocks (cor 1 γ.toBlocks₁₁) (cor 0 γ.toBlocks₁₂) (cor 0 γ.toBlocks₂₁)
    (cor 1 γ.toBlocks₂₂)

theorem ccT_cor (a : E) (A : Matrix (Fin N) (Fin N) E) : ccT (cor a A) = cor (cc a) (ccT A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor, ccT, cc]

theorem ccT_fromBlocks {m : ℕ} (A B C D : Matrix (Fin m) (Fin m) E) :
    ccT (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (ccT A) (ccT C) (ccT B) (ccT D) := by
  simp [ccT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

private theorem fromBlocks_cor_mul_fromBlocks_cor {R : Type} [CommRing R] {N : ℕ} (a b c d a' b' c' d' : R)
    (A B C D A' B' C' D' : Matrix (Fin N) (Fin N) R) :
    Matrix.fromBlocks (cor a A) (cor b B) (cor c C) (cor d D) *
        Matrix.fromBlocks (cor a' A') (cor b' B') (cor c' C') (cor d' D') =
      Matrix.fromBlocks (cor (a * a' + b * c') (A * A' + B * C')) (cor (a * b' + b * d') (A * B' + B * D'))
        (cor (c * a' + d * c') (C * A' + D * C')) (cor (c * b' + d * d') (C * B' + D * D')) := by
  rw [Matrix.fromBlocks_multiply]
  simp only [cor_mul, cor_add]

theorem emb_mem {γ : M2 E N} (h : γ ∈ UU E N) : emb γ ∈ UU E (N + 1) := by
  have h' : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  rw [← Matrix.fromBlocks_toBlocks γ, ccT_fromBlocks, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h'
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp h'
  have hJ : Matrix.J (Fin (N + 1)) E =
      Matrix.fromBlocks (cor 0 0) (cor (-1) (-1)) (cor 1 1) (cor 0 0) := by
    rw [Matrix.J, cor_zero, ← cor_neg, cor_one]
  show ccT (emb γ) * Matrix.J (Fin (N + 1)) E * emb γ = Matrix.J (Fin (N + 1)) E
  rw [hJ, emb, ccT_fromBlocks, ccT_cor, ccT_cor, ccT_cor, ccT_cor, fromBlocks_cor_mul_fromBlocks_cor, fromBlocks_cor_mul_fromBlocks_cor]
  simp only [h11, h12, h21, h22, cc, map_one, map_zero]
  congr 1 <;> congr 1 <;> ring

omit [NumberField E] [IsCMField E] in
theorem hDen_emb_det (γ : M2 E N) (Z : CM Ψ (N + 1) (N + 1)) (τ : Ψ) :
    (hDen Ψ (emb γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det := by
  simp only [hDen, emb, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one]
  exact det_cor_den _ _ _

def corZ (s : ℂ) (Z : CM Ψ N N) : CM Ψ (N + 1) (N + 1) := fun τ => cor s (Z τ)

def corV (z : CM Ψ n N) : CM Ψ n (N + 1) := fun τ => Matrix.of fun k => Fin.cons 0 (z τ k)

omit [NumberField E] [IsCMField E] in
theorem corZ_mem {Z : CM Ψ N N} (h : Z ∈ Hn Ψ N) : corZ I Z ∈ Hn Ψ (N + 1) := by
  intro τ
  show (imH (cor I (Z τ))).PosDef
  rw [imH_cor]
  exact posDef_cor_one _ (h τ)

omit [NumberField E] [IsCMField E] in
theorem pushZ_corZ (Z : CM Ψ N N) (t : ℝ) :
    pushZ Ψ (corZ I Z) (Pi.single 0 1) t = corZ (I + I * t) Z := by
  funext τ
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [cor, pushZ, corZ, Matrix.vecMulVec_apply, Pi.single_apply, Fin.succ_ne_zero]

omit [NumberField E] [IsCMField E] in
theorem dropZ_corZ (s : ℂ) (Z : CM Ψ N N) : dropZ Ψ (corZ s Z) = Z := by
  funext τ
  ext i j
  simp [cor, dropZ, corZ]

omit [NumberField E] [IsCMField E] in
theorem drop_corV (z : CM Ψ n N) : (fun τ => (corV z τ).submatrix id Fin.succ) = z := by
  funext τ
  ext k a
  simp [corV]

omit [NumberField E] [IsCMField E] in
theorem hDen_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen Ψ γ Z τ) := by
  simp only [hDen, emb, corZ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, zero_mul, zero_add]

omit [NumberField E] [IsCMField E] in
theorem hDen'_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen' Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen' Ψ γ Z τ) := by
  simp only [hDen', emb, corZ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one,
    cor_conjTranspose, cor_mul, cor_add, mul_zero, zero_add, map_one]

omit [NumberField E] [IsCMField E] in
theorem hAct_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0) :
    hAct Ψ (emb γ) (corZ s Z) = corZ s (hAct Ψ γ Z) := by
  funext τ
  simp only [hAct]
  rw [hDen_emb, cor_inv _ (h τ)]
  simp only [emb, corZ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, one_mul, add_zero, mul_one]
  rfl

omit [NumberField E] [IsCMField E] in
theorem hFac_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0)
    (z z' : CM Ψ n N) : hFac Ψ (emb γ) (corZ s Z) (corV z) (corV z') = hFac Ψ γ Z z z' := by
  unfold hFac
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hDen_emb, det_cor_one, cor_inv _ (h τ)]
  simp only [emb, Matrix.toBlocks_fromBlocks₂₁, cor_map, map_zero, cor_mul, one_mul]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  show (Fin.cons 0 (z' τ k) : Fin (N + 1) → ℂ) ⬝ᵥ cor 0 _ *ᵥ (Fin.cons 0 (z τ k) : Fin (N + 1) → ℂ) = _
  rw [cor_mulVec, cons_dot]
  simp

theorem transH_drop (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    (h : TransH Ψ (emb γ) φ ψ) : TransH Ψ γ (dropF φ) (dropF ψ) := by
  intro Z hZ z z'
  obtain ⟨hden, hact, -⟩ := (GlobalTheory.T.unitary_act_halfSpace_alt E Ψ N γ hγ).2 Z hZ
  have hdet : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ => (hden τ).1
  have hdet' : ∀ τ, (hDen' Ψ γ Z τ).det ≠ 0 := fun τ h0 =>
    (hden τ).1 (by rw [← (hden τ).2.1, h0, zero_mul])
  obtain ⟨w, hw⟩ : ∃ w : CM Ψ n N, w = fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : CM Ψ n N, w' = fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hw, ← hw']
  have hWφ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).2 (corZ I Z) (corZ_mem hZ)
  have hWψ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N ψ hψ).2 (corZ I (hAct Ψ γ Z)) (corZ_mem hact)
  have L1 := hWφ.2.2 (corV z) (corV z')
  have L2 := hWψ.2.2 (corV w) (corV w')
  simp only [dropZ_corZ, drop_corV] at L1 L2
  have key : ∀ t : ℝ, 0 ≤ t →
      thH Ψ ψ (pushZ Ψ (corZ I (hAct Ψ γ Z)) (Pi.single 0 1) t) (corV w) (corV w') =
        hFac Ψ γ Z z z' * thH Ψ φ (pushZ Ψ (corZ I Z) (Pi.single 0 1) t) (corV z) (corV z') := by
    intro t ht
    have hmem := hWφ.2.1 t ht
    have e := h _ hmem (corV z) (corV z')
    simp only [pushZ_corZ] at hmem e ⊢
    rw [hAct_emb γ _ Z hdet, hFac_emb γ _ Z hdet] at e
    rw [← e]
    congr 1
    · funext τ
      ext k j
      simp only [hDen'_emb, cor_inv _ (hdet' τ)]
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [cor, hw, corV, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · funext τ
      ext k j
      simp only [hDen_emb, cor_inv _ (hdet τ)]
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [cor, hw', corV, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  exact tendsto_nhds_unique_of_eventuallyEq L2 (L1.const_mul _) ((Filter.eventually_ge_atTop 0).mono key)

theorem dropF_weil (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) :
    dropF (weil Ψ (emb γ) φ) = weil Ψ γ (dropF φ) := by
  obtain ⟨hsb, htr, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n (N + 1) hn (emb γ) (emb_mem hγ) φ hφ
  have hd := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).1
  have hdw := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ hsb).1
  exact (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ (dropF φ) hd).2.2.1 _ hdw (transH_drop hΨ hγ hφ hsb htr)

abbrev up (N : ℕ) : Fin N ⊕ Fin N → Fin (N + 1) ⊕ Fin (N + 1) := Sum.map Fin.succ Fin.succ

def extV (E : Type) [Field E] (N : ℕ) :
    (Fin N ⊕ Fin N → E) →ₗ[E] (Fin (N + 1) ⊕ Fin (N + 1) → E) where
  toFun v := Sum.elim (Fin.cons 0 fun a => v (Sum.inl a)) (Fin.cons 0 fun a => v (Sum.inr a))
  map_add' v w := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_smul' c v := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp


omit [IsCMField E] in
theorem botSpan_eq (h : M2 E (N + 1)) (h0 : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1)
    (h1 : ∀ a, h (Sum.inr a) (Sum.inl 0) = 0) :
    botSpan h = (E ∙ Pi.single (Sum.inr 0) 1) ⊔
      (botSpan (h.submatrix (up N) (up N))).map (extV E N) := by
  have key : ∀ b : Fin N, extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) =
      h (Sum.inr b.succ) - h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 := by
    intro b
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp [extV, h1, Pi.single_apply]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    show h (Sum.inr a) ∈ _
    induction a using Fin.cases with
    | zero => rw [h0]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    | succ b =>
      have e : h (Sum.inr b.succ) = h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 +
          extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) := by rw [key]; abel
      rw [e]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, rfl⟩)))
  · refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, ← h0]
      exact Submodule.subset_span ⟨0, rfl⟩
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, rfl⟩
      show extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) ∈ botSpan h
      rw [key]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨b.succ, rfl⟩) (Submodule.smul_mem _ _ ?_)
      rw [← h0]
      exact Submodule.subset_span ⟨0, rfl⟩

omit [IsCMField E] in
theorem botSpan_emb (γ : M2 E N) :
    botSpan (emb γ) = (E ∙ Pi.single (Sum.inr 0) 1) ⊔ (botSpan γ).map (extV E N) := by
  have h0 : emb γ (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    ext (j | j) <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [cor, emb, Pi.single_apply]
  have h1 : ∀ a, emb γ (Sum.inr a) (Sum.inl 0) = 0 := by
    intro a; refine Fin.cases ?_ (fun a => ?_) a <;> simp [cor, emb]
  have hs : (emb γ).submatrix (up N) (up N) = γ := by
    ext (i | i) (j | j) <;>
      simp [cor, emb, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
  rw [botSpan_eq (emb γ) h0 h1, hs]

omit [IsCMField E] in
theorem map_botSpan_emb (γ : M2 E N) :
    (botSpan (emb γ)).map (LinearMap.funLeft E E (up N)) = botSpan γ := by
  rw [botSpan_emb, Submodule.map_sup, Submodule.map_span, Set.image_singleton, ← Submodule.map_comp]
  have e1 : LinearMap.funLeft E E (up N) (Pi.single (Sum.inr 0) 1) = 0 := by
    funext j
    rcases j with j | j <;> simp [LinearMap.funLeft_apply, Pi.single_apply, Fin.succ_ne_zero]
  have e2 : (LinearMap.funLeft E E (up N)).comp (extV E N) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    funext j
    rcases j with j | j <;> simp [extV, LinearMap.funLeft_apply]
  rw [e1, e2, Submodule.map_id, Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq]

omit [IsCMField E] in
theorem botSpan_emb_iff (γ γ' : M2 E N) :
    botSpan (emb γ) = botSpan (emb γ') ↔ botSpan γ = botSpan γ' := by
  constructor
  · intro h
    rw [← map_botSpan_emb γ, h, map_botSpan_emb]
  · intro h
    rw [botSpan_emb, botSpan_emb, h]

omit [IsCMField E] in
theorem botSpan_mul_le {m : ℕ} (a d : Matrix (Fin m) (Fin m) E) (g : M2 E m) :
    botSpan (Matrix.fromBlocks a 0 0 d * g) ≤ botSpan g := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have e : (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) = ∑ k, d i k • g (Sum.inr k) := by
    ext j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply]
  show (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) ∈ botSpan g
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)


omit [NumberField E] [IsCMField E] in
theorem exists_col (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, IsUnit b.det ∧ ∀ i, b i 0 = v i := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hc
    exact hv (funext fun i => by_contra fun hi => hc ⟨i, hi⟩)
  set c : Matrix (Fin (N + 1)) (Fin (N + 1)) E := Matrix.of fun i j =>
    Fin.cases (v (Equiv.swap 0 k i)) (fun j' : Fin N => if i = j'.succ then (1 : E) else 0) j with hcdef
  have hc : c.det = v k := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have e : c.submatrix Fin.succ (Fin.succAbove 0) = 1 := by
      ext i j
      simp [hcdef, Matrix.one_apply]
    rw [e]
    simp [hcdef, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1)))]
  refine ⟨c.submatrix (Equiv.swap 0 k) id, ?_, fun i => ?_⟩
  · rw [Matrix.det_permute, hc]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero ?_ hk)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 k)) with hs | hs <;> simp [hs]
  · simp [hcdef]

private theorem ccT_mul_J_mul_apply {m : ℕ} (M : M2 E m) (p q : Fin m ⊕ Fin m) :
    (ccT M * Matrix.J (Fin m) E * M) p q =
      ∑ i, cc (M (Sum.inr i) p) * M (Sum.inl i) q - ∑ i, cc (M (Sum.inl i) p) * M (Sum.inr i) q := by
  simp [Matrix.mul_apply, Matrix.J, ccT, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

private theorem cc_cc_siegel_theta_transformation (x : E) : cc (cc x) = x := by
  have := congrFun (congrFun (Base.ccT_ccT (Matrix.of fun (_ : Unit) (_ : Unit) => x)) ()) ()
  simpa [ccT] using this

theorem sub_mem {h : M2 E (N + 1)} (hh : h ∈ UU E (N + 1))
    (hc : ∀ i, h i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) i) :
    h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 ∧ h.submatrix (up N) (up N) ∈ UU E N := by
  have hU : ∀ p q, (ccT h * Matrix.J (Fin (N + 1)) E * h) p q = Matrix.J (Fin (N + 1)) E p q := by
    intro p q
    rw [show ccT h * Matrix.J (Fin (N + 1)) E * h = Matrix.J (Fin (N + 1)) E from hh]
  have hl : ∀ i, h (Sum.inl i) (Sum.inl 0) = if i = 0 then 1 else 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hr : ∀ i, h (Sum.inr i) (Sum.inl 0) = 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hrow : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    funext p
    have e := hU p (Sum.inl 0)
    rw [ccT_mul_J_mul_apply] at e
    simp only [hl, hr, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    have e2 : Matrix.J (Fin (N + 1)) E p (Sum.inl 0) = (Pi.single (Sum.inr 0) 1 : _ → E) p := by
      rcases p with p | p <;> simp [Matrix.J, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e2] at e
    have e3 := congrArg cc e
    rw [cc_cc_siegel_theta_transformation] at e3
    rw [e3]
    rcases p with p | p <;> simp [Pi.single_apply, cc]
  refine ⟨hrow, ?_⟩
  have hJ : ∀ p q, Matrix.J (Fin (N + 1)) E (up N p) (up N q) = Matrix.J (Fin N) E p q := by
    rintro (p | p) (q | q) <;> simp [Matrix.J, Matrix.one_apply]
  have z1 : ∀ x : Fin N ⊕ Fin N, (Pi.single (Sum.inr 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) (up N x) = 0 := by
    rintro (x | x) <;> simp [Pi.single_apply, Fin.succ_ne_zero]
  show ccT (h.submatrix (up N) (up N)) * Matrix.J (Fin N) E * h.submatrix (up N) (up N) = Matrix.J (Fin N) E
  ext p q
  have e := hU (up N p) (up N q)
  rw [ccT_mul_J_mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, hrow, hJ] at e
  rw [ccT_mul_J_mul_apply, ← e]
  simp [z1, cc]

theorem exists_botSpan {g : M2 E (N + 1)} (hg : g ∈ UU E (N + 1))
    (h0 : ∀ a, g.toBlocks₂₁ a 0 = 0) : ∃ γ ∈ UU E N, botSpan g = botSpan (emb γ) := by
  have hgU := (GlobalTheory.T.unitary_act_halfSpace_alt E (∅ : Finset (E →+* ℂ)) (N + 1) g hg).1
  have h0' : ∀ a, g (Sum.inr a) (Sum.inl 0) = 0 := fun a => by simpa [Matrix.toBlocks₂₁] using h0 a
  obtain ⟨v, hvd⟩ : ∃ v : Fin (N + 1) → E, v = fun i => g (Sum.inl i) (Sum.inl 0) := ⟨_, rfl⟩
  have hv : v ≠ 0 := by
    intro hv0
    refine (isUnit_iff_ne_zero.mp hgU.1) (Matrix.det_eq_zero_of_column_eq_zero (Sum.inl 0) ?_)
    rintro (i | i)
    · have := congrFun hv0 i
      rw [hvd] at this
      simpa using this
    · exact h0' i
  obtain ⟨b, hb, hbv⟩ := exists_col v hv
  have e2 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv _ hb
  have e1 : ccT b⁻¹ * ccT b = 1 := by rw [← Base.ccT_mul, e2, Base.ccT_one]
  have e0 : ccT (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) E) = 0 := by
    ext i j; simp [ccT, cc]
  obtain ⟨δ, hδd⟩ : ∃ δ : M2 E (N + 1), δ = Matrix.fromBlocks b⁻¹ 0 0 (ccT b) := ⟨_, rfl⟩
  have hδ : δ ∈ UU E (N + 1) := by
    show ccT δ * Matrix.J _ E * δ = Matrix.J _ E
    rw [hδd, ccT_fromBlocks, e0, Base.ccT_ccT, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [e1, e2]
  have hh : δ * g ∈ UU E (N + 1) := hgU.2.2.2.2 δ hδ
  have hv' : b *ᵥ Pi.single 0 1 = v := by
    funext i; simp [Matrix.mulVec_single, hbv]
  have hinv : b⁻¹ *ᵥ v = Pi.single 0 1 := by
    rw [← hv', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]
  have hc : ∀ i, (δ * g) i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : _ → E) i := by
    rintro (i | i)
    · have := congrFun hinv i
      rw [hvd] at this
      simp only [Matrix.mulVec, dotProduct] at this
      simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0', this, Pi.single_apply]
    · simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0']
  obtain ⟨hrow, hsub⟩ := sub_mem hh hc
  have h1 : ∀ a, (δ * g) (Sum.inr a) (Sum.inl 0) = 0 := fun a => by rw [hc]; simp
  refine ⟨(δ * g).submatrix (up N) (up N), hsub, ?_⟩
  rw [botSpan_emb, ← botSpan_eq (δ * g) hrow h1]
  apply le_antisymm
  · calc botSpan g = botSpan (Matrix.fromBlocks b 0 0 (ccT b⁻¹) * (δ * g)) := by
          rw [← Matrix.mul_assoc, hδd, Matrix.fromBlocks_multiply]
          simp [e1, e2]
      _ ≤ botSpan (δ * g) := botSpan_mul_le _ _ _
  · rw [hδd]
    exact botSpan_mul_le _ _ _

theorem exists_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∃ ι : M2 E N → M2 E (N + 1), (∀ γ ∈ UU E N, ι γ ∈ UU E (N + 1) ∧ (∀ a, (ι γ).toBlocks₂₁ a 0 = 0) ∧ (∀ (Z : CM Ψ (N + 1) (N + 1)) τ, (hDen Ψ (ι γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det) ∧ (∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → dropF (weil Ψ (ι γ) φ) = weil Ψ γ (dropF φ)) ∧ ∀ γ' ∈ UU E N, (botSpan (ι γ) = botSpan (ι γ') ↔ botSpan γ = botSpan γ')) ∧ ∀ g ∈ UU E (N + 1), (∀ a, g.toBlocks₂₁ a 0 = 0) → ∃ γ ∈ UU E N, botSpan g = botSpan (ι γ) := by
  intro E _ _ _ Ψ hΨ n N hn
  refine ⟨emb, fun γ hγ => ⟨emb_mem hγ, fun a => ?_, fun Z τ => hDen_emb_det γ Z τ,
    fun φ hφ => dropF_weil hΨ hn hγ hφ, fun γ' _ => botSpan_emb_iff γ γ'⟩, fun g hg h0 => exists_botSpan hg h0⟩
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [cor, emb]

end

end GlobalTheory.SW.Emb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominatorStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_compatible_with_weil_and_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∃ ι : M2 E N → M2 E (N + 1), (∀ γ ∈ UU E N, ι γ ∈ UU E (N + 1) ∧ (∀ a, (ι γ).toBlocks₂₁ a 0 = 0) ∧ (∀ (Z : CM Ψ (N + 1) (N + 1)) τ, (hDen Ψ (ι γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det) ∧ (∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → dropF (weil Ψ (ι γ) φ) = weil Ψ γ (dropF φ)) ∧ ∀ γ' ∈ UU E N, (botSpan (ι γ) = botSpan (ι γ') ↔ botSpan γ = botSpan γ')) ∧ ∀ g ∈ UU E (N + 1), (∀ a, g.toBlocks₂₁ a 0 = 0) → ∃ γ ∈ UU E N, botSpan g = botSpan (ι γ) := by
  first | exact @GlobalTheory.SW.Emb.exists_embedding | exact GlobalTheory.SW.Emb.exists_embedding | (intros; apply GlobalTheory.SW.Emb.exists_embedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelOperatorHermitianEisensteinSeries
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.EisSiegel

variable {N : ℕ}

theorem det_growth (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : D * Cᴴ = C * Dᴴ)
    (hQ : (C * Z + D).det ≠ 0) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ (C *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ, ‖(C * Z + D).det‖ * (1 + t * c) ≤
      ‖(C * (Z + (I * t) • vecMulVec v (star v)) + D).det‖ := by
  have hH : (C * Dᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h]
  set Q := C * Z + D with hQdef
  have hU : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  set x : Fin N → ℂ := (Q⁻¹)ᴴ *ᵥ v with hx
  have hxv : Qᴴ *ᵥ x = v := by
    rw [hx, mulVec_mulVec, ← conjTranspose_mul, nonsing_inv_mul _ hU, conjTranspose_one, one_mulVec]
  have hsx : star x = star v ᵥ* Q⁻¹ := by
    rw [hx, star_mulVec, conjTranspose_conjTranspose]
  have hs := im_quad_denom C D Z hH x
  rw [← hQdef, hxv] at hs
  refine ⟨(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re,
    (Complex.nonneg_iff.1 (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ x))).1,
    fun hv => (Complex.pos_iff.1 (hZ.dotProduct_mulVec_pos fun h0 => hv ?_)).1, fun t => ?_⟩
  · rw [← hxv, hQdef, conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec x Zᴴ, h0,
      mulVec_zero, zero_add, mulVec_mulVec, ← h, ← mulVec_mulVec, h0, mulVec_zero]
  · have e : C * (Z + (I * t) • vecMulVec v (star v)) + D =
        Q * (1 + vecMulVec ((I * t) • (Q⁻¹ *ᵥ (C *ᵥ v))) (star v)) := by
      rw [Matrix.mul_add Q, Matrix.mul_one, mul_vecMulVec, mulVec_smul, mulVec_mulVec,
        mul_nonsing_inv _ hU, one_mulVec, Matrix.mul_add, ← smul_vecMulVec, mul_vecMulVec,
        mulVec_smul, hQdef]
      abel
    rw [e, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, norm_mul,
      dotProduct_smul, dotProduct_mulVec (star v), ← hsx]
    generalize (star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re = c at hs
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) (Complex.re_le_norm _)) (norm_nonneg _)
    simp only [smul_eq_mul, add_re, one_re, mul_re, mul_im, I_re, I_im, zero_mul, one_mul,
      ofReal_re, ofReal_im, hs]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}


omit [NumberField E] [IsCMField E] in
theorem pushZ_mem {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have hP : ((t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a))).PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have := imH_add_I_smul (Z τ) _ hP.1
  rw [smul_smul] at this
  exact this ▸ (hZ τ).add_posSemidef hP

omit [NumberField E] [IsCMField E] in
theorem dropZ_pushZ (Z : CM Ψ (N + 1) (N + 1)) (t : ℝ) :
    dropZ Ψ (pushZ Ψ Z (Pi.single 0 1) t) = dropZ Ψ Z := by
  funext τ
  ext a b
  simp [dropZ, pushZ, vecMulVec_apply]

theorem hDen_growth {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (τ : Ψ) :
    (hDen Ψ γ Z τ).det ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ (γ.toBlocks₂₁ *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ,
      ‖(hDen Ψ γ Z τ).det‖ * (1 + t * c) ≤ ‖(hDen Ψ γ (pushZ Ψ Z v t) τ).det‖ := by
  have h0 := (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
  obtain ⟨c, h1, h2, h3⟩ := det_growth _ _ _ (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2 h0
    (hZ τ) (fun a => τ.1 (v a))
  refine ⟨h0, c, h1, fun hv => h2 fun h => hv ?_, h3⟩
  funext a
  apply τ.1.injective
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  exact congrFun h a

theorem norm_term_le {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (φ : Matrix (Fin n) (Fin N) E → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0‖ ≤ ‖eisTerm Ψ γ φ Z 0 0‖ := by
  simp only [eisTerm, EisTrans.hFac_zero, norm_mul, norm_inv, norm_prod, norm_pow]
  refine mul_le_mul_of_nonneg_left (inv_anti₀ ?_ ?_) (norm_nonneg _)
  · exact Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hDen_growth Ψ hγ hZ v τ).1) _
  · refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun τ _ => ?_
    obtain ⟨-, c, h1, -, h3⟩ := hDen_growth Ψ hγ hZ v τ
    refine pow_le_pow_left₀ (norm_nonneg _) (le_trans ?_ (h3 t)) _
    exact le_mul_of_one_le_right (norm_nonneg _) (by nlinarith [mul_nonneg ht h1])

theorem term_tendsto_zero (hΨ : IsType Ψ) (hn : n ≠ 0) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) (hv : γ.toBlocks₂₁ *ᵥ v ≠ 0)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Tendsto (fun t : ℝ => eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  have hne : Nonempty Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : σ ∈ Ψ
    · exact ⟨⟨σ, h⟩⟩
    · exact ⟨⟨_, not_not.1 ((hΨ σ).not.1 h)⟩⟩
  simp only [eisTerm, EisTrans.hFac_zero, ← Finset.prod_inv_distrib]
  have h1 : ∀ τ : Ψ, Tendsto (fun t : ℝ => ((hDen Ψ γ (pushZ Ψ Z v t) τ).det ^ n)⁻¹) atTop
      (𝓝 0) := by
    intro τ
    obtain ⟨h0, c, -, h2, h3⟩ := hDen_growth Ψ hγ hZ v τ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv, norm_pow]
    refine Tendsto.inv_tendsto_atTop ((tendsto_pow_atTop hn).comp (tendsto_atTop_mono h3 ?_))
    exact Tendsto.const_mul_atTop (norm_pos_iff.2 h0)
      (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const (h2 hv)))
  have h2 := (tendsto_finsetProd Finset.univ fun τ _ => h1 τ).const_mul (weil Ψ γ φ 0)
  rwa [Finset.prod_const, zero_pow (Finset.card_univ.trans_ne Fintype.card_ne_zero), mul_zero] at h2

end GlobalTheory.SW.EisSiegel


open GlobalTheory.SW.EisSiegel in
theorem GlobalTheory.SW.eis_siegel_operator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → ∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => eis Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 (eis Ψ (dropF φ) (dropZ Ψ Z) 0 0)) := by
  intro E _ _ _ Ψ hΨ n N hn hN φ hφ Z hZ
  obtain ⟨ι, hι, hsurj⟩ := GlobalTheory.T.embedding_compatible_with_weil_and_denominator E Ψ hΨ n N hn
  let j : Lag E N → Lag E (N + 1) := fun V =>
    ⟨botSpan (ι V.2.choose), _, (hι _ V.2.choose_spec.1).1, rfl⟩
  have hj : Function.Injective j := fun V W h => Subtype.ext (by
    rw [← V.2.choose_spec.2, ← W.2.choose_spec.2]
    exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ W.2.choose_spec.1).1 (congrArg Subtype.val h))
  unfold eis
  rw [← tsum_extend_zero hj]
  refine tendsto_tsum_of_dominated_convergence
    ((eis_automorphy_linear E Ψ hΨ n (N + 1) hn hN φ hφ Z hZ).1 0 0) (fun U => ?_) ?_
  · by_cases hU : ∃ V, j V = U
    · obtain ⟨V, rfl⟩ := hU
      rw [hj.extend_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨a1, -, a3, a4, -⟩ := hι _ V.2.choose_spec.1
      rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n (N + 1) hn φ hφ).2 _ (j V).2.choose_spec.1 _ a1
        (j V).2.choose_spec.2 _ (pushZ_mem Ψ hZ _ ht)]
      simp only [eisTerm, EisTrans.hFac_zero, a3, dropZ_pushZ]
      rw [← a4 φ hφ, dropF]
      congr 2
      ext k a
      refine Fin.cases rfl (fun _ => rfl) a
    · rw [Function.extend_apply' _ _ _ hU]
      refine term_tendsto_zero Ψ hΨ (by omega) U.2.choose_spec.1 hZ _ (fun h0 => hU ?_) φ
      obtain ⟨γ, hγ, e⟩ := hsurj _ U.2.choose_spec.1 fun a => by
        simpa using congrFun h0 a
      let V : Lag E N := ⟨botSpan γ, γ, hγ, rfl⟩
      refine ⟨V, Subtype.ext ?_⟩
      rw [← U.2.choose_spec.2, e]
      exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ hγ).2 V.2.choose_spec.2
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht U
    exact norm_term_le Ψ U.2.choose_spec.1 hZ _ φ ht
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelOperatorHermitianEisensteinSeriesStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelOperator_hermitianEisensteinSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → ∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => eis Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 (eis Ψ (dropF φ) (dropZ Ψ Z) 0 0)) := by
  first | exact @GlobalTheory.SW.eis_siegel_operator | exact GlobalTheory.SW.eis_siegel_operator | (intros; apply GlobalTheory.SW.eis_siegel_operator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SwdTendstoZeroAtCusps
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}


omit [IsCMField E] in
theorem exists_den {α β : Type} [Fintype α] [Fintype β] (γ : Matrix α β E) :
    ∃ c : ℕ, 0 < c ∧ Den c γ := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : α × β => γ p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i j => ?_⟩
  have h := hy (γ i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul, Nat.cast_natAbs]
  rw [zsmul_eq_mul] at h
  rcases abs_choice y with e | e
  · rw [e]; exact h
  · rw [e, Int.cast_neg, neg_mul]; exact h.neg


omit [NumberField E] [IsCMField E] in
theorem exists_inv (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ a b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, b * a = 1 ∧ a *ᵥ v = Pi.single 0 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  let b : Matrix (Fin (N + 1)) (Fin (N + 1)) E :=
    ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).submatrix id (Equiv.swap 0 i)
  have hd : ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).det = v i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hb : IsUnit b.det := by
    rw [Matrix.det_permute', hd]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.2 hi)
    exact (Equiv.Perm.sign (Equiv.swap 0 i)).isUnit.map (Int.castRingHom E)
  have hbv : b *ᵥ Pi.single 0 1 = v := by
    ext k; simp [b]
  refine ⟨b⁻¹, b, Matrix.mul_nonsing_inv b hb, ?_⟩
  rw [← hbv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hb, Matrix.one_mulVec]


omit [NumberField E] [IsCMField E] in
theorem pushZ_mem (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ}
    (ht : 0 ≤ t) : pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have e : imH (pushZ Ψ Z v t τ) = imH (Z τ) +
      (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) := by
    ext i j
    simp [imH, pushZ, vecMulVec_apply, Matrix.conjTranspose_apply]
    field_simp
    linear_combination (-2 * (t : ℂ) * τ.1 (v i) * conj (τ.1 (v j))) * I_sq
  rw [e]
  exact (hZ τ).add_posSemidef
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht))

theorem levi_mem {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1) :
    (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) ∈ UU E N := by
  have e : ccT (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 b := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  have h' : ccT a * ccT b = 1 := by rw [← Base.ccT_mul, h, Base.ccT_one]
  change ccT _ * _ * _ = _
  rw [e]
  simp [Matrix.J, Matrix.fromBlocks_multiply, h, h']

theorem hAct_levi (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (τ : Ψ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z τ = a.map τ.1 * Z τ * (a.map τ.1)ᴴ := by
  have h1 : b.map τ.1 * a.map τ.1 = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((b.map τ.1)ᴴ)⁻¹ = (a.map τ.1)ᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp [hAct, hDen, Base.ccT_map, h2]

theorem hAct_pushZ (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (v : Fin N → E) (t : ℝ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) (pushZ Ψ Z v t) =
      pushZ Ψ (hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z) (a *ᵥ v) t := by
  funext τ
  unfold pushZ
  rw [hAct_levi Ψ h, hAct_levi Ψ h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 3
  · funext i; simp [Matrix.mulVec, dotProduct]
  · funext i; simp [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]

theorem hFac_levi (Ψ : Finset (E →+* ℂ)) (a b : Matrix (Fin N) (Fin N) E) (Z : CM Ψ N N) :
    hFac Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z (0 : CM Ψ n N) 0 =
      ∏ τ : Ψ, ((ccT b).map τ.1).det ^ n := by
  simp [hFac, hDen]


omit [IsCMField E] in
theorem colsIn_cons (Λ : Lt E n) (c : E) (x : Matrix (Fin n) (Fin N) E) :
    ColsIn Λ (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E)) ↔
      ColsIn Λ (c • x) := by
  unfold ColsIn
  rw [Fin.forall_fin_succ]
  have : (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E))ᵀ 0 = 0 := by
    ext k; simp
  rw [this]
  exact ⟨fun h => h.2, fun h => ⟨Λ.zero_mem, h⟩⟩

theorem admissibleLatticeFamily_restrictFirstColumnZero {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ) :
    admitted M R (fun Λ => dropF (φ Λ)) := by
  refine ⟨hφ.pos, ?_, ?_, ?_, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' m x
    unfold dropF
    rw [← hφ.equiv h hh Λ hΛ Λ' hΛ' m]
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.mul_apply]
  · intro Λ hΛ x hx
    exact (colsIn_cons Λ _ x).1 (hφ.supp Λ hΛ _ hx)
  · intro Λ hΛ x y hy
    have hy' := (colsIn_cons Λ 1 y).2 (by rwa [one_smul])
    rw [one_smul] at hy'
    unfold dropF
    rw [← hφ.per Λ hΛ (Matrix.of fun k => Fin.cons 0 (x k)) _ hy']
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  · intro Λ hΛ Λ' hΛ' ha x hx hx'
    exact hφ.loc Λ hΛ Λ' hΛ' ha _ ((colsIn_cons Λ _ x).2 hx) ((colsIn_cons Λ' _ x).2 hx')

theorem isSB_of_adm {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n) {M R : ℕ}
    {φ : Fam E n N} (hφ : admitted M R φ) : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := by
  intro Λ hΛ
  obtain ⟨c, hc, hd⟩ := exists_den (1 : M2 E N)
  obtain ⟨_, _, -, h⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hφ.pos.2
  exact (h M Λ hΛ 1 Base.one_mem_UU hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1

theorem tendsto_first {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n)
    (hN : 4 * (N + 1) < n) (hsw : SWAt Ψ n N) {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ)
    {Z : CM Ψ (N + 1) (N + 1)} (hZ : Z ∈ Hn Ψ (N + 1)) :
    Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 0) := by
  have hsb := isSB_of_adm hΨ hn hφ
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hφ.pos.1).1
  letI : Fintype (Cls E n M) := Fintype.ofFinite _
  have hZ' : dropZ Ψ Z ∈ Hn Ψ N := ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N 0 isSB_zero).2 Z hZ).1
  rw [← hsw M R _ (admissibleLatticeFamily_restrictFirstColumnZero hφ) _ hZ']
  unfold swd classSum
  simp only [finsum_eq_sum_of_fintype]
  refine tendsto_finsetSum _ fun c _ => Tendsto.const_mul _ (Tendsto.sub ?_ ?_)
  · exact ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ (hsb _ (Quot.out c).2)).2 Z hZ).2.2 0 0
  · exact GlobalTheory.T.siegelOperator_hermitianEisensteinSeries E Ψ hΨ n N hn hN _ (hsb _ (Quot.out c).2) Z hZ

end GlobalTheory.SW.Cusp


open GlobalTheory.SW.Cusp in
theorem GlobalTheory.SW.swd_tendsto_zero_at_cusps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∀ v : Fin (N + 1) → E, v ≠ 0 → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  intro E _ _ _ Ψ hΨ n N hn hN hsw M R φ hφ v hv Z hZ
  obtain ⟨a, b, hba, hav⟩ := exists_inv v hv
  have hγ := levi_mem hba
  obtain ⟨c, hc, hd⟩ := exists_den (Matrix.fromBlocks a 0 0 (ccT b) : M2 E (N + 1))
  obtain ⟨R', hR'⟩ := GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction E Ψ hΨ n (N + 1) hn c R hc
  have hact := (unitary_act_halfSpace E Ψ (N + 1) _ hγ).2 Z hZ
  have hlim := tendsto_first hΨ hn hN hsw (hR' M φ hφ _ hγ hd) hact.2.1
  have hne : (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
    simpa [hDen] using (hact.1 τ).1
  have h2 := hlim.const_mul (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n)⁻¹
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h3 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hφ.pos.1 (isSB_of_adm hΨ hn hφ) _
    (pushZ_mem Ψ hZ v ht)).1 _ hγ
  rw [hAct_pushZ Ψ hba, hav, hFac_levi] at h3
  rw [h3, inv_mul_cancel_left₀ hne]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SwdTendstoZeroAtCuspsStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_swd_pushZ_atTop_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∀ v : Fin (N + 1) → E, v ≠ 0 → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  first | exact @GlobalTheory.SW.swd_tendsto_zero_at_cusps | exact GlobalTheory.SW.swd_tendsto_zero_at_cusps | (intros; apply GlobalTheory.SW.swd_tendsto_zero_at_cusps <;> assumption)
end
