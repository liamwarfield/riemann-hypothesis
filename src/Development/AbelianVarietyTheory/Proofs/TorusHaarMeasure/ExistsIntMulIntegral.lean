module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulMem
namespace GlobalTheory.IntegralMultiples

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  classical
  have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by
    rw [hΛ]
    exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy0, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  have hi := hy (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let o : NumberField.RingOfIntegers E := ⟨y • f i, hi⟩
  have e : y • f i • (g i : Fin r → E) = o • (g i : Fin r → E) := by
    rw [← smul_assoc, ← algebraMap_smul E o]
    rfl
  rw [e]
  exact Λ.smul_mem o (g i).2

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
      ∀ (v : Fin r → E), ∃ (k : ℤ), k ≠ (0 : ℤ) ∧ k • v ∈ Λ := by
  intro E _ _ r Λ hΛ v
  exact exists_int_smul_mem Λ hΛ v

end GlobalTheory.IntegralMultiples
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LatFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem exists_int_mul_integral (x : E) : ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * x) := by
  have h : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  exact ⟨k, hk, by simpa [zsmul_eq_mul] using hi⟩

omit [IsCMField E] in
theorem finite_bounded (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (k : ℤ) (hk : k ≠ 0) (R : ℝ) :
    {x : E | IsIntegral ℤ ((k : E) * x) ∧ ∀ τ : Ψ, ‖τ.1 x‖ ≤ R}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ (‖(k : ℂ)‖ * R)
  have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
  refine Set.Finite.of_finite_image (f := fun x => (k : E) * x) (hfin.subset ?_)
    (fun x _ y _ h => mul_left_cancel₀ hk' h)
  rintro _ ⟨x, ⟨hi, hb⟩, rfl⟩
  refine ⟨hi, fun φ => ?_⟩
  have : ‖φ x‖ ≤ R := by
    by_cases hφ : φ ∈ Ψ
    · exact hb ⟨φ, hφ⟩
    · have h2 : ComplexEmbedding.conjugate φ ∈ Ψ := by
        by_contra h3
        exact hφ ((hΨ φ).2 h3)
      have := hb ⟨_, h2⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

omit [IsCMField E] in
theorem exists_common_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ v ∈ Λ, ∀ a, IsIntegral ℤ ((k : E) * v a) := by
  classical
  obtain ⟨S, rfl⟩ := hΛ
  choose d hd hdi using (exists_int_mul_integral (E := E))
  refine ⟨∏ p ∈ S ×ˢ (Finset.univ : Finset (Fin r)), d (p.1 p.2),
    Finset.prod_ne_zero_iff.2 fun p _ => hd _, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    intro a
    have hm : (v, a) ∈ S ×ˢ (Finset.univ : Finset (Fin r)) :=
      Finset.mem_product.2 ⟨hv, Finset.mem_univ _⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : (Fin r → E) × Fin r => d (p.1 p.2)) hm
    rw [hc]
    have := (hdi (v a)).mul (isIntegral_algebraMap (R := ℤ) (A := E) (x := c))
    have e : ((d (v a) * c : ℤ) : E) * v a = (d (v a) : E) * v a * algebraMap ℤ E c := by
      simp only [Int.cast_mul, eq_intCast]
      ring
    exact e ▸ this
  | zero => intro a; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro a
    rw [Pi.add_apply, mul_add]
    exact (hx a).add (hy a)
  | smul c x _ hx =>
    intro a
    have := (hx a).mul (RingOfIntegers.isIntegral_coe c)
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm, mul_comm]
    exact this

omit [IsCMField E] in
theorem exists_int_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralMultiples.main
  | exact _root_.GlobalTheory.IntegralMultiples.main
  | (apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultiples.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultiples.main ..)

theorem finite_vectors (r : ℕ) (X : Data E r) (R : ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  refine (Set.Finite.pi' fun _ : Fin r => finite_bounded X.Ψ X.cmType k hk R).subset ?_
  rintro v ⟨hv, hb⟩ a
  exact ⟨hi v hv a, fun τ => hb τ a⟩

theorem finite_automorphisms (r : ℕ) (X : Data E r) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den X.Λ X.Λ_fg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem X.Λ X.Λ_span (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded X.Ψ X.cmType (k * l b) (mul_ne_zero hk (hl b)) R
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
  refine ⟨?_, fun τ => hb τ a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this

theorem latFin : ((∀ (r : ℕ) (X : Data E r) (R : ℝ), {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite) ∧ (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite)) :=
  ⟨finite_vectors, finite_automorphisms⟩

end GlobalTheory.LatFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate

namespace GlobalTheory.UnitaryFrames

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
lemma hermC_eq_dot {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ star w) := by
  simp only [hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply,
    mul_assoc, RCLike.star_def]

omit [NumberField E] [IsCMField E] in
lemma gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * (G.map τ * P.map (starRingEnd ℂ)) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc]

omit [NumberField E] [IsCMField E] in
lemma hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (u w : Fin r → ℂ) :
    hermC τ G (P *ᵥ u) (P *ᵥ w) = u ⬝ᵥ (gram τ G P *ᵥ star w) := by
  have h : star (P *ᵥ w) = P.map (starRingEnd ℂ) *ᵥ star w := by
    ext a
    simp [Matrix.mulVec, dotProduct]
  rw [hermC_eq_dot, gram_eq_mul, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

omit [NumberField E] [IsCMField E] in
lemma col_mul' {r : ℕ} (g P : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * P) a = g *ᵥ col P a := by
  ext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma det_ne_zero_of_isOrth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x)
    (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, Matrix.det_diagonal] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn
  split_ifs <;> simp

def unitarySubgroup {r : ℕ} (X : Data E r) : Subgroup (X.Ψ → GL (Fin r) ℂ) where
  carrier := {g | X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)}
  one_mem' := by
    intro τ u w
    simp
  mul_mem' := by
    intro a b ha hb τ u w
    have h1 := ha τ ((b τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((b τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    have h2 := hb τ u w
    simp only [Matrix.mulVec_mulVec] at h1
    simp only [Pi.mul_apply, Units.val_mul]
    exact h1.trans h2
  inv_mem' := by
    intro a ha τ u w
    have h1 := ha τ ((((a τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((((a τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1.symm

lemma isClosed_unitary {r : ℕ} (X : Data E r) :
    IsClosed {g : X.Ψ → GL (Fin r) ℂ | X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)} := by
  simp only [Data.IsUnitaryC, Set.setOf_forall]
  refine isClosed_iInter fun τ => isClosed_iInter fun u => isClosed_iInter fun w => ?_
  refine isClosed_eq ?_ continuous_const
  have hc : Continuous fun g : X.Ψ → GL (Fin r) ℂ => (g τ : Matrix (Fin r) (Fin r) ℂ) :=
    Units.continuous_val.comp (continuous_apply τ)
  simp only [hermC_eq_dot]
  exact (hc.matrix_mulVec continuous_const).dotProduct
    (continuous_const.matrix_mulVec (hc.matrix_mulVec continuous_const).star)

lemma locallyCompact_GL (r : ℕ) : LocallyCompactSpace (GL (Fin r) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

lemma secondCountable_GL (r : ℕ) : SecondCountableTopology (GL (Fin r) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

lemma isOrth_lmulC {r : ℕ} (X : Data E r) {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hn : X.IsUnitaryC n) {x : Frame X.Ψ r} (hx : IsOrth X x) : IsOrth X (X.lmulC n x) := by
  intro τ
  rw [← hx τ, show mat (X.lmulC n x) τ = n τ * mat x τ from rfl]
  ext a b
  simp only [gram, Matrix.of_apply, col_mul', hn τ]

noncomputable def toGL {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (mat x τ) (det_ne_zero_of_isOrth X hx τ)

lemma val_toGL {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (toGL X hx τ : Matrix (Fin r) (Fin r) ℂ) = mat x τ := rfl

lemma quotient_unitary {r : ℕ} (X : Data E r) {x y : Frame X.Ψ r} (hx : IsOrth X x)
    (hy : IsOrth X y) :
    X.IsUnitaryC fun τ => ((toGL X hx * (toGL X hy)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  intro τ u w
  have key : ∀ u w, hermC τ.1 X.Gm (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      hermC τ.1 X.Gm (mat y τ *ᵥ u) (mat y τ *ᵥ w) := by
    intro u w
    rw [hermC_mulVec, hermC_mulVec, hx τ, hy τ]
  have h := key ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
    ((((toGL X hy τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
  rw [← val_toGL X hx, ← val_toGL X hy] at h
  simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  exact h

lemma continuous_toGL {r : ℕ} (X : Data E r) :
    Continuous fun x : {x : Frame X.Ψ r | IsOrth X x} => toGL X x.2 := by
  refine continuous_pi fun τ => ?_
  have hc : Continuous fun x : {x : Frame X.Ψ r | IsOrth X x} => mat x.1 τ :=
    (continuous_apply τ).comp continuous_subtype_val
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  have h : (fun x : {x : Frame X.Ψ r | IsOrth X x} =>
      (((toGL X x.2 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) =
      fun x => ((mat x.1 τ).det)⁻¹ • (mat x.1 τ).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, val_toGL, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hc.matrix_det.inv₀ fun x => det_ne_zero_of_isOrth X x.2 τ).smul hc.matrix_adjugate

theorem unitary_group_frames :
    ((∀ (r : ℕ) (X : Data E r), ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ), ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧ (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, IsOrth X x0 → (∀ g : H, IsOrth X (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | IsOrth X x} ∧ (∀ x, IsOrth X x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g)) := by
  classical
  refine ⟨fun r X => ⟨unitarySubgroup X, fun g => Iff.rfl⟩, fun r X H hH => ?_⟩
  haveI := locallyCompact_GL r
  haveI := secondCountable_GL r
  have hcl : IsClosed (H : Set (X.Ψ → GL (Fin r) ℂ)) := by
    convert isClosed_unitary X using 1
    ext g
    exact hH g
  refine ⟨hcl.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, fun x0 hx0 => ?_⟩
  have horth : ∀ g : H, IsOrth X (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) :=
    fun g => isOrth_lmulC X ((hH _).1 g.2) hx0
  refine ⟨horth, fun x => if hx : IsOrth X x then
    ⟨toGL X hx * (toGL X hx0)⁻¹, (hH _).2 (quotient_unitary X hx hx0)⟩ else 1, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    refine ((continuous_toGL X).mul (continuous_const (y := (toGL X hx0)⁻¹))).congr fun x => ?_
    have hx : IsOrth X x.1 := x.2
    simp only [Function.comp_apply, Set.restrict_apply, dif_pos hx]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    funext τ
    change (((toGL X hx τ * (toGL X hx0 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (toGL X hx0 τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Units.val_mul, inv_mul_cancel_right, val_toGL]
  · intro g
    simp only [dif_pos (horth g)]
    apply Subtype.ext
    change toGL X (horth g) * (toGL X hx0)⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    funext τ
    exact Units.ext rfl

end GlobalTheory.UnitaryFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanNeZero
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem _root_.GlobalTheory.SpanIndex.relIndex_span_ne_zero : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) ≠ 0) := by
  classical
  intro r X ι _ _ w _ hw
  set V := Submodule.span E (Set.range w)
  set N := Submodule.span (𝓞 E) (Set.range w)
  set M : Submodule (𝓞 E) (Fin r → E) := X.Λ ⊓ V.restrictScalars (𝓞 E)
  have hK : X.Λ.toAddSubgroup ⊓ V.toAddSubgroup = M.toAddSubgroup := rfl
  rw [hK]
  have hMfg : M.FG := by
    haveI : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
    exact Submodule.FG.of_le_of_isNoetherian inf_le_left
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.mpr hMfg
  haveI : Module.Finite ℤ (M ⧸ N.comap M.subtype) := Module.Finite.trans (𝓞 E) _
  have htors : Module.IsTorsion ℤ (M ⧸ N.comap M.subtype) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨v, hv⟩ := x
      have hvV : v ∈ V := (Submodule.mem_inf.mp hv).2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hvV
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap]
      have hint : ∀ a, IsIntegral ℤ (y • c a) := fun a =>
        hy _ (Finset.mem_image_of_mem c (Finset.mem_univ a))
      have hsum : y • v = ∑ a, (⟨y • c a, hint a⟩ : 𝓞 E) • w a := by
        rw [← hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ext i
        change _ = ((⟨y • c a, hint a⟩ : 𝓞 E) : E) * w a i
        simp [zsmul_eq_mul, mul_assoc]
      change y • v ∈ N
      rw [hsum]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Finite (M ⧸ N.comap M.subtype) := Module.finite_of_fg_torsion _ htors
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

end GlobalTheory.SpanIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormFderivLeOfClosedBallSubset
open Metric

namespace GlobalTheory

theorem norm_fderiv_le_of_closedBall_subset {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {U : Set H} {f : H → ℂ} {C r : ℝ} {y : H} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hy : closedBall y r ⊆ U) (hC : ∀ x ∈ U, ‖f x‖ ≤ C) :
    ‖fderiv ℂ f y‖ ≤ C / r := by
  have hyU : y ∈ U := hy (mem_closedBall_self hr.le)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y hyU)
  refine ContinuousLinearMap.opNorm_le_bound' _ (div_nonneg hC0 hr.le) fun v hv => ?_
  have hv0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hR : 0 < r / ‖v‖ := div_pos hr hv0
  have hmem : ∀ t ∈ closedBall (0 : ℂ) (r / ‖v‖), y + t • v ∈ U := by
    intro t ht
    apply hy
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (le_div_iff₀ hv0).1 ht
  have hlin : ∀ t : ℂ, HasDerivAt (fun s : ℂ => y + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hd : DifferentiableOn ℂ (fun s : ℂ => f (y + s • v)) (closedBall 0 (r / ‖v‖)) := by
    intro t ht
    exact ((hf.differentiableAt (hU.mem_nhds (hmem t ht))).comp t
      (hlin t).differentiableAt).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun s : ℂ => f (y + s • v)) (ball 0 (r / ‖v‖)) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball _ hR.ne'])
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (sphere_subset_closedBall hz)))
  have hder : HasDerivAt (fun s : ℂ => f (y + s • v)) (fderiv ℂ f y v) 0 := by
    have h1 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using (hf.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hlin 0)
  rw [hder.deriv] at hb
  refine hb.trans (le_of_eq ?_)
  field_simp

theorem differentiableOn_tsum_of_norm_le :
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (ι : Type) (U : Set H)
      (f : ι → H → ℂ) (u : ι → ℝ), IsOpen U → (∀ i, DifferentiableOn ℂ (f i) U) → Summable u →
      (∀ i, ∀ x ∈ U, ‖f i x‖ ≤ u i) → DifferentiableOn ℂ (fun x => ∑' i, f i x) U := by
  intro H _ _ ι U f u hU hf hu hb x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : ∀ y ∈ ball x (ε / 2), closedBall y (ε / 2) ⊆ U := by
    intro y hy z hz
    apply hball
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  have h := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) (f := f)
    (f' := fun i y => fderiv ℂ (f i) y) (u := fun i => u i / (ε / 2)) (s := ball x (ε / 2))
    (x₀ := x) (x := x) (hu.div_const _) isOpen_ball (convex_ball x _).isPreconnected
    (fun i y hy => ((hf i).differentiableAt
      (hU.mem_nhds (hsub y hy (mem_closedBall_self hr.le)))).hasFDerivAt)
    (fun i y hy => norm_fderiv_le_of_closedBall_subset hU (hf i) hr (hsub y hy) (hb i))
    (mem_ball_self hr) (Summable.of_norm_bounded hu (fun i => hb i x hx)) (mem_ball_self hr)
  exact h.differentiableAt.differentiableWithinAt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one {r : ℕ} (G x : Matrix (Fin r) (Fin r) ℂ) (s : ℂ)
    (hs : s * s = 1) (h : xᵀ * G * x.map (starRingEnd ℂ) = s • (1 : Matrix (Fin r) (Fin r) ℂ))
    (a b : Fin r) : ‖x a b‖ ≤ 1 + ‖G⁻¹ a a‖ := by
  set y := x.map (starRingEnd ℂ) with hy
  have h1 : xᵀ * (s • (G * y)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h, smul_smul, hs, one_smul]
  have h2 : (s • (G * y)) * xᵀ = 1 := mul_eq_one_comm.1 h1
  have h3 : G * (s • (y * xᵀ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul]; exact h2
  have hinv : G⁻¹ = s • (y * xᵀ) := Matrix.inv_eq_right_inv h3
  have hentry : G⁻¹ a a = s * ((∑ c, ‖x a c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hinv, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hy, Matrix.transpose_apply, Complex.conj_mul']
  have hsn : ‖s‖ = 1 := by
    have h4 := congrArg norm hs
    rw [norm_mul, norm_one] at h4
    nlinarith [norm_nonneg s]
  have hsum : 0 ≤ ∑ c, ‖x a c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hnorm : ‖G⁻¹ a a‖ = ∑ c, ‖x a c‖ ^ 2 := by
    rw [hentry, norm_mul, hsn, one_mul, Complex.norm_of_nonneg hsum]
  have hle : ‖x a b‖ ^ 2 ≤ ∑ c, ‖x a c‖ ^ 2 :=
    Finset.single_le_sum (f := fun c => ‖x a c‖ ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)
  rw [hnorm]
  nlinarith [sq_nonneg (‖x a b‖ - 1), norm_nonneg (x a b)]

theorem _root_.GlobalTheory.orthonormal_frames_bounded_of_definite :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ X.p0 = r) →
      ∃ R : ℝ, ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖,
    fun x hx τ a b => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx
  have hτ := hx τ
  obtain ⟨s, hs, hdiag⟩ : ∃ s : ℂ, s * s = 1 ∧
      Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = s • 1 := by
    rcases hp with h | h
    · refine ⟨-1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
    · refine ⟨1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (Matrix.of (x τ))ᵀ * X.Gm.map (τ : E →+* ℂ) * (Matrix.of (x τ)).map (starRingEnd ℂ)
      = s • 1 := by
    rw [← hdiag, ← hτ]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hb := _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one _ _ s hs key a b
  have h1 : ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖ ≤ ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun a' => ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 : ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ ≤
      ∑ τ' : X.Ψ, ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun τ' : X.Ψ => ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hx' : ‖x τ a b‖ = ‖Matrix.of (x τ) a b‖ := rfl
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GramSchmidtCont

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem continuousOn_inv_apply {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M) (hd : ∀ t ∈ s, (M t).det ≠ 0)
    (i j : Fin n) : ContinuousOn (fun t => (M t)⁻¹ i j) s := by
  have hdet : Continuous fun t => (M t).det := hM.matrix_det
  have hadj : Continuous fun t => (M t).adjugate i j := hM.matrix_adjugate.matrix_elem i j
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hdet.continuousOn.inv₀ hd).mul hadj.continuousOn

theorem continuousOn_uMat_apply {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M)
    (hd : ∀ t ∈ s, ∀ c : Fin n, (blk (M t) c).det ≠ 0) (j c : Fin n) :
    ContinuousOn (fun t => uMat (M t) j c) s := by
  by_cases hjc : j = c
  · simp only [uMat, Matrix.of_apply, if_pos hjc]
    exact continuousOn_const
  by_cases h : j < c
  · have hB : Continuous fun t => blk (M t) c := by
      unfold blk
      exact hM.matrix_submatrix _ _
    have hinv := fun m k => continuousOn_inv_apply hB (fun t ht => hd t ht c) m k
    simp only [uMat, Matrix.of_apply, if_neg hjc, dif_pos h, Matrix.vecMul, dotProduct, rowc]
    refine ContinuousOn.neg (continuousOn_finsetSum _ fun m _ => ContinuousOn.mul ?_ (hinv m _))
    exact (hM.matrix_elem c _).continuousOn
  · simp only [uMat, Matrix.of_apply, if_neg hjc, dif_neg h]
    exact continuousOn_const

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem continuous_gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    Continuous (gram τ G) := by
  refine continuous_matrix fun a b => ?_
  simp only [gram, hermC, col, Matrix.of_apply]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    ((continuous_id.matrix_elem k a).mul continuous_const).mul
      (Complex.continuous_conj.comp (continuous_id.matrix_elem l b))

theorem continuous_mat {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    Continuous (fun x : Frame X.Ψ r => mat x τ) := by
  refine continuous_matrix fun a b => ?_
  simp only [mat, Matrix.of_apply]
  exact (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))

theorem continuousOn_uOf {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    ContinuousOn (fun x : Frame X.Ψ r => uOf X x τ) X.dom := by
  refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun c => ?_
  exact continuousOn_uMat_apply ((continuous_gram τ.1 X.Gm).comp (continuous_mat X τ))
    (fun x hx c => blk_det X hx τ c) j c

theorem continuousOn_dOf {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => dOf X x τ k) X.dom := by
  show ContinuousOn (fun x => gram τ.1 X.Gm (mat x τ * uOf X x τ) k k) X.dom
  exact ((continuous_id.matrix_elem k k).comp (continuous_gram τ.1 X.Gm)).comp_continuousOn
    ((continuous_mat X τ).continuousOn.mul (continuousOn_uOf X τ))

theorem continuousOn_sOf {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => sOf X x τ k) X.dom := by
  show ContinuousOn (fun x => (((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ) : ℂ)) X.dom
  refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀ ?_ ?_)
  · exact Real.continuous_sqrt.comp_continuousOn (continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (continuousOn_dOf X τ k)))
  · intro x hx
    exact (Real.sqrt_pos.2 (abs_re_pos X hx τ k)).ne'

theorem continuousOn_bOf {r : ℕ} (X : Data E r) : ContinuousOn (bOf X) X.dom := by
  refine continuousOn_pi.2 fun τ => ?_
  show ContinuousOn (fun x => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix (Fin r) (Fin r) ℂ)) X.dom
  exact (continuousOn_uOf X τ).mul (continuous_id.matrix_diagonal.comp_continuousOn
    (continuousOn_pi.2 fun k => continuousOn_sOf X τ k))

theorem exists_continuous_gramSchmidt :
    (∀ (r : ℕ) (X : Data E r), ∃ β : Frame X.Ψ r → Frame X.Ψ r, ContinuousOn β X.dom ∧
      ∀ x ∈ X.dom, β x ∈ Bor X.Ψ r ∧ IsOrth X (rmul x (β x))) := by
  intro r X
  exact ⟨bOf X, continuousOn_bOf X, fun x hx => ⟨bOf_mem X hx, ortho_bOf X hx⟩⟩

end GlobalTheory.GramSchmidtCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder

namespace GlobalTheory.MajorantContinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_l {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [NumberField E] [IsCMField E] in
lemma hermC_smul_r {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (a • v) = conj a * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma scale_lemma {n : ℕ} (s : ℝ) (A B : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, (s : ℂ) * A a * M a b * ((s : ℂ) * B b) = ((s ^ 2 : ℝ) : ℂ) * ∑ a, ∑ b, A a * M a b * B b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

lemma maj_real_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (t : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((t : ℂ) • v) = t ^ 2 * X.maj x τ v := by
  have hc : conj (t : ℂ) = t := Complex.conj_ofReal t
  have e2 : hermC τ.1 X.Gm ((t : ℂ) • v) ((t : ℂ) • v) = ((t ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_l, hermC_smul_r, hc]; push_cast; ring
  unfold Data.maj Data.posPart
  rw [e2]
  simp_rw [hermC_smul_l (a := (t : ℂ)) (u := v), map_mul, hc]
  rw [scale_lemma, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

lemma continuousAt_maj {r : ℕ} (X : Data E r) (τ : X.Ψ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → ℂ) :
    ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, v) := by
  have hH : ∀ f g : Frame X.Ψ r × (Fin r → ℂ) → (Fin r → ℂ), Continuous f → Continuous g →
      Continuous fun p => hermC τ.1 X.Gm (f p) (g p) := by
    intro f g hf hg
    unfold hermC
    have hf' : ∀ a, Continuous fun p => f p a := fun a => (continuous_apply a).comp hf
    have hg' : ∀ b, Continuous fun p => g p b := fun b => (continuous_apply b).comp hg
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hf' a).mul continuous_const).mul (Complex.continuous_conj.comp (hg' b))
  have hcol : ∀ k : Fin r, Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => col (mat p.1 τ) k := by
    intro k
    change Continuous fun p : Frame X.Ψ r × (Fin r → ℂ) => fun i => p.1 τ i k
    exact continuous_pi fun i => (continuous_apply k).comp ((continuous_apply i).comp
      ((continuous_apply τ).comp continuous_fst))
  have hG : Continuous fun y : Frame X.Ψ r => X.gramPos y τ := by
    unfold Data.gramPos
    exact (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_gram X τ).matrix_submatrix _ _
  have hdet : (X.gramPos x τ).det ≠ 0 := (X.gramPos_posDef hx τ).det_pos.ne'
  have hI : ContinuousAt (fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) x := by
    refine (continuousAt_matrix_inv _ ?_).comp hG.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hIab : ∀ a b : Fin X.p0,
      ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹ a b) (x, v) :=
    fun a b => by
      have hI' : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => (X.gramPos p.1 τ)⁻¹) (x, v) :=
        ContinuousAt.comp (g := fun y : Frame X.Ψ r => (X.gramPos y τ)⁻¹) (f := Prod.fst) hI
          continuous_fst.continuousAt
      exact ContinuousAt.comp (g := fun M : Matrix (Fin X.p0) (Fin X.p0) ℂ => M a b)
        (continuous_id.matrix_elem a b).continuousAt hI'
  unfold Data.maj Data.posPart
  refine ContinuousAt.sub (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_))
    (Complex.continuous_re.comp (hH _ _ continuous_snd continuous_snd)).continuousAt
  refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
  exact (((hH _ _ continuous_snd (hcol _)).continuousAt.mul (hIab a b)).mul
    (Complex.continuous_conj.comp (hH _ _ continuous_snd (hcol _))).continuousAt)

lemma exists_sphere {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) :
    ∃ w ∈ Metric.sphere (0 : Fin r → ℂ) 1, v = ((‖v‖ : ℝ) : ℂ) • w := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  refine ⟨((‖v‖ : ℝ) : ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hn), one_smul]

lemma maj_at_zero {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC]

lemma ne_zero_of_sphere {r : ℕ} {w : Fin r → ℂ} (hw : w ∈ Metric.sphere (0 : Fin r → ℂ) 1) :
    w ≠ 0 := by
  rintro rfl
  rw [mem_sphere_zero_iff_norm, norm_zero] at hw
  exact zero_ne_one hw

theorem eventually_comparable {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v := by
  have hdom : ∀ᶠ y in 𝓝 x, y ∈ X.dom := (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X).mem_nhds hx
  have key : ∀ τ : X.Ψ, ∀ᶠ y in 𝓝 x, ∀ w ∈ Metric.sphere (0 : Fin r → ℂ) 1,
      X.maj x τ w < (1 + ε) * X.maj y τ w ∧ X.maj y τ w < (1 + ε) * X.maj x τ w := by
    intro τ
    refine (isCompact_sphere (0 : Fin r → ℂ) 1).eventually_forall_of_forall_eventually ?_
    intro w hw
    have hpos : 0 < X.maj x τ w := X.maj_pos hx τ (ne_zero_of_sphere hw)
    have h1 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, w) :=
      continuousAt_maj X τ hx w
    have h2 : ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj x τ p.2) (x, w) :=
      ContinuousAt.comp_of_eq (g := fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
        (f := fun p : Frame X.Ψ r × (Fin r → ℂ) => (x, p.2)) h1
        (continuous_const.prodMk continuous_snd).continuousAt rfl
    refine (h2.eventually_lt (continuousAt_const.mul h1) ?_).and
      (h1.eventually_lt (continuousAt_const.mul h2) ?_)
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
    · show X.maj x τ w < (1 + ε) * X.maj x τ w
      nlinarith
  filter_upwards [hdom, Filter.eventually_all.2 key] with y hy hk
  refine ⟨hy, fun τ v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hx' : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hy' : X.maj y τ v = ‖v‖ ^ 2 * X.maj y τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X y τ _ w
  obtain ⟨k1, k2⟩ := hk τ w hw
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hx', hy']
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left k1.le ht]
  · nlinarith [mul_le_mul_of_nonneg_left k2.le ht]

theorem compact_bounds {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)} (hK : IsCompact K)
    (hKd : K ⊆ X.dom) : ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2 := by
  classical
  have hKS := hK.prod (isCompact_sphere (0 : Fin r → ℂ) 1)
  have hcont : ∀ τ : X.Ψ, ContinuousOn (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
      (K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1) :=
    fun τ => continuousOn_of_forall_continuousAt fun p hp => continuousAt_maj X τ (hKd hp.1) p.2
  have hlow : ∀ τ : X.Ψ, ∃ c', 0 < c' ∧ ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1,
      c' ≤ X.maj p.1 τ p.2 :=
    fun τ => hKS.exists_forall_le' (hcont τ) fun p hp => X.maj_pos (hKd hp.1) τ (ne_zero_of_sphere hp.2)
  have hup : ∀ τ : X.Ψ, ∃ C', ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1, ‖X.maj p.1 τ p.2‖ ≤ C' :=
    fun τ => hKS.exists_bound_of_continuousOn (hcont τ)
  choose cτ hcpos hcle using hlow
  choose Cτ hCle using hup
  have hsum : 0 ≤ ∑ σ, (cτ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hcpos σ)).le
  refine ⟨(1 + ∑ σ, (cτ σ)⁻¹)⁻¹, ∑ σ, |Cτ σ|, inv_pos.2 (by linarith), ?_⟩
  intro x hx τ v
  have hc_le : (1 + ∑ σ, (cτ σ)⁻¹)⁻¹ ≤ cτ τ := by
    have h1 : (cτ τ)⁻¹ ≤ ∑ σ, (cτ σ)⁻¹ :=
      Finset.single_le_sum (f := fun σ => (cτ σ)⁻¹) (fun σ _ => (inv_pos.2 (hcpos σ)).le)
        (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  have hC_le : Cτ τ ≤ ∑ σ, |Cτ σ| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |Cτ σ|) (fun σ _ => abs_nonneg _)
      (Finset.mem_univ τ))
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hm : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hlo : cτ τ ≤ X.maj x τ w := hcle τ (x, w) ⟨hx, hw⟩
  have hhi : X.maj x τ w ≤ Cτ τ := (le_abs_self _).trans
    ((Real.norm_eq_abs _).symm.trans_le (hCle τ (x, w) ⟨hx, hw⟩))
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hc_le.trans hlo) ht]
  · nlinarith [mul_le_mul_of_nonneg_left (hhi.trans hC_le) ht]

theorem majorant_continuity :
    ((∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) ∧ (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2)) := ⟨fun _ X _ hx _ hε => eventually_comparable X hx hε,
    fun _ X _ hK hKd => compact_bounds X hK hKd⟩

end GlobalTheory.MajorantContinuity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMaximalMinorNeZeroOfLinearIndependent
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent
    (K : Type) [Field K] (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → K)
    (hw : LinearIndependent K w) :
    ∃ e : ι → Fin r, Function.Injective e ∧ (Matrix.of fun k a => w a (e k)).det ≠ 0 := by
  classical
  set A : Matrix (Fin r) ι K := Matrix.of fun k a => w a k with hA
  have hcol : A.col = w := rfl
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_cols, hcol, finrank_span_eq_card hw]
  have htop : Submodule.span K (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  haveI : Fintype κ := Fintype.ofInjective a ha
  let b := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := K), Module.finrank_eq_card_basis b]
  let f : ι ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ f, ha.comp f.injective, ?_⟩
  have hrow : LinearIndependent K (Matrix.of fun k a' => w a' ((a ∘ f) k)).row :=
    hli.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrow)).ne_zero

end GlobalTheory
end
