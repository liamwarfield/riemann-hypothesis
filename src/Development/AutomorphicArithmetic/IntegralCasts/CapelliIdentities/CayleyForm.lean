module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyForm
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

noncomputable def UpperTheory.Reformulated.B.Qj14.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qj14.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qj14.Hpk k r + UpperTheory.Reformulated.B.Qj14.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qj14.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qj14.UH (UpperTheory.Reformulated.B.Qj14.Hpk k r)

noncomputable def UpperTheory.Reformulated.B.Qj14.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qj14.Mat k r → UpperTheory.Reformulated.B.Qj14.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)⁻¹

private theorem UpperTheory.Reformulated.B.Qj14.cayley_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Y : Matrix ι ι ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [hinv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.Qj14.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qj14.Mat k r},
      UpperTheory.Reformulated.B.Qj14.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qj14.kap Y ∈ UpperTheory.Reformulated.B.Qj14.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qj14.cayley_form (UpperTheory.Reformulated.B.Qj14.Hpk k r) Y h hu
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetEmbUnitriA
theorem UpperTheory.Reformulated.B.Qe13.aux1 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ),
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R)
          (0 : Matrix (Fin (1 : ℕ)) (Fin n) R) (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        (1 : Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R) := by
  intro R _ n
  exact Matrix.fromBlocks_one

theorem UpperTheory.Reformulated.B.Qe13.aux2 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R),
      Matrix.fromBlocks (A * B) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
          (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) *
          Matrix.fromBlocks B (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) := by
  intro R _ n A B
  rw [Matrix.fromBlocks_multiply]
  simp

noncomputable def UpperTheory.Reformulated.B.Qe13.blkHom :
    (R : Type) →
      [inst : CommRing R] → (n : ℕ) → Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R :=
    fun (R : Type) [CommRing R] (n : ℕ) ↦
      {
        toFun := fun (A : Matrix (Fin n) (Fin n) R) ↦
          Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R),
        map_one' := UpperTheory.Reformulated.B.Qe13.aux1 R n, map_mul' := UpperTheory.Reformulated.B.Qe13.aux2 R n :
        Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R }

noncomputable def UpperTheory.Reformulated.B.Qe13.embGL :
    (R : Type) → [inst : CommRing R] → (n N : ℕ) → n + (1 : ℕ) = N → GL (Fin n) R →* GL (Fin N) R :=
    fun (R : Type) [CommRing R] (n N : ℕ) (h : n + (1 : ℕ) = N) ↦
      Units.map
        ((↑(↑(Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))) :
                    Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →ₐ[R] Matrix (Fin N) (Fin N) R).toRingHom :
              Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →* Matrix (Fin N) (Fin N) R).comp
          (UpperTheory.Reformulated.B.Qe13.blkHom R n))

theorem UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A :
    ∀ {n : ℕ} (g : GL (Fin n) ℂ),
      (∀ (i j : Fin n), j < i → (↑g : Matrix (Fin n) (Fin n) ℂ) i j = (0 : ℂ)) →
        (∀ (i : Fin n), (↑g : Matrix (Fin n) (Fin n) ℂ) i i = (1 : ℂ)) →
          (Matrix.GeneralLinearGroup.det : GL (Fin (n + (1 : ℕ))) ℂ → ℂˣ)
              ((UpperTheory.Reformulated.B.Qe13.embGL ℂ n (n + (1 : ℕ)) rfl : GL (Fin n) ℂ → GL (Fin (n + (1 : ℕ))) ℂ) g) =
            (1 : ℂˣ) := by
  intro n g hlow hdiag
  have htri : (↑g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id := fun i j hij => hlow i j hij
  have hg : (↑g : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  apply Units.ext
  change Matrix.det (Matrix.reindex (finSumFinEquiv.trans (finCongr rfl)) (finSumFinEquiv.trans (finCongr rfl))
    (Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin n) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ))) = 1
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hg, Matrix.det_one, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableOperator
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh28.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qh28.Umon.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) ↦
      Submonoid.closure (Set.range fun (ab : Fin n × Fin n) ↦ E ab.1 ab.2)

noncomputable def UpperTheory.Reformulated.B.Qh28.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qh28.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qh28.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qh28.isoSub.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qh28.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (lam : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qh28.Umon E, ∃ (v : V), UpperTheory.Reformulated.B.Qh28.IsHWV E lam v ∧ x = (u : V → V) v}

theorem UpperTheory.Reformulated.B.Qh28.isotypic_stable_operator.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  unfold UpperTheory.Reformulated.B.Qh28.isoSub at hx ⊢
  refine (Submodule.span_le (p := Submodule.comap (E a b) (Submodule.span K _))).2 ?_ hx
  rintro _ ⟨u, hu, v, hv, rfl⟩
  refine Submodule.subset_span ⟨E a b * u, ?_, v, hv, rfl⟩
  exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChoiceOfModulusAndDiscriminant
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK :
    ℕ → ℤ → ℤ → ℕ → Prop :=
    fun (a : ℕ) (b c : ℤ) (d : ℕ) ↦
      (4 : ℤ) * (↑a : ℤ) * c = b ^ (2 : ℕ) + (↑d : ℤ) ∧ Odd a ∧ d % (8 : ℕ) = (7 : ℕ) ∧ Nat.Prime d

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta :
    ℤ → ℕ → ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ((↑b : ℂ) + Complex.I * (↑√(↑d : ℝ) : ℂ)) / (2 : ℂ)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF :
    ℤ → ℕ → IntermediateField ℚ ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ℚ⟮UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d⟯

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq (b : ℤ) (d : ℕ) :
    UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d =
      (b : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d - ((b : ℂ) ^ 2 + (d : ℂ)) / 4 := by
  have h : ((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  unfold UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta
  linear_combination (((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) / 4) * Complex.I_mul_I - (1 / 4 : ℂ) * h

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral (b : ℤ) (d : ℕ) :
    IsIntegral ℚ (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X
    + Polynomial.C (((b : ℚ) ^ 2 + (d : ℚ)) / 4), ?_, ?_⟩
  · monicity!
  · have h := UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, eq_ratCast]
    push_cast
    linear_combination h

theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.kap_repr :
    ∀ {a : ℕ} {b c : ℤ} {d : ℕ},
      UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK a b c d →
        ∀ {x : ℂ}, x ∈ UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF b d → ∃ (u : ℚ) (v : ℚ), x = (↑u : ℂ) + (↑v : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d := by
  intro a b c d _ x hx
  have hx' : x ∈ Algebra.adjoin ℚ {UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral b d).isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - v * v' * (((b : ℚ) ^ 2 + (d : ℚ)) / 4), u * v' + v * u' + v * v' * b, ?_⟩
    push_cast
    linear_combination ((v : ℂ) * (v' : ℂ)) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableGlOperator
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe29.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qe29.Umon.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) ↦
      Submonoid.closure (Set.range fun (ab : Fin n × Fin n) ↦ E ab.1 ab.2)

noncomputable def UpperTheory.Reformulated.B.Qe29.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qe29.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qe29.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qe29.isoSub.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qe29.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (lam : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qe29.Umon E, ∃ (v : V), UpperTheory.Reformulated.B.Qe29.IsHWV E lam v ∧ x = (u : V → V) v}

theorem UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n),
      ∀ x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu, (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  have hE : E a b ∈ UpperTheory.Reformulated.B.Qe29.Umon E := Submonoid.subset_closure ⟨(a, b), rfl⟩
  have hle : UpperTheory.Reformulated.B.Qe29.isoSub E mu ≤ (UpperTheory.Reformulated.B.Qe29.isoSub E mu).comap (E a b) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, v, hv, rfl⟩
    exact Submodule.subset_span ⟨E a b * u, Submonoid.mul_mem _ hE hu, v, hv, rfl⟩
  exact hle hx
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerRest
noncomputable def UpperTheory.Reformulated.B.Qe31.Statement :
    Prop :=
    ∀ (T : Type) [inst : CommRing T] [IsNoetherianRing T] (P : Ideal T) [inst_2 : P.IsPrime] (h : ℕ) (f : Fin h → T),
      (∀ (i : Fin h), f i ∈ P) →
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
            Ideal.span
                (Set.range fun (i : Fin h) ↦
                  (Algebra.algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) ⊔
              IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (2 : ℕ) →
          ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

theorem UpperTheory.Reformulated.B.Qe31.proof :
    UpperTheory.Reformulated.B.Qe31.Statement := by
  intro T _ _ P _ h f _ hle
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
      Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rwa [smul_eq_mul, ← pow_two]
  have hI : Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) =
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have key : ∀ x ∈ P, ∃ s ∉ P, s * x ∈ Ideal.span (Set.range f) := by
    intro x hx
    have h1 : algebraMap T (Localization.AtPrime P) x ∈
        (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
      rw [← hI]
      apply hm
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩ :=
      (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).1 h1
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hab
    obtain ⟨⟨c, hc⟩, hcab⟩ := hab
    refine ⟨c * b, P.primeCompl.mul_mem hc hb, ?_⟩
    have : c * b * x = c * a := by
      simp only at hcab
      rw [← hcab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian P
  have hSP : ∀ x ∈ S, x ∈ P := fun x hx ↦ hS ▸ Submodule.subset_span hx
  choose! g hg1 hg2 using key
  refine ⟨∏ y ∈ S, g y, P.primeCompl.prod_mem (fun y hy ↦ hg1 y (hSP y hy)), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g hy
    rw [hc, mul_comm (g y) c, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hg2 y (hSP y hy))
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Ideal.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ ha
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightComponentsMemInvariant
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf7.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qf7.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf7.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

private theorem UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V]
    [_root_.Module K V] {E : UpperTheory.Reformulated.B.Qf7.GLOps n K V} {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) (a : Fin n) : E a a x = (mu a : K) • x := by
  unfold UpperTheory.Reformulated.B.Qf7.weightSp at hx
  have h := (Submodule.mem_iInf _).1 hx a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h

theorem UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      [CharZero K] (E : UpperTheory.Reformulated.B.Qf7.GLOps n K V) (W : Submodule K V),
      (∀ (a : Fin n), ∀ x ∈ W, (E a a : V → V) x ∈ W) →
        ∀ (s : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
          (∀ mu ∈ s, f mu ∈ UpperTheory.Reformulated.B.Qf7.weightSp E mu) → ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W := by
  intro n K V _ _ _ _ E W hW s
  classical
  induction s using Finset.induction_on with
  | empty => intro f _ _ mu hmu; simp at hmu
  | insert nu t hnu ih =>
    intro f hf hsum
    have ht : ∀ mu ∈ t, f mu ∈ W := by
      intro mu hmu
      have hne : mu ≠ nu := fun h => hnu (h ▸ hmu)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      have h1 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l) ∈ W :=
        W.sub_mem (hW a _ hsum) (W.smul_mem _ hsum)
      have h2 : E a a (∑ l ∈ insert nu t, f l) - (nu a : K) • (∑ l ∈ insert nu t, f l)
          = ∑ l ∈ insert nu t, ((l a : K) - (nu a : K)) • f l := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [UpperTheory.Reformulated.B.Qf7.apply_of_mem_weightSp (hf l hl) a, sub_smul]
      rw [h2, Finset.sum_insert hnu, sub_self, zero_smul, zero_add] at h1
      have h3 := ih (fun l => ((l a : K) - (nu a : K)) • f l)
        (fun l hl => Submodule.smul_mem _ _ (hf l (Finset.mem_insert_of_mem hl))) h1 mu hmu
      have hc : ((mu a : K) - (nu a : K)) ≠ 0 :=
        sub_ne_zero.2 (fun h => ha (Int.cast_injective h))
      exact (W.smul_mem_iff hc).1 h3
    intro mu hmu
    rcases Finset.mem_insert.1 hmu with rfl | hmu
    · rw [Finset.sum_insert hnu] at hsum
      exact (W.add_mem_iff_left (W.sum_mem ht)).1 hsum
    · exact ht mu hmu
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsCMOfConj
theorem UpperTheory.Reformulated.B.Qh8.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨x, hx⟩ : ∃ x : K, starRingEnd ℂ (φ₀ x) ≠ φ₀ x := by
    by_contra hne
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    by_contra hz
    exact hne ⟨z, hz⟩
  have hanti : ∀ (z : K) (φ : K →+* ℂ), starRingEnd ℂ (φ (z - c z)) = -φ (z - c z) := by
    intro z φ
    simp [hc]
  obtain ⟨d, hd0, hd⟩ : ∃ d : K, d ≠ 0 ∧ ∀ φ : K →+* ℂ, starRingEnd ℂ (φ d) = -φ d := by
    refine ⟨x - c x, fun h0 => hx ?_, hanti x⟩
    rw [← hc, ← sub_eq_zero.mp h0]
  have hli : LinearIndependent (NumberField.maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    have h1 : s * 1 + t * d = 0 := hst
    have h2 := congrArg φ₀ h1
    have h3 := congrArg (starRingEnd ℂ) h2
    have hs' : starRingEnd ℂ (φ₀ s) = φ₀ s := hs φ₀
    have ht' : starRingEnd ℂ (φ₀ t) = φ₀ t := ht φ₀
    simp only [map_add (f := _), map_mul, map_one, map_zero, hs', ht', hd] at h2 h3
    have hs0 : s = 0 := by
      apply φ₀.injective
      rw [map_zero]
      linear_combination (h2 + h3) / 2
    have ht0 : t = 0 := by
      rw [hs0, zero_mul, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_right hd0
    exact ⟨Subtype.ext hs0, Subtype.ext ht0⟩
  have hsp : ⊤ ≤ Submodule.span (NumberField.maximalRealSubfield K)
      (Set.range ![(1 : K), d]) := by
    intro z _
    have ha : (z + c z) / 2 ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      simp [hc, add_comm, map_ofNat]
    have hb : (z - c z) / (2 * d) ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      rw [map_div₀, map_div₀, hanti, map_mul, map_mul, hd, map_ofNat, map_ofNat, mul_neg,
        neg_div_neg_eq]
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
    change (z + c z) / 2 * 1 + (z - c z) / (2 * d) * d = z
    field_simp
    ring
  have hfin : Module.finrank (NumberField.maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]
  haveI : Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K :=
    { finrank_eq_two' := hfin }
  exact ⟨⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermApply
noncomputable def UpperTheory.Reformulated.B.Yoa6.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.Yoa6.Helpers

private noncomputable def herm {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v))
    (by intro v v' w; simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)
    (by intro v w w'; simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)

private lemma herm_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) (v w : V) :
    herm B c v w = c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.Yoa6.Helpers

open UpperTheory.Reformulated.B.Yoa6.Helpers in
theorem UpperTheory.Reformulated.B.Yoa6.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.Yoa6.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ h
  obtain ⟨B, hB0, hBinv⟩ := h
  have hherm : ∀ (c : ℂ) (v w : V), herm B c w v = starRingEnd ℂ (herm B c v w) := by
    intro c v w
    simp only [herm_apply, map_add (f := _), map_mul, Complex.conj_conj]
    ring
  have hinv : ∀ (c : ℂ) (g : G) (v w : V), herm B c (ρ g v) (ρ g w) = herm B c v w := by
    intro c g v w
    simp only [herm_apply, hBinv]
  by_cases h1 : herm B 1 = 0
  · refine ⟨herm B Complex.I, ?_, hherm Complex.I, hinv Complex.I⟩
    intro hI
    apply hB0
    ext v w
    have e1 := congrArg (fun f => f v w) h1
    have e2 := congrArg (fun f => f v w) hI
    simp only [herm_apply, LinearMap.zero_apply, map_one, one_mul, Complex.conj_I] at e1 e2
    simp only [LinearMap.zero_apply]
    have : (2 * Complex.I) * B v w = 0 := by
      linear_combination Complex.I * e1 + e2
    rcases mul_eq_zero.mp this with h | h
    · exfalso; simp [Complex.ext_iff] at h
    · exact h
  · exact ⟨herm B 1, h1, hherm 1, hinv 1⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WtGeProd
noncomputable def UpperTheory.Reformulated.B.Qk29.dot.{v} :
    {ι : Type v} → (ι →₀ ℕ) → (ι → ℝ) → ℝ :=
    fun {ι : Type v} (n : ι →₀ ℕ) (r : ι → ℝ) ↦ n.sum fun (i : ι) (k : ℕ) ↦ (↑k : ℝ) * r i

noncomputable def UpperTheory.Reformulated.B.Qk29.MonoWtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → (ι →₀ ℕ) → K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (n : ι →₀ ℕ) (c : K) ↦
      ‖c‖ ≤ pi ^ (w - UpperTheory.Reformulated.B.Qk29.dot n r)

noncomputable def UpperTheory.Reformulated.B.Qk29.WtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), UpperTheory.Reformulated.B.Qk29.MonoWtGe pi r w n ((MvPowerSeries.coeff n : MvPowerSeries ι K → K) f)

private theorem UpperTheory.Reformulated.B.Qk29.dot_add {ι : Type*} (a b : ι →₀ ℕ) (r : ι → ℝ) :
    UpperTheory.Reformulated.B.Qk29.dot (a + b) r = UpperTheory.Reformulated.B.Qk29.dot a r + UpperTheory.Reformulated.B.Qk29.dot b r := by
  unfold UpperTheory.Reformulated.B.Qk29.dot
  apply Finsupp.sum_add_index'
  · intro i; simp
  · intro i m n; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_one {K : Type*} [NormedField K] {ι : Type*} {pi : ℝ}
    (hpi : 0 < pi) (r : ι → ℝ) : UpperTheory.Reformulated.B.Qk29.WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h
    simp [UpperTheory.Reformulated.B.Qk29.dot]
  · rw [norm_zero]
    exact (Real.rpow_pos_of_pos hpi _).le

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_mul {K : Type*} [NormedField K] {ι : Type*}
    [IsUltrametricDist K] {pi : ℝ} (hpi : 0 < pi) {r : ι → ℝ} {a b : ℝ}
    {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qk29.WtGe pi r a f)
    (hg : UpperTheory.Reformulated.B.Qk29.WtGe pi r b g) : UpperTheory.Reformulated.B.Qk29.WtGe pi r (a + b) (f * g) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_pos_of_pos hpi _).le
  intro p hp
  have hn : p.1 + p.2 = n := by simpa using hp
  have h1 := hf p.1
  have h2 := hg p.2
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe at h1 h2
  have he : a + b - UpperTheory.Reformulated.B.Qk29.dot n r =
      (a - UpperTheory.Reformulated.B.Qk29.dot p.1 r) + (b - UpperTheory.Reformulated.B.Qk29.dot p.2 r) := by
    rw [← hn, UpperTheory.Reformulated.B.Qk29.dot_add]; ring
  rw [he, Real.rpow_add hpi, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_pos_of_pos hpi _).le

theorem UpperTheory.Reformulated.B.Qk29.wtGe_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} [IsUltrametricDist K] {pi : ℝ},
      (0 : ℝ) < pi →
        ∀ {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ) (F : α → MvPowerSeries ι K),
          (∀ i ∈ s, UpperTheory.Reformulated.B.Qk29.WtGe pi r (wt i) (F i)) → UpperTheory.Reformulated.B.Qk29.WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by
  intro K inst ι _ pi hpi r α s wt F h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperTheory.Reformulated.B.Qk29.wtGe_one hpi r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qk29.wtGe_mul hpi (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsotypicStableUnderOperators
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf30.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qf30.Umon.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) ↦
      Submonoid.closure (Set.range fun (ab : Fin n × Fin n) ↦ E ab.1 ab.2)

noncomputable def UpperTheory.Reformulated.B.Qf30.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qf30.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qf30.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qf30.isoSub.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qf30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (lam : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qf30.Umon E, ∃ (v : V), UpperTheory.Reformulated.B.Qf30.IsHWV E lam v ∧ x = (u : V → V) v}

theorem UpperTheory.Reformulated.B.Qf30.isotypic_stable_under_operators.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  unfold UpperTheory.Reformulated.B.Qf30.isoSub at hx ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨u, hu, v, hv, rfl⟩
    refine Submodule.subset_span ⟨E a b * u, ?_, v, hv, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ c hy
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegreeOneStatement
namespace DegreeOneCoeffSubstitution
open MvPowerSeries Finsupp

private lemma deg_one {σ : Type} [DecidableEq σ] (d : σ →₀ ℕ) (h : d.degree = 1) :
    ∃ s, d = Finsupp.single s 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
  refine ⟨s, ?_⟩
  have hsum : d s + ∑ i ∈ d.support.erase s, d i = 1 := by
    rw [Finset.add_sum_erase _ _ hs, ← degree_apply, h]
  have hs0 : d s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hds : d s = 1 := by omega
  have hrest : ∑ i ∈ d.support.erase s, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  ext i
  by_cases his : i = s
  · subst his; simp [hds]
  · rw [Finsupp.single_apply, if_neg (Ne.symm his)]
    by_cases hi : i ∈ d.support
    · exact hrest i (Finset.mem_erase.mpr ⟨his, hi⟩)
    · exact Finsupp.notMem_support_iff.mp hi

end DegreeOneCoeffSubstitution

open MvPowerSeries Finsupp in
theorem UpperTheory.Reformulated.B.LinearTermOfSubstitution.main :
    ∀ {S : Type}
    [inst : CommRing S] {σ τ : Type} [inst_1 : Fintype σ] [DecidableEq σ] [DecidableEq τ] (a : σ → MvPowerSeries τ S),
    (∀ (s : σ), (MvPowerSeries.constantCoeff : MvPowerSeries τ S → S) (a s) = (0 : S)) →
      ∀ (f : MvPowerSeries σ S) (t : τ),
        (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (MvPowerSeries.subst a f) =
          ∑ s : σ,
            (MvPowerSeries.coeff fun₀ | s => (1 : ℕ) : MvPowerSeries σ S → S) f *
              (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (a s) := by
  intro S _ σ τ _ _ _ a ha f t
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hS]
  have key : ∀ d : σ →₀ ℕ, d ∉ Finset.univ.image (fun s => Finsupp.single s 1) →
      coeff (Finsupp.single t 1) (d.prod fun s e => a s ^ e) = 0 := by
    intro d hd
    by_cases h0 : d = 0
    · subst h0
      simp [coeff_one]
    have h1 : d.degree ≠ 1 := by
      intro h
      obtain ⟨s, rfl⟩ := DegreeOneCoeffSubstitution.deg_one d h
      exact hd (by simp)
    have h2 : 2 ≤ d.degree := by
      have : d.degree ≠ 0 := fun h => h0 ((degree_eq_zero_iff d).mp h)
      omega
    unfold Finsupp.prod
    apply coeff_of_lt_order
    rw [Finsupp.degree_single]
    refine lt_of_lt_of_le ?_ (le_order_prod _ _)
    calc ((1 : ℕ) : ℕ∞) < 2 := by norm_num
      _ ≤ ((d.degree : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = ∑ i ∈ d.support, ((d i : ℕ) : ℕ∞) := by rw [degree_apply]; push_cast; rfl
      _ ≤ ∑ i ∈ d.support, (a i ^ d i).order :=
          Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s => Finsupp.single s 1)) ?_]
  · rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]
    apply Finset.sum_congr rfl
    intro s _
    simp [Finsupp.prod_single_index, smul_eq_mul]
  · intro d hd
    by_contra h
    apply hd
    simp only
    rw [key d (by simpa using h), smul_zero]
end
