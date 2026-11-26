module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan
@[reducible] noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.Normd :
    {C : Type} →
      [inst : Field C] →
        {N : ℕ} → {Γ : Type} → [inst_1 : Group Γ] → (Γ →* GL (Fin N) C) → Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) → Prop :=
    fun {C : Type} [Field C] {N : ℕ} {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C)
        (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)) ↦
      ∀ (g : Γ),
        ∀ a ∈ A,
          (↑((ρ : Γ → GL (Fin N) C) g) : Matrix (Fin N) (Fin N) C) * a *
              (↑((ρ : Γ → GL (Fin N) C) g⁻¹) : Matrix (Fin N) (Fin N) C) ∈
            A

noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens :
    {Γ C : Type} →
      [inst : Group Γ] →
        [inst_1 : Field C] →
          {N : ℕ} → (Γ →* GL (Fin N) C) → Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) → Set (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) :=
    fun {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)) ↦
      {x : UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N | ∃ a ∈ A, ∃ (g : Γ), x = a * (↑((ρ : Γ → GL (Fin N) C) g) : Matrix (Fin N) (Fin N) C)}

theorem UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul :
    ∀ {Γ C : Type} [inst : Group Γ] [inst_1 : Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
      (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)),
      UpperTheory.Reformulated.B.NormalizedMatrixSpan.Normd ρ A →
        ∀ (x y : UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N),
          x ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) →
            y ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) → x * y ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) := by
  intro Γ C _ _ N ρ A hA x y hx hy
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, g, rfl⟩, _, ⟨b, hb, k, rfl⟩, rfl⟩
  refine ⟨a * ((ρ g : Matrix (Fin N) (Fin N) C) * b * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C)),
    A.mul_mem ha (hA g b hb), g * k, ?_⟩
  have e : (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) * (ρ (g * k) : Matrix (Fin N) (Fin N) C)
      = (ρ k : Matrix (Fin N) (Fin N) C) := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel_left]
  simp only [mul_assoc, e]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfEmbUnique
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf27.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

noncomputable def UpperTheory.Reformulated.B.Qf27.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qf27.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qf27.infEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {τ : E →+* ℂ}
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ τ θ θ' h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ c : F, (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F) c) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] (algebraMap F E c) := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hA : (fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h2 h2' ?_
    funext c
    simp only [Function.comp_apply]
    rw [key, h1, h1']
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    have e : a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h1, h1', congrFun hA a]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeqEx
theorem UpperTheory.Reformulated.B.Qj7.seq_ex :
    ∀ (S : ℕ → Type),
    (∀ (n : ℕ), Finite (S n)) →
      (∀ (n : ℕ), Nonempty (S n)) →
        ∀ (t : (n : ℕ) → S (n + (1 : ℕ)) → S n), ∃ (u : (n : ℕ) → S n), ∀ (n : ℕ), t n (u (n + (1 : ℕ))) = u n := by
  intro S hfin hne t
  classical
  letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥
  haveI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩
  let C : ℕ → Set ((n : ℕ) → S n) := fun k => {u | ∀ n < k, t n (u (n + 1)) = u n}
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    have hC : C k = ⋂ n, ⋂ (_ : n < k), {u : (n : ℕ) → S n | t n (u (n + 1)) = u n} := by
      ext u
      simp [C]
    rw [hC]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply (n + 1)))
      (continuous_apply n)
  have hstep : ∀ (k : ℕ) (x : S k), ∃ u ∈ C k, u k = x := by
    intro k
    induction k with
    | zero =>
      intro x
      refine ⟨Function.update (fun n => Classical.choice (hne n)) 0 x, ?_, by simp⟩
      intro n hn
      exact absurd hn (Nat.not_lt_zero n)
    | succ k ih =>
      intro x
      obtain ⟨u, hu, hk⟩ := ih (t k x)
      refine ⟨Function.update u (k + 1) x, ?_, by simp⟩
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hu n h
      · subst h
        rw [Function.update_self, Function.update_of_ne (by omega), hk]
  have hnon : ∀ k, (C k).Nonempty := by
    intro k
    obtain ⟨u, hu, _⟩ := hstep k (Classical.choice (hne k))
    exact ⟨u, hu⟩
  have hmono : ∀ k, C (k + 1) ⊆ C k := fun k u hu n hn => hu n (Nat.lt_succ_of_lt hn)
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hnon
    (hclosed 0).isCompact hclosed
  exact ⟨u, fun n => Set.mem_iInter.mp hu (n + 1) n (Nat.lt_succ_self n)⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalDet
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi25.UG :
    ℕ → Type :=
    fun (N : ℕ) ↦ ↥(Matrix.unitaryGroup (Fin N) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qi25.ent :
    {N : ℕ} → UpperTheory.Reformulated.B.Qi25.UG N → Fin N × Fin N → ℂ :=
    fun {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) (ij : Fin N × Fin N) ↦ (↑g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2

noncomputable def UpperTheory.Reformulated.B.Qi25.IsPD :
    {N : ℕ} → (UpperTheory.Reformulated.B.Qi25.UG N → ℂ) → Prop :=
    fun {N : ℕ} (f : UpperTheory.Reformulated.B.Qi25.UG N → ℂ) ↦
      ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
        ∀ (g : UpperTheory.Reformulated.B.Qi25.UG N),
          f g * (↑g : Matrix (Fin N) (Fin N) ℂ).det ^ k =
            (MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g) : MvPolynomial (Fin N × Fin N) ℂ → ℂ) P

private theorem UpperTheory.Reformulated.B.Qi25.eval_det {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) :
    MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g)
        (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det =
      (↑g : Matrix (Fin N) (Fin N) ℂ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [UpperTheory.Reformulated.B.Qi25.ent]

theorem UpperTheory.Reformulated.B.Qi25.sum.{u_1} :
    ∀ {N : ℕ} {ι : Type u_1} (s : Finset ι) {F : ι → UpperTheory.Reformulated.B.Qi25.UG N → ℂ},
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi25.IsPD (F i)) → UpperTheory.Reformulated.B.Qi25.IsPD fun (g : UpperTheory.Reformulated.B.Qi25.UG N) ↦ ∑ i ∈ s, F i g := by
  intro N ι s F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, 0, fun g ↦ by simp⟩
  | insert a s ha ih =>
    intro h
    obtain ⟨k, P, hP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨l, Q, hQ⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨k + l,
      P * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ l
        + Q * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ k,
      fun g ↦ ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, UpperTheory.Reformulated.B.Qi25.eval_det, ← hP g, ← hQ g]
    simp only [Finset.sum_insert ha]
    ring
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanTopFamily
noncomputable def UpperTheory.Reformulated.B.SpanTopFamily.Mι :
    {E K : Type} →
      [inst : Field E] →
        [inst_1 : Field K] →
          (O : ValuationSubring K) →
            (E →+* K) → {n : Type} → Submodule (NumberField.RingOfIntegers E) (n → E) → Submodule (↥O) (n → K) :=
    fun {E K : Type} [Field E] [Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
        (L : Submodule (NumberField.RingOfIntegers E) (n → E)) ↦
      Submodule.span (↥O) ((fun (l : n → E) (j : n) ↦ (ι : E → K) (l j)) '' (↑L : Set (n → E)))

theorem UpperTheory.Reformulated.B.SpanTopFamily.span_top :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by
  intro E K _ _ _ O ι n _ _ L hL
  have key : ∀ v : n → E, v ∈ Submodule.span E (↑L : Set (n → E)) →
      (fun j => ι (v j)) ∈ Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero =>
      have : (fun j : n => ι ((0 : n → E) j)) = 0 := by
        funext j; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun j : n => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
        funext j; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : (fun j : n => ι ((a • x) j)) = ι a • (fun j => ι (x j)) := by
        funext j; simp
      rw [this]; exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ' w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := key (Pi.single i 1) (by rw [hL]; trivial)
  have e : (fun j : n => ι ((Pi.single i 1 : n → E) j)) = Pi.single i (1 : K) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [e] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitBall
noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.UnitBallLemmas.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

private def UpperTheory.Reformulated.B.UnitBallLemmas.unitBall (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv F →
        (MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F = (1 : ℂ_[p]) →
          ∃ (G : MvPowerSeries σ ℂ_[p]), UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv G ∧ F * G = (1 : MvPowerSeries σ ℂ_[p]) := by
  intro p _ σ F hF h1
  let F' : MvPowerSeries σ (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) :=
    fun n => ⟨MvPowerSeries.coeff n F, hF n⟩
  have hmap : MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype F' = F := by
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  have hc : MvPowerSeries.constantCoeff F' = ((1 : (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p)ˣ) : UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) := by
    apply Subtype.ext
    exact h1
  refine ⟨MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype (MvPowerSeries.invOfUnit F' 1), ?_, ?_⟩
  · intro n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n (MvPowerSeries.invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, MvPowerSeries.mul_invOfUnit F' 1 hc, map_one]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasStrictFDerivAtEval
noncomputable def UpperTheory.Reformulated.B.Qi29.polyDeriv :
    {n : ℕ} → MvPolynomial (Fin n) ℂ → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) ↦
      ∑ l : Fin n,
        (MvPolynomial.eval fun (i : Fin n) ↦ x.ofLp i : MvPolynomial (Fin n) ℂ → ℂ)
            ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) p) •
          EuclideanSpace.proj l

theorem UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval :
    ∀ {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)),
      HasStrictFDerivAt
        (fun (y : EuclideanSpace ℂ (Fin n)) ↦ (MvPolynomial.eval fun (i : Fin n) ↦ y.ofLp i : MvPolynomial (Fin n) ℂ → ℂ) p)
        (UpperTheory.Reformulated.B.Qi29.polyDeriv p x) x := by
  intro n p x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (MvPolynomial.C a : MvPolynomial (Fin n) ℂ) x = 0 := by
      simp [UpperTheory.Reformulated.B.Qi29.polyDeriv]
    rw [h]
    simp only [MvPolynomial.eval_C]
    exact hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p + q) x
        = UpperTheory.Reformulated.B.Qi29.polyDeriv p x + UpperTheory.Reformulated.B.Qi29.polyDeriv q x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, map_add (f := _), add_smul, Finset.sum_add_distrib]
    rw [h]
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦ y.ofLp i)
        (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) x :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasStrictFDerivAt
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p * MvPolynomial.X i) x
        = (MvPolynomial.eval (fun j : Fin n ↦ x.ofLp j) p) •
            (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
          + (x.ofLp i) • UpperTheory.Reformulated.B.Qi29.polyDeriv p x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul,
        MvPolynomial.eval_X, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [MvPolynomial.pderiv_X_of_ne hb.symm]
      · simp
    rw [h]
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul hi
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClosureUpperUni
noncomputable def UpperTheory.Reformulated.B.Qe27.upperUni :
    (k : ℕ) → (A : Type) → [inst : CommRing A] → Set (GL (Fin k) A) :=
    fun (k : ℕ) (A : Type) [CommRing A] ↦
      {x : GL (Fin k) A |
        ∀ (i j : Fin k),
          (j < i → (↑x : Matrix (Fin k) (Fin k) A) i j = (0 : A)) ∧ (↑x : Matrix (Fin k) (Fin k) A) i i = (1 : A)}

private theorem UpperTheory.Reformulated.B.Qe27.diag_mul {k : ℕ} {A : Type} [CommRing A]
    (M N : Matrix (Fin k) (Fin k) A) (hM : M.BlockTriangular id) (hN : N.BlockTriangular id)
    (i : Fin k) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hM (show id j < id i from h), zero_mul]
  · rw [hN (show id i < id j from h), mul_zero]

private theorem UpperTheory.Reformulated.B.Qe27.mem_iff {k : ℕ} {A : Type} [CommRing A] (x : GL (Fin k) A) :
    x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A ↔
      (x : Matrix (Fin k) (Fin k) A).BlockTriangular id ∧
        ∀ i, (x : Matrix (Fin k) (Fin k) A) i i = 1 :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
    fun h i _ => ⟨fun hij => h.1 hij, h.2 i⟩⟩

theorem UpperTheory.Reformulated.B.Qe27.closure_upperUni :
    ∀ {k : ℕ} (A : Type) [inst : CommRing A],
      ∀ x ∈ Subgroup.closure (UpperTheory.Reformulated.B.Qe27.upperUni k A), x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A := by
  intro k A _ x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff]
    exact ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  | mul y z _ _ hy hz =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy hz ⊢
    rw [Units.val_mul]
    refine ⟨hy.1.mul hz.1, fun i => ?_⟩
    rw [UpperTheory.Reformulated.B.Qe27.diag_mul _ _ hy.1 hz.1, hy.2, hz.2, one_mul]
  | inv y _ hy =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy ⊢
    have hinv : ((y⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).BlockTriangular id := by
      letI : Invertible (y : Matrix (Fin k) (Fin k) A) := y.invertible
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hy.1
    refine ⟨hinv, fun i => ?_⟩
    have h := UpperTheory.Reformulated.B.Qe27.diag_mul _ _ hy.1 hinv i
    rw [Units.mul_inv, Matrix.one_apply_eq, hy.2, one_mul] at h
    exact h.symm
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulMemIntA
/-!
# Multiplicative Closure of Integral Finite Adeles `intA`

Condensed from 4,973 lines of `pp.explicit` signature dumps (including a 2,647-line
signature proved by `rfl`) down to ~55 lines of idiomatic Lean 4.
-/

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace UpperTheory.Reformulated.B.Uc13

@[reducible] noncomputable def Af (F : Type) [Field F] [NumberField F] : Type :=
  FiniteAdeleRing (𝓞 F) F

@[reducible] noncomputable def Fv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : Type :=
  v.adicCompletion F

noncomputable def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}

theorem intAf_mul (F : Type) [Field F] [NumberField F] {a b : Af F}
    (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F :=
  fun v => mul_mem (ha v) (hb v)

noncomputable def intA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a ∈ intAf F, ∃ s : 𝓞 E, z = a ⊗ₜ[F] (s : E)}

theorem mul_mem_intA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {x y : Af F ⊗[F] E} (hx : x ∈ intA F E) (hy : y ∈ intA F E) :
    x * y ∈ intA F E := by
  unfold intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a * b, intAf_mul F ha hb, s * t, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero_left _ _ => rw [zero_mul]; exact zero_mem _
  | zero_right _ _ => rw [mul_zero]; exact zero_mem _
  | add_left _ _ _ _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right _ _ _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left _ _ _ _ h => rw [neg_mul]; exact neg_mem h
  | neg_right _ _ _ _ h => rw [mul_neg]; exact neg_mem h

end UpperTheory.Reformulated.B.Uc13
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemWOfNorm
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.kb :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ AlgebraicClosure (ZMod p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.WW :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ WittVector p (UpperTheory.Reformulated.B.Qi32.kb p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.K0 :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ FractionRing (UpperTheory.Reformulated.B.Qi32.WW p)

theorem UpperTheory.Reformulated.B.Qi32.mem_W_of_norm :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (i0 : UpperTheory.Reformulated.B.Qi32.K0 p →+* ℂ_[p]),
      (∀ (x : UpperTheory.Reformulated.B.Qi32.WW p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p])
                ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  x)‖ ≤
            (1 : ℝ)) →
        ∀ (x : UpperTheory.Reformulated.B.Qi32.K0 p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p]) x‖ ≤ (1 : ℝ) →
            ∃ (w : UpperTheory.Reformulated.B.Qi32.WW p),
              (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  w =
                x := by
  intro p inst i0 hW x hx
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
    rw [h, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rcases ValuationRing.isInteger_or_isInteger (UpperTheory.Reformulated.B.Qi32.WW p) x with h | ⟨w, hw⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, map_zero _⟩
  by_cases hu : IsUnit w
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : (UpperTheory.Reformulated.B.Qi32.WW p)ˣ) : UpperTheory.Reformulated.B.Qi32.WW p), ?_⟩
    rw [map_units_inv, hw, inv_inv]
  · exfalso
    have hirr : Irreducible (p : UpperTheory.Reformulated.B.Qi32.WW p) := WittVector.irreducible p
    have hmem : w ∈ IsLocalRing.maximalIdeal (UpperTheory.Reformulated.B.Qi32.WW p) := hu
    rw [hirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨v, rfl⟩ := hmem
    have h1 : ‖i0 x‖ * ‖i0 x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h2 : ‖i0 x⁻¹‖ < 1 := by
      rw [← hw, map_mul, map_mul, map_natCast, map_natCast, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hW v)) hp
    have h3 : ‖i0 x‖ * ‖i0 x⁻¹‖ ≤ ‖i0 x⁻¹‖ := mul_le_of_le_one_left (norm_nonneg _) hx
    linarith
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomWProd
noncomputable def UpperTheory.Reformulated.B.Qi22.wsum.{v} :
    {ι : Type v} → (ι → ℤ) → (ι →₀ ℕ) → ℤ :=
    fun {ι : Type v} (w : ι → ℤ) (n : ι →₀ ℕ) ↦ n.sum fun (x : ι) (k : ℕ) ↦ (↑k : ℤ) * w x

noncomputable def UpperTheory.Reformulated.B.Qi22.HomW.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → (ι → ℤ) → ℤ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), (MvPowerSeries.coeff n : MvPowerSeries ι K → K) f ≠ (0 : K) → UpperTheory.Reformulated.B.Qi22.wsum w n = c

private theorem UpperTheory.Reformulated.B.Qi22.wsum_add {ι : Type*} (w : ι → ℤ) (a b : ι →₀ ℕ) :
    UpperTheory.Reformulated.B.Qi22.wsum w (a + b) = UpperTheory.Reformulated.B.Qi22.wsum w a + UpperTheory.Reformulated.B.Qi22.wsum w b := by
  unfold UpperTheory.Reformulated.B.Qi22.wsum
  apply Finsupp.sum_add_index'
  · intro x; simp
  · intro x p q; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qi22.homW_one {K : Type*} [NormedField K] {ι : Type*} (w : ι → ℤ) :
    UpperTheory.Reformulated.B.Qi22.HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  have h0 : n = 0 := by
    by_contra h
    exact hn (by rw [MvPowerSeries.coeff_one, if_neg h])
  subst h0
  simp [UpperTheory.Reformulated.B.Qi22.wsum]

private theorem UpperTheory.Reformulated.B.Qi22.homW_mul {K : Type*} [NormedField K] {ι : Type*} {w : ι → ℤ}
    {c d : ℤ} {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qi22.HomW w c f)
    (hg : UpperTheory.Reformulated.B.Qi22.HomW w d g) : UpperTheory.Reformulated.B.Qi22.HomW w (c + d) (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : p.1 + p.2 = n := by simpa using hp
  rw [← hsum, UpperTheory.Reformulated.B.Qi22.wsum_add, hf p.1 (left_ne_zero_of_mul hne),
    hg p.2 (right_ne_zero_of_mul hne)]

theorem UpperTheory.Reformulated.B.Qi22.homW_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} {w : ι → ℤ} {α : Type w} (s : Finset α) (c : α → ℤ)
      (F : α → MvPowerSeries ι K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi22.HomW w (c i) (F i)) → UpperTheory.Reformulated.B.Qi22.HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  intro K inst ι w α s c F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using UpperTheory.Reformulated.B.Qi22.homW_one (K := K) w
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qi22.homW_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsCMOfConjAlt
open NumberField

theorem UpperTheory.Reformulated.B.Qh9.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice inferInstance
  have hfix : ∀ x : K, c x = x ↔ x ∈ maximalRealSubfield K := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx φ
      have := hc x φ
      rw [hx] at this
      exact this.symm
    · intro hx
      apply φ₀.injective
      rw [hc]
      exact hx φ₀
  have hinv : ∀ x : K, c (c x) = x := by
    intro x
    apply φ₀.injective
    simp [hc]
  let σ : K ≃ₐ[maximalRealSubfield K] K :=
    { toFun := c
      invFun := c
      left_inv := hinv
      right_inv := hinv
      map_mul' := fun x y => φ₀.injective (by simp [hc])
      map_add' := fun x y => φ₀.injective (by simp [hc])
      commutes' := fun x => (hfix _).mpr x.2 }
  have hσ : ∀ x, σ x = c x := fun _ => rfl
  have hne : σ ≠ 1 := by
    intro h1
    apply IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x = x := by rw [← hσ, h1]; rfl
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, hx]
  have hord : orderOf σ = 2 :=
    orderOf_eq_prime (by ext x; simp [pow_two, hσ, hinv]) hne
  have hbot : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.mpr
      ⟨⟨x, (hfix x).mp (hx σ (Subgroup.mem_zpowers σ))⟩, rfl⟩
  have hrank := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers, hord] at hrank
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := ⟨hrank⟩
  exact ⟨⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyTransformPreservesForm
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

noncomputable def UpperTheory.Reformulated.B.Qk20.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk20.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qk20.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qk20.Hpk k r + UpperTheory.Reformulated.B.Qk20.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk20.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qk20.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qk20.UH (UpperTheory.Reformulated.B.Qk20.Hpk k r)

noncomputable def UpperTheory.Reformulated.B.Qk20.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qk20.Mat k r → UpperTheory.Reformulated.B.Qk20.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)⁻¹

private theorem UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form {n : Type} [Fintype n] [DecidableEq n]
    (H Y : Matrix n n ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, one_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hinv, Matrix.conjTranspose_one, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.Qk20.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qk20.Mat k r},
      UpperTheory.Reformulated.B.Qk20.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qk20.kap Y ∈ UpperTheory.Reformulated.B.Qk20.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form (UpperTheory.Reformulated.B.Qk20.Hpk k r) Y h hu
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvDecomp
theorem UpperTheory.Reformulated.B.Qf39.ev_decomp :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    ∃ (h : σ → MvPowerSeries σ O),
      f =
          (MvPowerSeries.C : O → MvPowerSeries σ O) ((MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f) +
            ∑ i : σ, MvPowerSeries.X i * h i ∧
        ∀ (i : σ),
          (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) (h i) =
            (MvPowerSeries.coeff fun₀ | i => (1 : ℕ) : MvPowerSeries σ O → O) f := by
  intro O σ _ _ f
  classical
  have key : ∀ m : σ →₀ ℕ, ∃ o : Option σ,
      (m ≠ 0 → ∃ j, o = some j) ∧ ∀ j, o = some j → m j ≠ 0 := by
    intro m
    by_cases hm : m = 0
    · exact ⟨none, fun h => (h hm).elim, fun j hj => by cases hj⟩
    · obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hm
      refine ⟨some j, fun _ => ⟨j, rfl⟩, fun k hk => ?_⟩
      cases hk
      simpa using hj
  choose c hc₁ hc₂ using key
  let h : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hh : ∀ i m, MvPowerSeries.coeff m (h i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have hX : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * h i) =
      if c m = some i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hle : Finsupp.single i 1 ≤ m
    · rw [if_pos hle, hh, tsub_add_cancel_of_le hle]
    · rw [if_neg hle, if_neg]
      intro hi
      exact hle (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (hc₂ m i hi)))
  refine ⟨h, ?_, fun i => ?_⟩
  · ext m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, MvPowerSeries.coeff_C]
    simp only [hX]
    by_cases hm : m = 0
    · subst hm
      have : ∀ i, ¬ c 0 = some i := fun i hi => hc₂ 0 i hi rfl
      simp [this]
    · obtain ⟨j, hj⟩ := hc₁ m hm
      simp [hm, hj]
  · have hne : (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 := by simp
    obtain ⟨j, hj⟩ := hc₁ _ hne
    have hji : j = i := by
      by_contra hji
      exact hc₂ _ j hj (Finsupp.single_eq_of_ne hji)
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh, zero_add, if_pos (hji ▸ hj)]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MsMul
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.XZ :
    Type → ℕ → ℕ → Type :=
    fun (Lt : Type) (N0 N1 : ℕ) ↦ Lt × ℕ × Fin N0 ⊕ Lt × Fin N0 × Fin N1

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.PolyXZ :
    Type → ℕ → ℕ → Type :=
    fun (H : Type) (N0 N1 : ℕ) ↦ MvPolynomial (UpperTheory.Reformulated.B.Qj21.XZ (Bool × H) N0 N1) ℤ

noncomputable def UpperTheory.Reformulated.B.Qj21.lfo :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ × Fin N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (c : ℕ × Fin N1) ↦
      ∑ a : Fin N0, MvPolynomial.X (Sum.inl ((Bool.false, t), c.1, a)) * MvPolynomial.X (Sum.inr ((Bool.false, t), a, c.2))

noncomputable def UpperTheory.Reformulated.B.Qj21.tmL :
    {H : Type} → {N0 N1 : ℕ} → H → List (ℕ × Fin N1) → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (L : List (ℕ × Fin N1)) (h : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ↦
      (List.map (UpperTheory.Reformulated.B.Qj21.lfo t) L).prod * h

noncomputable def UpperTheory.Reformulated.B.Qj21.nzc :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (0 : ℕ) else (1 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.z0c :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (1 : ℕ) else (0 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.MS :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ → ℕ → Submodule ℤ (UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (a b : ℕ) ↦
      Submodule.span ℤ
        {Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 |
          ∃ (L : List (ℕ × Fin N1)),
            Q = UpperTheory.Reformulated.B.Qj21.tmL t L (1 : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ∧
              UpperTheory.Reformulated.B.Qj21.nzc L = a ∧ UpperTheory.Reformulated.B.Qj21.z0c L = b}

theorem UpperTheory.Reformulated.B.Qj21.ms_mul :
    ∀ {H : Type} {N0 N1 : ℕ} (t : H) {a b a' b' : ℕ} {P Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1},
      P ∈ UpperTheory.Reformulated.B.Qj21.MS t a b → Q ∈ UpperTheory.Reformulated.B.Qj21.MS t a' b' → P * Q ∈ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
  intro H N0 N1 t a b a' b' P Q hP hQ
  have key : UpperTheory.Reformulated.B.Qj21.MS (N0 := N0) (N1 := N1) t a b * UpperTheory.Reformulated.B.Qj21.MS t a' b'
      ≤ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
    unfold UpperTheory.Reformulated.B.Qj21.MS
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨x, ⟨L, rfl, h1, h2⟩, y, ⟨L', rfl, h3, h4⟩, rfl⟩
    refine ⟨L ++ L', ?_, ?_, ?_⟩
    · simp only [UpperTheory.Reformulated.B.Qj21.tmL, List.map_append, List.prod_append, mul_one]
    · rw [← h1, ← h3]
      simp only [UpperTheory.Reformulated.B.Qj21.nzc, List.map_append, List.sum_append]
    · rw [← h2, ← h4]
      simp only [UpperTheory.Reformulated.B.Qj21.z0c, List.map_append, List.sum_append]
  exact key (Submodule.mul_mem_mul hP hQ)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InclR
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh24.Fv :
    (F : Type) →
      [inst : Field F] → [NumberField F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → Type :=
    fun (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

noncomputable def UpperTheory.Reformulated.B.Qh24.inclR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] → (R : Type) → [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] ↦
      Algebra.TensorProduct.includeRight.toRingHom

noncomputable def UpperTheory.Reformulated.B.Qh24.OEv :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
                Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E) :=
    fun {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      (↑(Submodule.span (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
            ((fun (x : NumberField.RingOfIntegers E) ↦
                (UpperTheory.Reformulated.B.Qh24.inclR (UpperTheory.Reformulated.B.Qh24.Fv F v) : E → TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E)
                  (↑x : E)) ''
              Set.univ)) :
        Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E))

theorem UpperTheory.Reformulated.B.Qh24.oev_mul :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      {s t : TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E},
      s ∈ UpperTheory.Reformulated.B.Qh24.OEv v → t ∈ UpperTheory.Reformulated.B.Qh24.OEv v → s * t ∈ UpperTheory.Reformulated.B.Qh24.OEv v := by
  intro F E _ _ _ _ _ v s t hs ht
  unfold UpperTheory.Reformulated.B.Qh24.OEv at *
  simp only [SetLike.mem_coe] at *
  induction hs using Submodule.span_induction with
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  | mem a ha =>
    induction ht using Submodule.span_induction with
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
    | mem b hb =>
      obtain ⟨x, -, rfl⟩ := ha
      obtain ⟨y, -, rfl⟩ := hb
      refine Submodule.subset_span ⟨x * y, Set.mem_univ _, ?_⟩
      beta_reduce
      rw [← map_mul]
      rfl
end
