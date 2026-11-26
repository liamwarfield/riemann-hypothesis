module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjoinStableAndCommutes
namespace GlobalTheory.AdjoinStableCommutes

theorem adjoin_stable_and_commutes {E V G : Type} [Field E] [AddCommGroup V] [Module E V]
    (A : Set GlobalTheory.KZ.Letter) (f : GlobalTheory.KZ.Letter → Module.End E V) (W : Submodule E V)
    (g : G → Module.End E V)
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W)
    (hg : ∀ T ∈ A, ∀ (s : G), ∀ x ∈ W, f T (g s x) = g s (f T x)) :
    ∀ Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A), ∀ x ∈ W,
      (FreeAlgebra.lift E f Q) x ∈ W ∧
        ∀ s : G, g s ((FreeAlgebra.lift E f Q) x) = (FreeAlgebra.lift E f Q) (g s x) := by
  intro Q hQ
  induction hQ using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro x hx
    rw [FreeAlgebra.lift_ι_apply]
    exact ⟨hW T hT x hx, fun s => (hg T hT s x hx).symm⟩
  | algebraMap r =>
    intro x hx
    rw [AlgHom.commutes]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hx
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add a b _ _ ha hb =>
    intro x hx
    rw [map_add (f := _)]
    refine ⟨?_, fun s => ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (ha x hx).1 (hb x hx).1
    · rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), (ha x hx).2 s, (hb x hx).2 s]
  | mul a b _ _ ha hb =>
    intro x hx
    rw [map_mul]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.End.mul_apply]
      exact (ha _ (hb x hx).1).1
    · rw [Module.End.mul_apply, Module.End.mul_apply, (ha _ (hb x hx).1).2 s, (hb x hx).2 s]

end GlobalTheory.AdjoinStableCommutes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelation
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.CayleyHamiltonId

theorem exists_decomp {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (P : ι → ι → Module.End E U)
    (hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0)
    (h1 : ∑ i, P i i = 1) :
    ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (ι → E)) (s : Fin m → (ι → E) →ₗ[E] U),
      (∀ i (M : Matrix ι ι E), π i ∘ₗ (∑ a, ∑ b, M a b • P a b) = Matrix.toLin' M ∘ₗ π i) ∧
      (∀ i (M : Matrix ι ι E), (∑ a, ∑ b, M a b • P a b) ∘ₗ s i = s i ∘ₗ Matrix.toLin' M) ∧
      (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧
      ∑ i, s i ∘ₗ π i = LinearMap.id := by
  classical
  have hPa : ∀ i j k l u, P i j (P k l u) = if j = k then P i l u else 0 := by
    intro i j k l u
    have := LinearMap.congr_fun (hP i j k l) u
    rw [Module.End.mul_apply] at this
    rw [this]; split_ifs <;> rfl
  set W := LinearMap.range (P i₀ i₀)
  have hW : ∀ k u, P i₀ k u ∈ W := fun k u => ⟨P i₀ k u, by rw [hPa, if_pos rfl]⟩
  have hfix : ∀ w ∈ W, P i₀ i₀ w = w := by
    rintro _ ⟨u, rfl⟩; rw [hPa, if_pos rfl]
  let b := Module.finBasis E W
  let π : Fin (Module.finrank E W) → U →ₗ[E] (ι → E) :=
    fun i => LinearMap.pi fun k => (b.coord i).comp (LinearMap.codRestrict W (P i₀ k) (hW k))
  let s : Fin (Module.finrank E W) → (ι → E) →ₗ[E] U :=
    fun i => ∑ k, (LinearMap.proj k : (ι → E) →ₗ[E] E).smulRight (P k i₀ (b i))
  have hπ : ∀ i u k, π i u k = b.repr ⟨P i₀ k u, hW k u⟩ i := fun i u k => rfl
  have hs : ∀ i v, s i v = ∑ k, v k • P k i₀ (b i) := by
    intro i v; simp [s, LinearMap.sum_apply]
  have hrec : ∀ k u, ∑ i, b.repr ⟨P i₀ k u, hW k u⟩ i • (b i : U) = P i₀ k u := by
    intro k u
    have h' := congrArg Subtype.val (b.sum_repr ⟨P i₀ k u, hW k u⟩)
    rw [Submodule.coe_sum] at h'
    simpa only [Submodule.coe_smul] using h'
  refine ⟨Module.finrank E W, π, s, ?_, ?_, ?_, ?_⟩
  · intro i M
    ext u k
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hπ]
    have e : (⟨P i₀ k ((∑ a, ∑ b', M a b' • P a b') u), hW k _⟩ : W)
        = ∑ b', M k b' • (⟨P i₀ b' u, hW b' u⟩ : W) := by
      apply Subtype.ext
      set_option synthInstance.maxHeartbeats 100000 in
        simp [LinearMap.sum_apply, map_sum, map_smul, hPa]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finsupp.finsetSum_apply]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hπ]
  · intro i M
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [LinearMap.sum_apply, map_sum, map_smul, hPa, Matrix.mulVec, dotProduct, Finset.sum_smul,
      mul_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  · intro i j
    refine LinearMap.ext fun v => funext fun k => ?_
    simp only [LinearMap.comp_apply, hπ, hs]
    have e : (⟨P i₀ k (∑ l, v l • P l i₀ (b j)), hW k _⟩ : W) = v k • b j := by
      apply Subtype.ext
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_smul, hPa, hfix _ (b j).2]
    rw [e]
    split_ifs with h
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  · ext u
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hs, hπ, LinearMap.id_apply]
    rw [Finset.sum_comm]
    have hk : ∀ k, ∑ x, b.repr ⟨P i₀ k u, hW k u⟩ x • P k i₀ (b x) = P k k u := by
      intro k
      have := congrArg (P k i₀) (hrec k u)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [map_smul] at this
      rw [this, hPa, if_pos rfl]
    simp only [hk]
    rw [← LinearMap.sum_apply, h1, Module.End.one_apply]

theorem isotypic_of_quadratic_relation : ∀ {E : Type} [Field E] [IsAlgClosed E], (2 : E) ≠ 0 → ∀ {G : Type} [Group G] (ρ : G →* GL (Fin 2) E), (∀ W : Submodule E (Fin 2 → E), (∀ g w, w ∈ W → (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] (σ : G →* Module.End E U), (∀ g, σ g * σ g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σ g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0) → ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (Fin 2 → E)) (s : Fin m → (Fin 2 → E) →ₗ[E] U), (∀ i g, π i ∘ₗ σ g = Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E) ∘ₗ π i) ∧ (∀ i g, σ g ∘ₗ s i = s i ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)) ∧ (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧ ∑ i, s i ∘ₗ π i = LinearMap.id := by
  intro E _ _ h2 G _ ρ hirr U _ _ _ σ hrel
  classical
  let R : G →* Matrix (Fin 2) (Fin 2) E := (Units.coeHom _).comp ρ
  have hRg : ∀ g, R g = (ρ g : Matrix (Fin 2) (Fin 2) E) := fun g => rfl
  have hspan := GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R (fun W hW => hirr W hW)
  let Φ : MonoidAlgebra E G →ₐ[E] Module.End E U := MonoidAlgebra.lift E (Module.End E U) G σ
  let Ψ : MonoidAlgebra E G →ₐ[E] Matrix (Fin 2) (Fin 2) E :=
    MonoidAlgebra.lift E (Matrix (Fin 2) (Fin 2) E) G R
  have hΦ : ∀ g c, Φ (MonoidAlgebra.single g c) = c • σ g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hΨ : ∀ g c, Ψ (MonoidAlgebra.single g c) = c • R g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hsurj : ∀ M, ∃ y, Ψ y = M := by
    intro M
    have hle : Submodule.span E (Set.range R) ≤ LinearMap.range Ψ.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [hΨ]⟩
    obtain ⟨y, hy⟩ := hle (hspan ▸ Submodule.mem_top : M ∈ Submodule.span E (Set.range R))
    exact ⟨y, hy⟩

  have hinv : ∀ g, (R g).det • σ g⁻¹ = (R g).trace • 1 - σ g := by
    intro g
    have h := congrArg (· * σ g⁻¹) (hrel g)
    have hgg : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, hgg, mul_one, one_mul, zero_mul] at h
    rw [hRg]
    linear_combination (norm := module) h
  have hpair : ∀ g h, σ g * σ h + σ h * σ g - (R h).trace • σ g - (R g).trace • σ h
      + ((R g).trace * (R h).trace - (R g * R h).trace) • (1 : Module.End E U) = 0 := by
    intro g h
    have e1 := hinv (g * h)
    have e2 : (R (g*h)).det • σ (g*h)⁻¹ = ((R h).det • σ h⁻¹) * ((R g).det • σ g⁻¹) := by
      rw [_root_.mul_inv_rev, map_mul σ, map_mul R, det_mul, smul_mul_smul_comm, mul_comm (R g).det]
    rw [e2, hinv g, hinv h, map_mul σ, map_mul R] at e1
    simp only [mul_sub, sub_mul, smul_mul_smul_comm, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm] at e1
    linear_combination (norm := module) e1
  have hB : ∀ x y, Φ x * Φ y + Φ y * Φ x - (Ψ y).trace • Φ x - (Ψ x).trace • Φ y
      + ((Ψ x).trace * (Ψ y).trace - (Ψ x * Ψ y).trace) • (1 : Module.End E U) = 0 := by
    intro x y
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add (f := _), add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
      linear_combination (norm := module) h₁ + h₂
    | single g c =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add (f := _), add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
        linear_combination (norm := module) h₁ + h₂
      | single h d =>
        simp only [hΦ, hΨ, trace_smul, smul_mul_smul_comm, smul_eq_mul]
        linear_combination (norm := module) (c * d) • hpair g h

  have hanti : ∀ x y, Ψ x = 0 → Φ x * Φ y + Φ y * Φ x = (Ψ y).trace • Φ x := by
    intro x y hx
    have := hB x y
    simp only [hx, trace_zero, zero_mul, mul_zero, sub_self, zero_smul, add_zero, sub_zero] at this
    linear_combination (norm := module) this
  have h2c : ∀ X : Module.End E U, X + X = 0 → X = 0 := by
    intro X hX
    rw [← two_smul E X] at hX
    exact (smul_eq_zero.mp hX).resolve_left h2
  obtain ⟨y₁, hy₁⟩ := hsurj (Matrix.single 0 1 1)
  obtain ⟨y₂, hy₂⟩ := hsurj (Matrix.single 1 0 1)
  have hc : Ψ (y₁ * y₂ - y₂ * y₁) = !![1, 0; 0, -1] := by
    rw [map_sub, map_mul, map_mul, hy₁, hy₂]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  have hc2 : Ψ ((y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1) = 0 := by
    rw [map_sub, map_mul, hc, map_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ht1 : (Ψ y₁).trace = 0 := by rw [hy₁]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have ht2 : (Ψ y₂).trace = 0 := by rw [hy₂]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have htc : (Ψ (y₁ * y₂ - y₂ * y₁)).trace = 0 := by rw [hc]; simp [Matrix.trace, Fin.sum_univ_two]
  have hJ : ∀ x, Ψ x = 0 → Φ x = 0 := by
    intro x hx
    set N := Φ x
    set a := Φ y₁
    set b := Φ y₂
    have e1 : N * a = -(a * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₁ hx, ht1, zero_smul])
    have e2 : N * b = -(b * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₂ hx, ht2, zero_smul])
    have k1 : N * (a * b) = a * b * N := by
      rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, neg_neg, mul_assoc]
    have k2 : N * (b * a) = b * a * N := by
      rw [← mul_assoc, e2, neg_mul, mul_assoc, e1, mul_neg, neg_neg, mul_assoc]
    have hC : Φ (y₁ * y₂ - y₂ * y₁) = a * b - b * a := by rw [map_sub, map_mul, map_mul]
    have hNC : N * (a * b - b * a) = 0 := by
      have h3 := hanti x (y₁ * y₂ - y₂ * y₁) hx
      rw [htc, zero_smul, hC] at h3
      apply h2c
      have : (a * b - b * a) * N = N * (a * b - b * a) := by rw [mul_sub, sub_mul, k1, k2]
      rw [this] at h3; exact h3
    set x' := (y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1
    have hN' : Φ x' * Φ x' = 0 := by
      apply h2c
      rw [hanti x' x' hc2, hc2, trace_zero, zero_smul]
    have hNN' : N * Φ x' = -N := by
      have hx' : Φ x' = (a * b - b * a) * (a * b - b * a) - 1 := by
        simp only [x']; rw [map_sub, map_mul, hC, map_one]
      rw [hx', mul_sub, mul_one, ← mul_assoc, hNC, zero_mul, zero_sub]
    have h5 : N * Φ x' * Φ x' = 0 := by rw [mul_assoc, hN', mul_zero]
    rw [hNN', neg_mul, hNN', neg_neg] at h5
    exact h5

  have hΦeq : ∀ x y, Ψ x = Ψ y → Φ x = Φ y := by
    intro x y h
    have := hJ (x - y) (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  choose yP hyP using fun i j : Fin 2 => hsurj (Matrix.single i j 1)
  let P : Fin 2 → Fin 2 → Module.End E U := fun i j => Φ (yP i j)
  have hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0 := by
    intro i j k l
    simp only [P, ← map_mul]
    split_ifs with h
    · subst h
      apply hΦeq
      rw [map_mul, hyP, hyP, hyP, Matrix.single_mul_single_same, mul_one]
    · rw [← map_zero Φ]
      apply hΦeq
      rw [map_mul, hyP, hyP, map_zero]
      simp [h]
  have hsum : ∑ i, P i i = 1 := by
    simp only [P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_one Φ]
    apply hΦeq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [hyP]
    rw [Fin.sum_univ_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply]
  have hσ : ∀ g, σ g = ∑ a, ∑ b, (R g) a b • P a b := by
    intro g
    have e : σ g = Φ (MonoidAlgebra.single g 1) := by rw [hΦ, one_smul]
    rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, ← map_smul, ← map_sum]
    apply hΦeq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hΨ, hyP, one_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single (R g)
  obtain ⟨m, π, s, k1, k2, k3, k4⟩ := exists_decomp (0 : Fin 2) P hP hsum
  refine ⟨m, π, s, fun i g => ?_, fun i g => ?_, k3, k4⟩
  · rw [hσ g]; exact k1 i (R g)
  · rw [hσ g]; exact k2 i (R g)

end GlobalTheory.CayleyHamiltonId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelationStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_dim_rep_quadratic_relation : ∀ {E : Type} [Field E] [IsAlgClosed E], (2 : E) ≠ 0 → ∀ {G : Type} [Group G] (ρ : G →* GL (Fin 2) E), (∀ W : Submodule E (Fin 2 → E), (∀ g w, w ∈ W → (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] (σ : G →* Module.End E U), (∀ g, σ g * σ g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σ g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0) → ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (Fin 2 → E)) (s : Fin m → (Fin 2 → E) →ₗ[E] U), (∀ i g, π i ∘ₗ σ g = Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E) ∘ₗ π i) ∧ (∀ i g, σ g ∘ₗ s i = s i ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)) ∧ (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧ ∑ i, s i ∘ₗ π i = LinearMap.id := by
  first | exact @GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation | exact GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation | (intros; apply GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepresentationOfEigensystem
set_option maxHeartbeats 1600000

noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeProj

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem gal_mul_apply (X : Tower Ω ε) (s s' : Ω ≃ₐ[ℚ] Ω) (f : X.K) : X.gal (s * s') f = X.gal s (X.gal s' f) := by
  letI := X.fld; letI := X.alg
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  refine HahnSeries.ext (funext fun r => ?_)
  show (X.exp (X.gal (s * s') f)).coeff r = (X.exp (X.gal s (X.gal s' f))).coeff r
  rw [X.gal_exp, X.gal_exp, X.gal_exp, AlgEquiv.mul_apply]

theorem gal_one_apply (X : Tower Ω ε) (f : X.K) : X.gal 1 f = f := by
  letI := X.fld; letI := X.alg
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  refine HahnSeries.ext (funext fun r => ?_)
  show (X.exp (X.gal 1 f)).coeff r = (X.exp f).coeff r
  rw [X.gal_exp, AlgEquiv.one_apply]

theorem kmap_comp (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) :
    X.kmap l φ ∘ₗ X.kmap l ψ = X.kmap l (ψ.trans φ) := by
  letI := X.fld
  unfold Tower.kmap
  apply LinearMap.ext; intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [← LinearMap.comp_apply (AdicCompletion.map _ _), AdicCompletion.map_comp, ← LinearMap.baseChange_comp]
  have h : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) =
      AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (ψ.trans φ).toMonoidHom)) := by
    ext u; rfl
  rw [h]

theorem kmap_refl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.kmap l (RingEquiv.refl X.K) = LinearMap.id := by
  letI := X.fld
  unfold Tower.kmap
  have h : AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom)) =
      LinearMap.id := by
    ext u; rfl
  rw [h, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem galB_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s s' : Ω ≃ₐ[ℚ] Ω) :
    X.galB l (s * s') = X.galB l s ∘ₗ X.galB l s' := by
  have hg : X.gal (s * s') = (X.gal s').trans (X.gal s) := RingEquiv.ext (gal_mul_apply X s s')
  have hr : (s * s').toRingEquiv = s.toRingEquiv * s'.toRingEquiv := RingEquiv.ext fun x => rfl
  apply LinearMap.ext; intro b; funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (X.kmap l (X.gal s)), kmap_comp, ← hg, hr, map_mul, Units.val_mul]
  congr 2
  ext i; fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem galB_one (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.galB l 1 = LinearMap.id := by
  have hg : X.gal 1 = RingEquiv.refl X.K := RingEquiv.ext (gal_one_apply X)
  have hr : (1 : Ω ≃ₐ[ℚ] Ω).toRingEquiv = 1 := RingEquiv.ext fun x => rfl
  apply LinearMap.ext; intro b; funext u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  rw [hg, kmap_refl, hr, map_one, Units.val_one, one_mul, LinearMap.id_apply]
  congr 1
  ext i; fin_cases i <;> rfl

section BC
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] (E : Type) [Field E] [Algebra R E]
  (B : Submodule R M)

theorem bc_mem (f : M →ₗ[R] M) (hf : ∀ b ∈ B, f b ∈ B) (x : E ⊗[R] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange E B.subtype)) :
    LinearMap.baseChange E f x ∈ LinearMap.range (LinearMap.baseChange E B.subtype) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨LinearMap.baseChange E (f.restrict hf) y, ?_⟩
  have h : B.subtype ∘ₗ f.restrict hf = f ∘ₗ B.subtype := LinearMap.ext fun b => rfl
  have := congrArg (fun φ => LinearMap.baseChange E φ y) h
  simpa [LinearMap.baseChange_comp] using this

theorem bc_comm (f g : M →ₗ[R] M) (hfg : ∀ b ∈ B, f (g b) = g (f b)) (x : E ⊗[R] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange E B.subtype)) :
    LinearMap.baseChange E f (LinearMap.baseChange E g x) = LinearMap.baseChange E g (LinearMap.baseChange E f x) := by
  obtain ⟨y, rfl⟩ := hx
  have h : f ∘ₗ g ∘ₗ B.subtype = g ∘ₗ f ∘ₗ B.subtype := LinearMap.ext fun b => hfg b b.2
  have := congrArg (fun φ => LinearMap.baseChange E φ y) h
  simpa [LinearMap.baseChange_comp] using this

end BC

section Gen
variable {E V G : Type} [Field E] [AddCommGroup V] [Module E V]

theorem adj_eigen (A : Set Letter) (f : Letter → Module.End E V) (lam : Letter → E) (y : V)
    (hy : ∀ T ∈ A, f T y = lam T • y) (Q : FreeAlgebra E Letter)
    (hQ : Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A)) :
    FreeAlgebra.lift E f Q y = FreeAlgebra.lift E lam Q • y := by
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [FreeAlgebra.lift_ι_apply, hy T hT]
  | algebraMap r => simp
  | add a b _ _ ha hb => simp [ha, hb, add_smul]
  | mul a b _ _ ha hb => simp [Module.End.mul_apply, ha, hb, smul_smul, mul_comm]

theorem adj_stab (A : Set Letter) (f : Letter → Module.End E V) (W : Submodule E V) (g : G → Module.End E V)
    (hs : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) (hc : ∀ T ∈ A, ∀ s, ∀ x ∈ W, f T (g s x) = g s (f T x))
    (Q : FreeAlgebra E Letter) (hQ : Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A)) :
    ∀ x ∈ W, FreeAlgebra.lift E f Q x ∈ W ∧ ∀ s, g s (FreeAlgebra.lift E f Q x) = FreeAlgebra.lift E f Q (g s x) := by
  first
  | exact @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes
  | exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes
  | (apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinStableCommutes.adjoin_stable_and_commutes ..)

end Gen

end GlobalTheory.KZ.HeckeProj

namespace GlobalTheory.KZ.HeckeProj

theorem heckeProj_main : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E), X.SSBB N l w E lam → ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw E _ _ _ hnorm lam hSS ρ S0 htc hdc hfr hirr
  obtain ⟨P, hPadm, hP1, hPe⟩ := hSS
  have hgal : ∀ s, ∀ x ∈ X.VB N l w E, X.galV l E s x ∈ X.VB N l w E := fun s x hx =>
    HeckeProj.bc_mem E (X.B N l w) (X.galB l s) (GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s) x hx
  have hstab : ∀ T ∈ {T | admitted N l T}, ∀ x ∈ X.VB N l w E, X.opV N l E T x ∈ X.VB N l w E := fun T hT x hx =>
    HeckeProj.bc_mem E (X.B N l w) (X.op N l T) (GlobalTheory.T.hecke_letter_preserves_basis_set ε X hε hj N l w hl hN hNl hw T hT) x hx
  have hcomm : ∀ T ∈ {T | admitted N l T}, ∀ s, ∀ x ∈ X.VB N l w E,
      X.opV N l E T (X.galV l E s x) = X.galV l E s (X.opV N l E T x) := fun T hT s x hx =>
    HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.galB l s)
      (fun b hb => GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl hN hNl hw T hT s b hb) x hx
  have hfin : Module.Finite ℤ_[l] (X.B N l w) := (GlobalTheory.T.kummerBettiModule_free_finite ε X hε hj N l w hl hN hNl hw).2
  have hVBfin : FiniteDimensional E (X.VB N l w E) := by
    unfold Tower.VB; infer_instance
  set Pv := FreeAlgebra.lift E (X.opV N l E) P with hPv
  have hPst := HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E) (X.galV l E) hstab hcomm P hPadm
  have heig : ∀ x ∈ X.VB N l w E, ∀ T, admitted N l T → X.opV N l E T (Pv x) = lam T • Pv x := by
    intro x hx T hT
    have := hPe x hx T hT
    simpa [sub_eq_zero] using this
  have hfix : ∀ y, (∀ T, admitted N l T → X.opV N l E T y = lam T • y) → Pv y = y := by
    intro y hy
    have := HeckeProj.adj_eigen {T | admitted N l T} (X.opV N l E) lam y hy P hPadm
    rw [hP1, one_smul] at this
    exact this
  set U : Submodule E (E ⊗[ℤ_[l]] X.Fn l) := (X.VB N l w E).map Pv with hU
  have hUVB : ∀ u ∈ U, u ∈ X.VB N l w E := by
    rintro u ⟨x, hx, rfl⟩; exact (hPst x hx).1
  have hUeig : ∀ u ∈ U, ∀ T, admitted N l T → X.opV N l E T u = lam T • u := by
    rintro u ⟨x, hx, rfl⟩; exact heig x hx
  have hUfix : ∀ u ∈ U, Pv u = u := fun u hu => hfix u (hUeig u hu)
  have hUgal : ∀ s, ∀ u ∈ U, X.galV l E s u ∈ U := by
    rintro s u ⟨x, hx, rfl⟩
    exact ⟨X.galV l E s x, hgal s x hx, ((hPst x hx).2 s).symm⟩
  haveI : FiniteDimensional E U := by rw [hU]; infer_instance
  have hgm : ∀ s s', X.galV l E (s * s') = X.galV l E s * X.galV l E s' := by
    intro s s'
    simp only [Tower.galV, HeckeProj.galB_mul, LinearMap.baseChange_comp, Module.End.mul_eq_comp]
  have hg1 : X.galV l E 1 = 1 := by
    simp only [Tower.galV, HeckeProj.galB_one, LinearMap.baseChange_id, Module.End.one_eq_id]
  let σU : (Ω ≃ₐ[ℚ] Ω) →* Module.End E U :=
    { toFun := fun s => (X.galV l E s).restrict (hUgal s)
      map_one' := by
        ext u; simp [LinearMap.restrict_apply, hg1]
      map_mul' := by
        intro s s'; ext u; simp [LinearMap.restrict_apply, hgm, Module.End.mul_apply] }
  have hσU : ∀ s (u : U), ((σU s u : U) : E ⊗[ℤ_[l]] X.Fn l) = X.galV l E s u := fun s u => rfl
  have h2 : (2 : E) ≠ 0 := by
    intro h
    have h' : algebraMap ℤ_[l] E 2 = 0 := by rw [map_ofNat]; exact h
    have := hnorm 2
    rw [h', norm_zero] at this
    have h0 : (2 : ℤ_[l]) = 0 := norm_eq_zero.mp this.symm
    exact two_ne_zero h0
  have hCH : ∀ g, σU g * σU g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σU g +
      Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0 := by
    intro g
    ext u
    have hu := GlobalTheory.T.cayleyHamilton_heckeEigenvector_every_galois_element ε X hε hj N l w hl hN hNl hw hnorm lam
      (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E))
      S0 htc hdc hfr (u : E ⊗[ℤ_[l]] X.Fn l) (hUVB u u.2) (hUeig u u.2) g
    simpa [Module.End.mul_apply, hσU] using hu
  obtain ⟨m, π', s', h1, h2', h3, h4⟩ := GlobalTheory.T.two_dim_rep_quadratic_relation h2 ρ hirr σU hCH
  let Pr : X.VB N l w E →ₗ[E] U :=
    LinearMap.codRestrict U (Pv ∘ₗ (X.VB N l w E).subtype) (fun x => Submodule.mem_map_of_mem x.2)
  have hext : ∀ i : Fin m, ∃ g : (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E),
      g ∘ₗ (X.VB N l w E).subtype = π' i ∘ₗ Pr := fun i => LinearMap.exists_extend _
  choose π hπ using hext
  have hπx : ∀ i x (hx : x ∈ X.VB N l w E), π i x = π' i (Pr ⟨x, hx⟩) := fun i x hx =>
    LinearMap.congr_fun (hπ i) ⟨x, hx⟩
  have hTT : ∀ T ∈ {T | admitted N l T}, ∀ T' : {T // admitted N l T}, ∀ x ∈ X.VB N l w E,
      X.opV N l E T (X.opV N l E T'.1 x) = X.opV N l E T'.1 (X.opV N l E T x) := fun T hT T' x hx =>
    HeckeProj.bc_comm E (X.B N l w) (X.op N l T) (X.op N l T'.1)
      (fun b hb => GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X hε hj N l w hl hN hNl hw T T'.1 hT T'.2 b hb) x hx
  have hPT := HeckeProj.adj_stab {T | admitted N l T} (X.opV N l E) (X.VB N l w E)
    (fun T' : {T // admitted N l T} => X.opV N l E T'.1) hstab hTT P hPadm
  have hsumP : ∀ x ∈ X.VB N l w E, Pv x = ∑ i, (U.subtype ∘ₗ s' i) (π i x) := by
    intro x hx
    have := LinearMap.congr_fun h4 (Pr ⟨x, hx⟩)
    have e2 : (∑ i, s' i (π' i (Pr ⟨x, hx⟩))) = Pr ⟨x, hx⟩ := by simpa [LinearMap.sum_apply] using this
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, hπx _ x hx]
    rw [← Submodule.coe_sum, e2]
    rfl
  refine ⟨m, π, fun i => U.subtype ∘ₗ s' i, P, hPadm, hP1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hxe
    rw [← hsumP x hx]
    exact hfix x hxe
  · intro i v
    exact hUVB _ (s' i v).2
  · intro i s x hx
    rw [hπx i _ (hgal s x hx), hπx i x hx]
    have e : Pr ⟨X.galV l E s x, hgal s x hx⟩ = σU s (Pr ⟨x, hx⟩) := by
      apply Subtype.ext
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, hσU]
      exact ((hPst x hx).2 s).symm
    rw [e]
    have := LinearMap.congr_fun (h1 i s) (Pr ⟨x, hx⟩)
    simpa [Matrix.toLin'_apply] using this
  · intro i s v
    have := LinearMap.congr_fun (h2' i s) v
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [← hσU, this]
    simp [Matrix.toLin'_apply]
  · intro i T v hT
    exact hUeig _ (s' i v).2 T hT
  · intro i T hT x hx
    have hTx := hstab T hT x hx
    rw [hπx i _ hTx, hπx i x hx]
    have e : Pr ⟨X.opV N l E T x, hTx⟩ = lam T • Pr ⟨x, hx⟩ := by
      apply Subtype.ext
      have hc := (hPT x hx).2 ⟨T, hT⟩
      simp only at hc
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.coe_smul]
      rw [← hc]
      exact hUeig _ (Submodule.mem_map_of_mem hx) T hT
    rw [e, map_smul]
  · intro i j v
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [hπx i _ (hUVB _ (s' j v).2)]
    have e : Pr ⟨((s' j v : U) : E ⊗[ℤ_[l]] X.Fn l), hUVB _ (s' j v).2⟩ = s' j v := by
      apply Subtype.ext
      simp only [Pr, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype]
      exact hUfix _ (s' j v).2
    rw [e]
    have := LinearMap.congr_fun (h3 i j) v
    rw [LinearMap.comp_apply] at this
    rw [this]
    split_ifs <;> simp
  · intro x hx
    exact hsumP x hx

end GlobalTheory.KZ.HeckeProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepresentationOfEigensystemStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_representation_of_eigensystem : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E), X.SSBB N l w E lam → ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  first | (exact @GlobalTheory.KZ.HeckeProj.heckeProj_main) | (exact GlobalTheory.KZ.HeckeProj.heckeProj_main) | (intros; apply GlobalTheory.KZ.HeckeProj.heckeProj_main  <;> assumption)
end
