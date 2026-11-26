module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousConjBlockEmbedding

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanUnitaryElementLift
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanUnitaryElementLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit

section Lin

variable {A : Type} [CommRing A] {n m : ℕ}

theorem mulVec_eq_of_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hDC : D * C = 0) (hUC : ∀ i j, j ∈ I → (U * C) i j = 0)
    {y : Fin n → A} (hy : y ∈ Submodule.span A ((fun i => Cᵀ i) '' I)) : (1 + C * U + W * D) *ᵥ y = y := by
  obtain ⟨a, ha, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I y).1 hy
  have h1 : (U * C) *ᵥ a = 0 := funext fun i => by
    show ∑ l, (U * C) i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l ∈ I
    · rw [hUC i l hl, zero_mul]
    · rw [ha l hl, mul_zero]
  have h2 : (1 + C * U + W * D) *ᵥ (C *ᵥ a) = C *ᵥ a + C *ᵥ ((U * C) *ᵥ a) + W *ᵥ ((D * C) *ᵥ a) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec]
  rw [h2, h1, hDC]
  simp

theorem mulVec_sub_mem (C : Matrix (Fin n) (Fin m) A) (D : Matrix (Fin m) (Fin n) A) (U : Matrix (Fin m) (Fin n) A)
    (W : Matrix (Fin n) (Fin m) A) (I : Set (Fin m)) (hU : ∀ i v, i ∉ I → U i v = 0) {y : Fin n → A}
    (hy : W *ᵥ (D *ᵥ y) = 0) : (1 + C * U + W * D) *ᵥ y - y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) := by
  have h : (1 + C * U + W * D) *ᵥ y - y = C *ᵥ (U *ᵥ y) := by
    simp only [add_mulVec, one_mulVec, ← mulVec_mulVec, hy]
    abel
  rw [h]
  refine (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff C I _).2 ⟨U *ᵥ y, fun l hl => ?_, rfl⟩
  show ∑ v, U l v * y v = 0
  exact Finset.sum_eq_zero fun v _ => by rw [hU l v hl, zero_mul]

theorem mem_iff_of_fix {M : Matrix (Fin n) (Fin n) A} (hM : Function.Injective M.mulVec) (S : Submodule A (Fin n → A))
    (hS : ∀ y ∈ S, M *ᵥ y = y) (y : Fin n → A) : y ∈ S ↔ M *ᵥ y ∈ S :=
  ⟨fun h => by rwa [hS y h], fun h => by rwa [← hM (hS _ h)]⟩

end Lin

theorem mem_unip {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin m) E) (T : Finset (Fin m)) (g : GAd σ J)
    (U : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) (W : Matrix (Fin n) (Fin m) (AF F ⊗[F] E))
    (hX : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hU : ∀ i v, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → U i v = 0)
    (hW : ∀ v i, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → W v i = 0)
    (hUX : ∀ i j, j ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → (U * GlobalTheory.SiegelSet.adMat F X) i j = 0)
    (hg : (GlobalTheory.AdelicU.matHom _ σ J g).1 =
      1 + GlobalTheory.SiegelSet.adMat F X * U + W * GlobalTheory.SiegelSet.adMat F (Formalism.UG.cT (σ : E →+* E) X * J)) :
    g ∈ GlobalTheory.StdPar.unip σ J X T := by
  have hDC : adMat F (Formalism.UG.cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [adMat, adMat, ← Matrix.map_mul, hX]
    exact Matrix.map_zero _ (map_zero _)
  have hinj : Function.Injective (GlobalTheory.AdelicU.matHom _ σ J g).1.mulVec :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit _)
  have hfix : ∀ y ∈ colSpan F X (upTo T), (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    rw [hg]
    exact mulVec_eq_of_mem _ _ U W _ hDC hUX hy
  have hsub : ∀ y, W *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) = 0 →
      (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y - y ∈ colSpan F X (upTo T) := fun y hy => by
    rw [hg]
    exact mulVec_sub_mem _ _ U W _ hU hy
  have hiff : ∀ S ≤ colSpan F X (upTo T), ∀ y, y ∈ S ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y ∈ S := fun S hS =>
    mem_iff_of_fix hinj S fun y hy => hfix y (hS hy)
  refine ⟨Subgroup.mem_iInf.2 fun j => ?_, hiff _ le_rfl, fun y hy => hsub y ?_⟩
  · by_cases hj : j ∈ upTo T
    · have hA : colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono fun i ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩)
      have hB : colSpan F X {j} ≤ colSpan F X (upTo T) :=
        Submodule.span_mono (Set.image_mono (Set.singleton_subset_iff.2 hj))
      refine ⟨hiff _ hA, fun y hy => ?_⟩
      rw [hfix y (hB hy), sub_self]
      exact zero_mem _
    · have hA : {i | ∃ k ∈ T, i ≤ k ∧ k < j} = upTo T := Set.ext fun i =>
        ⟨fun ⟨k, hk, hik, _⟩ => ⟨k, hk, hik⟩, fun ⟨k, hk, hik⟩ =>
          ⟨k, hk, hik, not_le.1 fun h => hj ⟨k, hk, h⟩⟩⟩
      rw [hA]
      refine ⟨hiff _ le_rfl, fun y hy => hsub y ?_⟩
      obtain ⟨a, -, rfl⟩ := (GlobalTheory.StdPar.UnipArch.mem_span_cols_iff _ _ y).1 hy
      rw [mulVec_mulVec a, hDC, zero_mulVec, mulVec_zero]
  · funext v
    show ∑ i, W v i * (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ upTo T
    · have h : (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0 := by
        simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
        exact hy i hi
      rw [h, mul_zero]
    · rw [hW v i hi, zero_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanUnitaryElementLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_unipotent_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin m) E) (T : Finset (Fin m)) (g : GAd σ J)
    (U : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) (W : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)),
    Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → (∀ i v, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → U i v = 0) →
    (∀ v i, i ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → W v i = 0) →
    (∀ i j, j ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → (U * GlobalTheory.SiegelSet.adMat F X) i j = 0) →
    (GlobalTheory.AdelicU.matHom _ σ J g).1 = 1 + GlobalTheory.SiegelSet.adMat F X * U + W * GlobalTheory.SiegelSet.adMat F (Formalism.UG.cT (σ : E →+* E) X * J) →
    g ∈ GlobalTheory.StdPar.unip σ J X T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip | exact GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.UnipCrit.mem_unip <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNe
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNe
open Matrix

namespace GlobalTheory.CompanionTheory.EichlerTransf

open scoped ComplexOrder

variable {n m : ℕ}

theorem mulVec_column {p q r : ℕ} (N : Matrix (Fin p) (Fin q) ℂ) (M : Matrix (Fin q) (Fin r) ℂ)
    (i : Fin r) : (N *ᵥ fun j => M j i) = fun j => (N * M) j i := by
  ext k; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem mulVec_mem_of_columns {p q : ℕ} (G : Submodule ℂ (Fin p → ℂ))
    (M : Matrix (Fin p) (Fin q) ℂ) (h : ∀ i, (fun j => M j i) ∈ G) (z : Fin q → ℂ) :
    M *ᵥ z ∈ G := by
  have e : M *ᵥ z = ∑ i, z i • (fun j => M j i) := by
    ext k; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (h i))

theorem isUnit_gram (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P) :
    IsUnit (aᴴ * a + (1 - P)) := by
  have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPh]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hB : aᴴ * a + (1 - P) = (fromRows a (1 - P))ᴴ * fromRows a (1 - P) := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, hQ]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [hB, Matrix.conjTranspose_mul_self_mulVec_eq_zero, fromRows_mulVec] at hz
  have h1 : a *ᵥ v = 0 := by
    ext k; simpa using congrFun hz (Sum.inl k)
  have h2 : (1 - P) *ᵥ v = 0 := by
    ext k; simpa using congrFun hz (Sum.inr k)
  have h3 : P *ᵥ v = 0 := by
    rw [← hb, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  apply hv
  rw [Matrix.sub_mulVec, h3, Matrix.one_mulVec, sub_zero] at h2
  exact h2

theorem exists_gram_inverse (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P)
    (hap : a * P = a) :
    ∃ C H : Matrix (Fin m) (Fin m) ℂ, C * H = P ∧ aᴴ * a * C = P ∧ C * P = C := by
  have hu := isUnit_gram a b P hPh hPP hb
  set H := aᴴ * a + (1 - P) with hH
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hl : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ hdet
  have hr : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hPa : P * aᴴ = aᴴ := by
    have := congrArg conjTranspose hap
    rwa [conjTranspose_mul, hPh] at this
  have HP : H * P = aᴴ * a := by
    rw [hH, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, add_zero,
      Matrix.mul_assoc, hap]
  have PH : P * H = aᴴ * a := by
    rw [hH, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, add_zero,
      ← Matrix.mul_assoc, hPa]
  have comm : H⁻¹ * P = P * H⁻¹ := by
    calc H⁻¹ * P = H⁻¹ * (P * H) * H⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hr, Matrix.mul_one]
      _ = H⁻¹ * (H * P) * H⁻¹ := by rw [PH, HP]
      _ = P * H⁻¹ := by rw [← Matrix.mul_assoc, hl, Matrix.one_mul]
  refine ⟨H⁻¹ * P, H, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, PH, ← HP, ← Matrix.mul_assoc, hl, Matrix.one_mul]
  · calc aᴴ * a * (H⁻¹ * P) = H * (P * H⁻¹) * P := by
          rw [← HP]; simp only [Matrix.mul_assoc]
      _ = H * H⁻¹ * (P * P) := by rw [← comm]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hr, Matrix.one_mul, hPP]
  · rw [Matrix.mul_assoc, hPP]

theorem eichler_isometry (J : Matrix (Fin n) (Fin n) ℂ) (a d : Matrix (Fin n) (Fin m) ℂ)
    (F : Matrix (Fin m) (Fin m) ℂ) (hJh : Jᴴ = J) (h1 : aᴴ * J * a = 0) (h2 : aᴴ * J * d = 0)
    (hF : F + Fᴴ = dᴴ * J * d) :
    (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J))ᴴ * J *
      (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J)) = J := by
  have h3 : dᴴ * J * a = 0 := by
    have := congrArg conjTranspose h2
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have key : (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J))ᴴ * J =
      J - J * d * (aᴴ * J) - J * a * Fᴴ * (aᴴ * J) + J * a * (dᴴ * J) := by
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_neg,
      conjTranspose_one, conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [key]
  generalize hL : aᴴ * J = L at *
  generalize hD : dᴴ * J = D at *
  set N := 1 + a * (-D - F * L) + d * L with hN
  have hLN : L * N = L := by
    simp only [hN, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h1, h2, Matrix.zero_mul,
      add_zero]
  have hDN : D * N = D + (F + Fᴴ) * L := by
    rw [hF]
    simp only [hN, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h3, Matrix.zero_mul,
      add_zero]
  calc (J - J * d * L - J * a * Fᴴ * L + J * a * D) * N
      = J * N - J * d * (L * N) - J * a * Fᴴ * (L * N) + J * a * (D * N) := by
        simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    _ = J := by
        rw [hLN, hDN, hN]
        simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_neg, Matrix.mul_one,
          Matrix.mul_assoc]
        abel

theorem eichler_of_involution (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J)
    (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m))
    (hxx : xᴴ * J * x = 0) (hxy : xᴴ * J * y = 1) :
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * J ∈ Formalism.QuantumDeterminants.UH J ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)),
        J *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin m) (Fin m) ℂ,
      P = diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) := ⟨_, rfl⟩
  have hPh : Pᴴ = P := by
    rw [hPdef, diagonal_conjTranspose]
    congr 1
    ext i
    by_cases h : i ∈ A <;> simp [h]
  have hPP : P * P = P := by
    rw [hPdef, diagonal_mul_diagonal]
    congr 1
    ext i
    by_cases h : i ∈ A <;> simp [h]
  have colP : ∀ {r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) (v : Fin r) (i : Fin m),
      (M * P) v i = M v i * (if i ∈ A then (1 : ℂ) else 0) := by
    intro r M v i
    rw [hPdef, Matrix.mul_diagonal]
  have rowP : ∀ {r : ℕ} (M : Matrix (Fin m) (Fin r) ℂ) (i : Fin m) (v : Fin r),
      (P * M) i v = (if i ∈ A then (1 : ℂ) else 0) * M i v := by
    intro r M i v
    rw [hPdef, Matrix.diagonal_mul]
  obtain ⟨a, ha⟩ : ∃ a, a = x * P := ⟨_, rfl⟩
  have hap : a * P = a := by rw [ha, Matrix.mul_assoc, hPP]
  have haH : aᴴ = P * xᴴ := by rw [ha, conjTranspose_mul, hPh]
  have hPaH : P * aᴴ = aᴴ := by rw [haH, ← Matrix.mul_assoc, hPP]
  have haJa : aᴴ * J * a = 0 := by
    calc aᴴ * J * a = P * (xᴴ * J * x) * P := by rw [haH, ha]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hxx]; simp
  have haJy : aᴴ * J * y = P := by
    calc aᴴ * J * y = P * (xᴴ * J * y) := by rw [haH]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hxy, Matrix.mul_one]
  have hyJx : yᴴ * J * x = 1 := by
    have := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hb : (yᴴ * J) * a = P := by rw [ha, ← Matrix.mul_assoc, hyJx, Matrix.one_mul]
  obtain ⟨C, H, hCH, haaC, hCP⟩ := exists_gram_inverse a (yᴴ * J) P hPh hPP hb hap
  obtain ⟨y₂, hy₂⟩ : ∃ y₂, y₂ = J * a * C := ⟨_, rfl⟩
  have hJy₂ : J * y₂ = a * C := by
    rw [hy₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJa : J * a = y₂ * H := by
    rw [hy₂, Matrix.mul_assoc, hCH, Matrix.mul_assoc, hap]
  have hy₂P : y₂ * P = y₂ := by rw [hy₂, Matrix.mul_assoc, hCP]
  have hay₂ : aᴴ * J * y₂ = P := by
    rw [Matrix.mul_assoc, hJy₂, ← Matrix.mul_assoc, haaC]
  obtain ⟨d, hd⟩ : ∃ d, d = y₂ - y * P := ⟨_, rfl⟩
  have had : aᴴ * J * d = 0 := by
    rw [hd, Matrix.mul_sub, hay₂, ← Matrix.mul_assoc, haJy, hPP, sub_self]
  have hdP : d * P = d := by
    rw [hd, Matrix.sub_mul, hy₂P, Matrix.mul_assoc, hPP]
  have hPdH : P * dᴴ = dᴴ := by
    have := congrArg conjTranspose hdP
    rwa [conjTranspose_mul, hPh] at this
  obtain ⟨F, hFdef⟩ : ∃ F, F = (1 / 2 : ℂ) • (dᴴ * J * d) := ⟨_, rfl⟩
  have hEh : (dᴴ * J * d)ᴴ = dᴴ * J * d := by
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hF : F + Fᴴ = dᴴ * J * d := by
    rw [hFdef, conjTranspose_smul, hEh]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← add_smul]
    norm_num
  have hPF : P * F = F := by
    rw [hFdef, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPdH]
  obtain ⟨u, hu⟩ : ∃ u, u = -(dᴴ * J) - F * (aᴴ * J) := ⟨_, rfl⟩
  have hPu : P * u = u := by
    rw [hu, Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPdH, hPF]
  have hua : u * a = 0 := by
    have h3 : dᴴ * J * a = 0 := by
      have := congrArg conjTranspose had
      simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
    rw [hu, Matrix.sub_mul, Matrix.neg_mul, h3, Matrix.mul_assoc F, haJa]
    simp
  have hxu : x * u = a * u := by rw [ha, Matrix.mul_assoc, hPu]
  have hdx : d * xᴴ * J = d * (aᴴ * J) := by
    rw [haH, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hdP]
  have hN : 1 + x * u + d * xᴴ * J = 1 + a * u + d * (aᴴ * J) := by rw [hxu, hdx]
  have hiso := eichler_isometry J a d F hJh haJa had hF
  refine ⟨u, d, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v hi
    rw [← hPu, rowP]
    simp [hi]
  · intro v i hi
    rw [← hdP, colP]
    simp [hi]
  · intro i j hj
    have h0 : (u * a) i j = 0 := by rw [hua]; rfl
    rw [ha, ← Matrix.mul_assoc, colP] at h0
    simpa [hj] using h0
  · rw [hN, hu]
    exact hiso
  · rw [hN]
    obtain ⟨N, hNdef⟩ : ∃ N, N = 1 + a * u + d * (aᴴ * J) := ⟨_, rfl⟩
    rw [← hNdef]
    have hNa : N * a = a := by
      rw [hNdef, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc a, hua,
        Matrix.mul_assoc d, haJa]
      simp
    have hNy : N * (y * P) = y₂ + a * (u * (y * P)) := by
      have e : d * (aᴴ * J) * (y * P) = d := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (aᴴ * J), haJy, hPP, hdP]
      rw [hNdef, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc a, e, hd]
      abel
    have colx : ∀ i : A, (fun j => x j i) = fun j => a j i := by
      intro i
      ext j
      rw [ha, colP]
      simp [i.2]
    have coly : ∀ i : A, (fun j => y j i) = fun j => (y * P) j i := by
      intro i
      ext j
      rw [colP]
      simp [i.2]
    have hgx : ∀ i : A, (N *ᵥ fun j => x j i) = fun j => a j i := by
      intro i
      rw [colx, mulVec_column, hNa]
    have hgy : ∀ i : A, (N *ᵥ fun j => y j i) =
        (fun j => y₂ j i) + a *ᵥ (fun j => (u * (y * P)) j i) := by
      intro i
      rw [coly, mulVec_column, hNy, mulVec_column]
      ext j
      simp
    set G := Submodule.span ℂ (Set.range (fun i : A => N *ᵥ fun j => x j i) ∪
      Set.range (fun i : A => N *ᵥ fun j => y j i)) with hG
    have sub1 : ∀ i : A, (N *ᵥ fun j => x j i) ∈ G :=
      fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    have sub2 : ∀ i : A, (N *ᵥ fun j => y j i) ∈ G :=
      fun i => Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    have haG : ∀ z, a *ᵥ z ∈ G := by
      refine mulVec_mem_of_columns G a (fun i => ?_)
      by_cases h : i ∈ A
      · have := sub1 ⟨i, h⟩
        rwa [hgx] at this
      · have e : (fun j => a j i) = 0 := by
          ext j
          rw [← hap, colP]
          simp [h]
        rw [e]
        exact G.zero_mem
    have hyG : ∀ z, y₂ *ᵥ z ∈ G := by
      refine mulVec_mem_of_columns G y₂ (fun i => ?_)
      by_cases h : i ∈ A
      · have h1 := sub2 ⟨i, h⟩
        rw [hgy] at h1
        have h2 := G.sub_mem h1 (haG (fun j => (u * (y * P)) j i))
        rwa [add_sub_cancel_right] at h2
      · have e : (fun j => y₂ j i) = 0 := by
          ext j
          rw [← hy₂P, colP]
          simp [h]
        rw [e]
        exact G.zero_mem
    have J1 : ∀ z, J *ᵥ (a *ᵥ z) ∈ G := by
      intro z
      rw [Matrix.mulVec_mulVec, hJa, ← Matrix.mulVec_mulVec]
      exact hyG _
    have J2 : ∀ z, J *ᵥ (y₂ *ᵥ z) ∈ G := by
      intro z
      rw [Matrix.mulVec_mulVec, hJy₂, ← Matrix.mulVec_mulVec]
      exact haG _
    have hle : G ≤ G.comap (Matrix.mulVecLin J) := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · change J *ᵥ (N *ᵥ fun j => x j i) ∈ G
        have e : (fun j => a j i) = a *ᵥ (fun j => P j i) := by
          rw [mulVec_column, hap]
        rw [hgx, e]
        exact J1 _
      · change J *ᵥ (N *ᵥ fun j => y j i) ∈ G
        have e : (fun j => y₂ j i) = y₂ *ᵥ (fun j => P j i) := by
          rw [mulVec_column, hy₂P]
        rw [hgy, e, Matrix.mulVec_add]
        exact G.add_mem (J2 _) (J1 _)
    intro v hv
    exact hle hv

theorem eichler_transformation : ∀ {n m : ℕ} (ε : Fin n → Bool) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    xᴴ * Formalism.REAL.Jm ε * x = 0 → xᴴ * Formalism.REAL.Jm ε * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * Formalism.REAL.Jm ε ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)) :=
  fun ε x y A h1 h2 => eichler_of_involution (Formalism.REAL.Jm ε) (Formalism.REAL.Jm_mul_self ε)
    (Formalism.REAL.Jm_conjTranspose ε) x y A h1 h2

end GlobalTheory.CompanionTheory.EichlerTransf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_element_prescribed_blocks : ∀ {n m : ℕ} (ε : Fin n → Bool) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    xᴴ * Formalism.REAL.Jm ε * x = 0 → xᴴ * Formalism.REAL.Jm ε * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * Formalism.REAL.Jm ε ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)) := by
  first | exact @GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation | exact GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation | (intros; apply GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspace
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspace
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.JStable


open Module in
theorem exists_adapted_onb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (T : Set ι),
      W = Submodule.span ℂ (b '' T) := by
  classical
  let v : Set (EuclideanSpace ℂ ι) := Set.range (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι))
  have hon : Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι)) :=
    (stdOrthonormalBasis ℂ W).orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hv : Orthonormal ℂ ((↑) : v → EuclideanSpace ℂ ι) :=
    (orthonormal_subtype_range hon.linearIndependent.injective).2 hon
  obtain ⟨u, bu, hvu, hbu⟩ := hv.exists_orthonormalBasis_extension
  have hcard : Fintype.card u = Fintype.card ι :=
    (Module.finrank_eq_card_basis bu.toBasis).symm.trans finrank_euclideanSpace
  let e : u ≃ ι := Fintype.equivOfCardEq hcard
  refine ⟨bu.reindex e, e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}, ?_⟩
  have himg : (bu.reindex e) '' (e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}) = v := by
    rw [Set.image_image]
    ext y
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hbu, Set.mem_image,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hvu hy⟩, hy, rfl⟩
  rw [himg]
  have hr : W.subtype '' Set.range (stdOrthonormalBasis ℂ W) = v := (Set.range_comp _ _).symm
  rw [← hr, Submodule.span_image, ← (stdOrthonormalBasis ℂ W).coe_toBasis,
    (stdOrthonormalBasis ℂ W).toBasis.span_eq, Submodule.map_subtype_top]

variable {n : ℕ} (ε : Fin n → Bool)

def ext0 (s : Bool) : EuclideanSpace ℂ {i : Fin n // ε i = s} →ₗ[ℂ] (Fin n → ℂ) where
  toFun x a := if h : ε a = s then x ⟨a, h⟩ else 0
  map_add' x y := by
    funext a
    by_cases h : ε a = s <;> simp [h]
  map_smul' c x := by
    funext a
    by_cases h : ε a = s <;> simp [h]

def res0 (s : Bool) (v : Fin n → ℂ) : EuclideanSpace ℂ {i : Fin n // ε i = s} :=
  WithLp.toLp 2 fun i => v i

lemma extendByZero_apply_of_ne {s : Bool} (x : EuclideanSpace ℂ {i : Fin n // ε i = s}) {a : Fin n}
    (h : ε a ≠ s) : ext0 ε s x a = 0 := by
  simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]

lemma extendByZero_restrict_eigen_projection (s : Bool) (v : Fin n → ℂ) :
    ext0 ε s (res0 ε s v) =
      (1 / 2 : ℂ) • (v + (if s then (1 : ℂ) else -1) • (Formalism.REAL.Jm ε *ᵥ v)) := by
  funext a
  have hJ : (Formalism.REAL.Jm ε *ᵥ v) a = (if ε a then 1 else -1) * v a := by
    simp [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases s <;> cases h : ε a <;> simp <;> ring

lemma eq_extendByZero_restrict_sum (v : Fin n → ℂ) :
    v = ext0 ε true (res0 ε true v) + ext0 ε false (res0 ε false v) := by
  funext a
  simp only [Pi.add_apply, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases h : ε a <;> simp

lemma sum_extendByZero_fin_eq_sum_of_eq (s : Bool) (x y : EuclideanSpace ℂ {i : Fin n // ε i = s}) :
    ∑ a, star (ext0 ε s x a) * ext0 ε s y a = inner ℂ x y := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => ε a = s)
    (fun a => star (ext0 ε s x a) * ext0 ε s y a)]
  have h2 : ∑ a : {a // ¬ ε a = s}, star (ext0 ε s x a) * ext0 ε s y a = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [extendByZero_apply_of_ne ε x a.2, star_zero, zero_mul])
  rw [h2, add_zero, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hx : ∀ z : EuclideanSpace ℂ {i : Fin n // ε i = s}, ext0 ε s z i.1 = z i := by
    intro z
    simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2]
  rw [hx x, hx y]
  simp [mul_comm]

theorem exists_KG_coordinate (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) :
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin := by
  classical
  choose b T hT using fun s : Bool => exists_adapted_onb (W.comap (ext0 ε s))
  have hres : ∀ (s : Bool) (v : Fin n → ℂ), v ∈ W → res0 ε s v ∈ W.comap (ext0 ε s) := by
    intro s v hv
    rw [Submodule.mem_comap, extendByZero_restrict_eigen_projection]
    exact W.smul_mem _ (W.add_mem hv (W.smul_mem _ (hW v hv)))
  have hdecomp : W = (W.comap (ext0 ε true)).map (ext0 ε true) ⊔
      (W.comap (ext0 ε false)).map (ext0 ε false) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (Submodule.map_le_iff_le_comap.2 le_rfl)
      (Submodule.map_le_iff_le_comap.2 le_rfl))
    rw [eq_extendByZero_restrict_sum ε v]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (hres true v hv))
      (Submodule.mem_map_of_mem (hres false v hv))
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ,
      ∀ i j, M i j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i :=
    ⟨Matrix.of fun i j => ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i, fun _ _ => rfl⟩
  have hcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}) (a : Fin n),
      M a i'.1 = ext0 ε s (b s i') a := by
    rintro s ⟨j, rfl⟩ a
    exact hM a j
  have hMM : Mᴴ * M = 1 := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hjl : ε j = ε l
    · have h1 : ∀ a, M a j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) a := fun a => hcol (ε j) ⟨j, rfl⟩ a
      have h2 : ∀ a, M a l = ext0 ε (ε j) (b (ε j) ⟨l, hjl.symm⟩) a :=
        fun a => hcol (ε j) ⟨l, hjl.symm⟩ a
      simp only [h1, h2]
      rw [sum_extendByZero_fin_eq_sum_of_eq, orthonormal_iff_ite.1 (b (ε j)).orthonormal]
      simp only [Subtype.mk.injEq]
    · have hne : j ≠ l := fun h => hjl (h ▸ rfl)
      rw [if_neg hne]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hi : ε i = ε j
      · rw [hM i l, extendByZero_apply_of_ne ε _ (fun h => hjl (hi.symm.trans h)), mul_zero]
      · rw [hM i j, extendByZero_apply_of_ne ε _ hi, star_zero, zero_mul]
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hMM
  have hJ : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
    have hJd : Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl
    ext i j
    rw [hJd, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : ε i = ε j
    · simp only [hi]
      ring
    · rw [hM i j, extendByZero_apply_of_ne ε _ hi]
      ring
  have hunit : M ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hMM
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Mᴴ, hMM', hMM⟩
  have hUJ : u ∈ Formalism.REAL.UJ ε := by
    show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  let gu : Formalism.REAL.UJ ε := ⟨u, hUJ⟩
  have hK : M ∈ Formalism.REAL.Kset ε := ⟨hunit, hJ⟩
  let k : Formalism.REAL.KG ε := ⟨gu, (Formalism.REAL.mem_KG ε gu).2 hK⟩
  let S : Set (Fin n) := {j | (⟨j, rfl⟩ : {i : Fin n // ε i = ε j}) ∈ T (ε j)}
  refine ⟨k, S, ?_⟩
  change W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
    M.mulVecLin
  have hMcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}),
      M *ᵥ Pi.single i'.1 1 = ext0 ε s (b s i') := by
    intro s i'
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hcol s i' a]
  have hmemS : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s → i'.1 ∈ S := by
    rintro s ⟨j, rfl⟩ hi'
    exact hi'
  have hset : ⇑(ext0 ε true) '' (⇑(b true) '' T true) ∪ ⇑(ext0 ε false) '' (⇑(b false) '' T false) =
      Set.range (⇑M.mulVecLin ∘ fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ)) := by
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_range, Function.comp_apply,
      Matrix.mulVecLin_apply]
    constructor
    · rintro (⟨y, ⟨i', hi', rfl⟩, rfl⟩ | ⟨y, ⟨i', hi', rfl⟩, rfl⟩)
      · exact ⟨⟨i'.1, hmemS true i' hi'⟩, hMcol true i'⟩
      · exact ⟨⟨i'.1, hmemS false i' hi'⟩, hMcol false i'⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      have htr : ∀ (s : Bool) (h : ε j = s), (⟨j, h⟩ : {i : Fin n // ε i = s}) ∈ T s := by
        rintro s rfl
        exact hj
      have hback : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s →
          ∃ y, (∃ a ∈ T s, b s a = y) ∧ ext0 ε s y = M *ᵥ Pi.single i'.1 1 :=
        fun s i' hi' => ⟨b s i', ⟨i', hi', rfl⟩, (hMcol s i').symm⟩
      rcases Bool.eq_false_or_eq_true (ε j) with h | h
      · exact Or.inl (hback _ ⟨j, h⟩ (htr _ h))
      · exact Or.inr (hback _ ⟨j, h⟩ (htr _ h))
  conv_lhs => rw [hdecomp, hT true, hT false]
  rw [Submodule.map_span, Submodule.map_span, Submodule.map_span, ← Submodule.span_union, hset,
    Set.range_comp]

end GlobalTheory.CompanionTheory.JStable
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsOrthogonalHermitianSubspaceStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_stable_subspace_coordinate : ∀ {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), (∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) →
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map (Formalism.REAL.toMK k).mulVecLin := by
  first | exact @GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | exact GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate | (intros; apply GlobalTheory.CompanionTheory.JStable.exists_KG_coordinate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem eichler_frame : ∀ {n m : ℕ} (ε : Fin n → Bool) (G Q : Matrix (Fin n) (Fin n) ℂ) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    IsUnit Q → Qᴴ * Formalism.REAL.Jm ε * Q = G → xᴴ * G * x = 0 → xᴴ * G * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * G ∈ Formalism.QuantumDeterminants.UH G ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)) := by
  intro n m ε G Q x y A hQ hG hxx hxy
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have h2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have ex : ∀ z : Matrix (Fin n) (Fin m) ℂ, xᴴ * G * z = (Q * x)ᴴ * Formalism.REAL.Jm ε * (Q * z) := fun z => by
    rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨u, w, hu, hw, hux, hN, hJ⟩ := GlobalTheory.T.unitary_element_prescribed_blocks ε (Q * x) (Q * y) A (by rw [← ex, hxx]) (by rw [← ex, hxy])
  refine ⟨u * Q, Q⁻¹ * w, fun i v hi => ?_, fun v i hi => ?_, fun i j hj => ?_, ?_⟩
  · simp [Matrix.mul_apply, hu i _ hi]
  · simp [Matrix.mul_apply, hw _ i hi]
  · rw [Matrix.mul_assoc]; exact hux i j hj
  have key : Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) = (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q := by
    rw [← hG, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q⁻¹, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · show _ = _
    have e : (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)ᴴ * G * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) =
        (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G))ᴴ * Formalism.REAL.Jm ε * (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) := by
      rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, key, Matrix.conjTranspose_mul]
    have hN' : _ = _ := hN
    calc Qᴴ * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q)
        = Qᴴ * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)) * Q := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hN', ← hG, Matrix.mul_assoc]
  · have cx : ∀ z : Matrix (Fin n) (Fin m) ℂ, ∀ i : A, (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) *ᵥ (fun j => z j i) =
        (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => (Q * z) j i := fun z i => by
      rw [key, ← Matrix.mulVec_mulVec]
      congr 1
    simp only [cx]
    exact hJ

theorem iwasawa_adapted : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  intro D θ hθ V ε fr hfr m X Y hW T b
  classical
  have hQ := isFrameFam_mul_infMat_inv D θ hθ V ε fr hfr b
  let Q : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹
  let x : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => X.map (tauE D τ)
  let y : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => Y.map (tauE D τ)
  have hmap : ∀ τ (Z Z' : Matrix (Fin V.rank) (Fin m) D.host.E), (Z.map (tauE D τ))ᴴ * gramAt D V τ * Z'.map (tauE D τ) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z').map (tauE D τ) := by
    intro τ Z Z'
    have e : (Z.map (tauE D τ))ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (tauE D τ) := by
      ext i j
      simp [Formalism.UG.cT, GlobalTheory.Mem.Isom.tauE_sig]
    rw [e, gramAt, Matrix.map_mul, Matrix.map_mul]
  have hxx : ∀ τ, (x τ)ᴴ * gramAt D V τ * x τ = 0 := fun τ => by
    rw [hmap, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have hxy : ∀ τ, (x τ)ᴴ * gramAt D V τ * y τ = 1 := fun τ => by
    rw [hmap, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  choose u w hu hw hux hN hJ using fun τ =>
    eichler_frame (ε τ) (gramAt D V τ) (Q τ) (x τ) (y τ) (upTo T) (hQ τ).1 (hQ τ).2 (hxx τ) (hxy τ)
  obtain ⟨g, hg, U, W, hU, hW', hUX, hgM⟩ := GlobalTheory.T.archimedean_unitary_element_lift D θ hθ V X u w hN
  have hgu : g ∈ unip D.sp.cm.sig V.gram X T :=
    GlobalTheory.T.unitary_adelic_unipotent_lift D.sp.cm.sig V.gram X T g U W hW.xx (fun i v hi => hU i v fun τ => hu τ i v hi)
      (fun v i hi => hW' v i fun τ => hw τ v i hi) (fun i j hj => hUX i j fun τ => hux τ i j hj) hgM
  refine ⟨g, hgu, 1, one_mem _, g⁻¹ * b, by rw [mul_one, mul_inv_cancel_left], fun τ => ?_⟩
  have e1 : (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g := by
    rw [Formalism.L2.Fam.ThC.infMat_mul, Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have e2 : fr τ * (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * (1 + x τ * u τ + w τ * (x τ)ᴴ * gramAt D V τ) := by
    rw [e1, hg τ, ← Matrix.mul_assoc]
  obtain ⟨k, S, hk⟩ := GlobalTheory.T.involution_stable_subspace_coordinate (ε τ) _ (hJ τ)
  refine ⟨k, S, ?_⟩
  beta_reduce
  rw [e2]
  exact hk

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_decomposition_unipotent_levi : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted <;> assumption)
end
