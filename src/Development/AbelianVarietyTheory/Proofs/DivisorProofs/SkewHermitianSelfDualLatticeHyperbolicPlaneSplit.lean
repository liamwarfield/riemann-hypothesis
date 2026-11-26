module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewHermitianLatticeSplitsHyperbolicPlan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceLocalLatticeBasisHyperbolicPlane
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceLocalLatticeBasisHyperbolicPlane
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewBasis

open GlobalTheory.AdelicU GlobalTheory.PlaneBasis

theorem exists_decomp {E : Type} [Field E] {n₁ : ℕ} (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hind : ∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0)
    (z : Fin (n₁ + 2) → E) : ∃ (s t : E) (u : Fin n₁ → E), z = s • x + ι *ᵥ u + t • y := by
  let φ : (E × E) × (Fin n₁ → E) →ₗ[E] (Fin (n₁ + 2) → E) :=
    ((LinearMap.fst E E E).smulRight x).comp (LinearMap.fst E (E × E) (Fin n₁ → E)) +
      (Matrix.mulVecLin ι).comp (LinearMap.snd E (E × E) (Fin n₁ → E)) +
      ((LinearMap.snd E E E).smulRight y).comp (LinearMap.fst E (E × E) (Fin n₁ → E))
  have hφ : ∀ p, φ p = p.1.1 • x + ι *ᵥ p.2 + p.1.2 • y := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨s, t⟩, u⟩ h
    rw [hφ] at h
    obtain ⟨rfl, rfl, rfl⟩ := hind s t u h
    rfl
  have hdim : Module.finrank E ((E × E) × (Fin n₁ → E)) = Module.finrank E (Fin (n₁ + 2) → E) := by
    simp [Module.finrank_prod]; omega
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj z
  exact ⟨p.1.1, p.1.2, p.2, by rw [← hp, hφ]⟩

theorem exists_isSplitBasis_plane_of_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n₁ : ℕ) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E) (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ),
    i₀ < i₁ → i₁ < n₁ + 2 →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) →
    PrimAt (GlobalTheory.AdelicU.splitPrime τ) L x → PrimAt (GlobalTheory.AdelicU.splitPrime τ) L y → GlobalTheory.AdelicU.IsSplitBasis τ (lowLat ι L) β₁ →
    ∃ β : GL (Fin (n₁ + 2)) (Fv F v), GlobalTheory.AdelicU.IsSplitBasis τ L β ∧ ∀ i : Fin (n₁ + 2),
      (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧ (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j := by
  intro F E _ _ _ _ _ σ _ v τ n₁ L x y ι β₁ i₀ i₁ h01 h1n hdec hind hxP hyP hβ₁
  have hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1 := by
    simp only [valued_apply_eq_valuation]; exact hxP
  have hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1 := by
    simp only [valued_apply_eq_valuation]; exact hyP
  have hO : ∀ a : v.adicCompletion F, a ∈ v.adicCompletionIntegers F ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  set M := colMat τ x y ι β₁.1 i₀ i₁ with hM
  set P := Submodule.span (v.adicCompletionIntegers F) (Set.range fun i r => M r i) with hP
  set Q := LinearMap.range M.mulVecLin with hQ
  have hsmul : ∀ (c : E) (z : Fin (n₁ + 2) → E), (fun r => τ ((c • z) r)) = τ c • fun r => τ (z r) :=
    fun c z => funext fun r => by simp
  have hτmul : ∀ u : Fin n₁ → E, (fun r => τ ((ι *ᵥ u) r)) = ι.map τ *ᵥ fun r => τ (u r) :=
    fun u => funext fun r => by simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hc0 : (fun r => M r ⟨i₀, by omega⟩) = fun r => τ (x r) := funext fun r => by simp [hM, colMat]
  have hc1 : (fun r => M r ⟨i₁, h1n⟩) = fun r => τ (y r) := funext fun r => by
    simp [hM, colMat, h01.ne']
  have hcj : ∀ j : Fin n₁, (fun r => M r ⟨skip i₀ i₁ j, skip_lt j.2⟩) = fun r => (ι.map τ * β₁.1) r j :=
    fun j => funext fun r => by
      simp [hM, colMat, skip_ne_left h01, skip_ne_right h01, unskip_skip h01, j.2]
  have hPx : (fun r => τ (x r)) ∈ P := hc0 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPy : (fun r => τ (y r)) ∈ P := hc1 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPcol : ∀ j : Fin n₁, (fun r => (ι.map τ * β₁.1) r j) ∈ P := fun j =>
    hcj j ▸ Submodule.subset_span ⟨_, rfl⟩
  have hcolsum : ∀ w₁ : Fin n₁ → v.adicCompletion F,
      (ι.map τ * β₁.1) *ᵥ w₁ = ∑ j, w₁ j • (fun r => (ι.map τ * β₁.1) r j) := by
    intro w₁; funext r; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hPimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (∀ j, w₁ j ∈ v.adicCompletionIntegers F) →
      (ι.map τ * β₁.1) *ᵥ w₁ ∈ P := by
    intro w₁ hw
    rw [hcolsum]
    exact sum_mem fun j _ => smul_mem_int (hw j) (hPcol j)
  have hQcolv : ∀ i, (fun r => M r i) ∈ Q := fun i =>
    ⟨Pi.single i 1, funext fun r => by simp [Matrix.mulVec_single_one, Matrix.transpose_apply]⟩
  have hQx : (fun r => τ (x r)) ∈ Q := hc0 ▸ hQcolv _
  have hQy : (fun r => τ (y r)) ∈ Q := hc1 ▸ hQcolv _
  have hQimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (ι.map τ * β₁.1) *ᵥ w₁ ∈ Q := by
    intro w₁
    rw [hcolsum]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (hcj j ▸ hQcolv _)
  have hsplit : ∀ (s t : E) (u : Fin n₁ → E), (fun r => τ ((s • x + ι *ᵥ u + t • y) r)) = τ s • (fun r => τ (x r)) +
      (ι.map τ * β₁.1) *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) + τ t • fun r => τ (y r) := by
    intro s t u
    have e : (fun r => τ (u r)) = β₁.1 *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, ← e, ← hτmul, ← hsmul, ← hsmul]; funext r; simp
  have hSub : ∀ z ∈ L, (fun r => τ (z r)) ∈ P := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hdec z hz
    have hu' : u ∈ lowLat ι L := hu
    have h1 := (hβ₁ ((β₁⁻¹).1 *ᵥ fun r => τ (u r))).2 (by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact tau_mem_splitLat τ hu')
    rw [hsplit]
    exact add_mem (add_mem (smul_mem_int ((hO _).2 (hx.1 s hs)) hPx) (hPimg _ h1))
      (smul_mem_int ((hO _).2 (hy.1 t ht)) hPy)
  have hImg : ∀ u ∈ splitLat τ (lowLat ι L), ι.map τ *ᵥ u ∈ splitLat τ L := fun u hu =>
    splitLat_induction τ _ (p := fun u => ι.map τ *ᵥ u ∈ splitLat τ L)
      (fun a ha z hz => by
        rw [Matrix.mulVec_smul, ← hτmul]; exact smul_mem_int ha (tau_mem_splitLat τ hz))
      (by rw [Matrix.mulVec_zero]; exact zero_mem _)
      (fun u w hu hw => by rw [Matrix.mulVec_add]; exact add_mem hu hw)
      (fun u hu => by rw [Matrix.mulVec_neg]; exact neg_mem hu) hu
  have hunit : ∀ z : Fin (n₁ + 2) → E, ((∀ c : E, c • z ∈ L → Valued.v (τ c) ≤ 1) ∧
      ∃ c : E, c • z ∈ L ∧ Valued.v (τ c) = 1) → (fun r => τ (z r)) ∈ splitLat τ L := by
    rintro z ⟨-, c, hc, hv⟩
    have hne : τ c ≠ 0 := by intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have h2 := tau_mem_splitLat τ hc
    rw [hsmul] at h2
    have hinv : (τ c)⁻¹ ∈ v.adicCompletionIntegers F := (hO _).2 (by rw [map_inv₀, hv, inv_one])
    have := smul_mem_int hinv h2
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hColSL : ∀ i, (fun r => M r i) ∈ splitLat τ L := by
    intro i
    by_cases h0 : i.1 = i₀
    · convert hunit x hx using 1; funext r; simp [hM, colMat, h0]
    by_cases h1 : i.1 = i₁
    · convert hunit y hy using 1; funext r; simp only [hM, colMat, if_neg h0, if_pos h1]
    by_cases h2 : unskip i₀ i₁ i.1 < n₁
    · have : (fun r => M r i) = ι.map τ *ᵥ (β₁.1 *ᵥ Pi.single ⟨_, h2⟩ 1) := by
        funext r
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
        simp only [hM, colMat, if_neg h0, if_neg h1, dif_pos h2, Matrix.transpose_apply]
        rfl
      rw [this]
      refine hImg _ ((hβ₁ _).1 fun k => ?_)
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    · convert zero_mem (splitLat τ L) using 1; funext r; simp [hM, colMat, h0, h1, h2]
  have hPle : P ≤ splitLat τ L := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hColSL i)
  have hSLle : ∀ u ∈ splitLat τ L, u ∈ P := fun u hu =>
    splitLat_induction τ L (p := (· ∈ P)) (fun a ha z hz => smul_mem_int ha (hSub z hz)) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem) hu
  have hR : ∀ z : Fin (n₁ + 2) → E, (fun r => τ (z r)) ∈ Q := by
    intro z
    obtain ⟨s, t, u, rfl⟩ := exists_decomp x y ι hind z
    rw [hsplit]
    exact add_mem (add_mem (Submodule.smul_mem _ _ hQx) (hQimg _)) (Submodule.smul_mem _ _ hQy)
  have hsurj : Function.Surjective M.mulVec := by
    intro u
    have : u ∈ Q := by
      rw [← Finset.univ_sum_single u]
      refine sum_mem fun k _ => ?_
      have e : Pi.single k (u k) = u k • fun r => τ ((Pi.single k (1 : E) : Fin (n₁ + 2) → E) r) := by
        funext r
        by_cases h : r = k
        · subst h; simp
        · simp [h]
      rw [e]
      exact Submodule.smul_mem _ _ (hR _)
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  have hU : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  refine ⟨hU.unit, ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro u
    rw [IsUnit.unit_spec]
    constructor
    · intro hu; exact hPle (mem_colSpan.2 ⟨u, hu, rfl⟩)
    · intro hu
      obtain ⟨w, hw, e⟩ := mem_colSpan.1 (hSLle _ hu)
      have := Matrix.mulVec_injective_iff_isUnit.2 hU e
      rw [← this]; exact hw
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h]
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h, h01.ne']
  · intro j h r
    rw [IsUnit.unit_spec]
    have : i = ⟨skip i₀ i₁ j, skip_lt j.2⟩ := Fin.ext h
    subst this
    exact congrFun (hcj j) r

end GlobalTheory.PlaneSkewBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceLocalLatticeBasisHyperbolicPlaneStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n₁ : ℕ) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E) (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ),
    i₀ < i₁ → i₁ < n₁ + 2 →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) →
    PrimAt (GlobalTheory.AdelicU.splitPrime τ) L x → PrimAt (GlobalTheory.AdelicU.splitPrime τ) L y → GlobalTheory.AdelicU.IsSplitBasis τ (lowLat ι L) β₁ →
    ∃ β : GL (Fin (n₁ + 2)) (Fv F v), GlobalTheory.AdelicU.IsSplitBasis τ L β ∧ ∀ i : Fin (n₁ + 2),
      (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧ (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j := by
  first | exact @GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep | exact GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep | (intros; apply GlobalTheory.PlaneSkewBasis.exists_isSplitBasis_plane_of_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtension
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneCartan
open Matrix

theorem entry_eq {n : ℕ} {k l : Type} [Fintype k] [Fintype l] (A : Matrix (Fin n) k ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) l ℂ) (j : k) (m : l) :
    (Aᵀ * M * B) j m = (fun i => A i j) ⬝ᵥ M *ᵥ (fun i => B i m) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem form_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.conjTranspose = M) (x y : Fin n → ℂ) :
    x ⬝ᵥ M *ᵥ star y = star (y ⬝ᵥ M *ᵥ star x) := by
  have h : ∀ i j, M i j = star (M j i) := fun i j => by
    have := congrFun (congrFun hM i) j
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h j i]; ring

theorem star_mulVec' {n : ℕ} {k : Type} [Fintype k] (P : Matrix (Fin n) k ℂ) (b : k → ℂ) :
    star (P *ᵥ b) = P.map star *ᵥ star b := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]

theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum, mul_comm]

theorem dot_mulVec_left {n : ℕ} {k : Type} [Fintype k] (P : Matrix (Fin n) k ℂ) (a : k → ℂ) (v : Fin n → ℂ) :
    (P *ᵥ a) ⬝ᵥ v = a ⬝ᵥ (Pᵀ *ᵥ v) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]

theorem transport {n : ℕ} {k : Type} [Fintype k] [DecidableEq k] (M : Matrix (Fin n) (Fin n) ℂ)
    (P : Matrix (Fin n) k ℂ) (Q : Matrix k (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (G D : Matrix k k ℂ) (hG : Pᵀ * M * P.map star = G) (hD1 : D * D = 1) (hD2 : Dᵀ * G * D.map star = G)
    (hD3 : ∀ y : k → ℂ, y ≠ 0 → 0 < ((D *ᵥ y) ⬝ᵥ G *ᵥ star y).re) : IsCartan M (P * D * Q) := by
  have key : ∀ a b : k → ℂ, (P *ᵥ a) ⬝ᵥ M *ᵥ star (P *ᵥ b) = a ⬝ᵥ G *ᵥ star b := by
    intro a b
    rw [star_mulVec', dot_mulVec_left, ← hG, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · calc P * D * Q * (P * D * Q) = P * D * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P D D, hD1, Matrix.mul_one, hPQ]
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, map_star_mul, map_star_mul]
    calc Qᵀ * (Dᵀ * Pᵀ) * M * (P.map star * D.map star * Q.map star)
        = Qᵀ * (Dᵀ * (Pᵀ * M * P.map star) * D.map star) * Q.map star := by simp only [Matrix.mul_assoc]
      _ = Qᵀ * (Pᵀ * M * P.map star) * Q.map star := by rw [hG, hD2]
      _ = (P * Q)ᵀ * M * (P * Q).map star := by rw [Matrix.transpose_mul, map_star_mul]; simp only [Matrix.mul_assoc]
      _ = M := by rw [hPQ]; simp
  · intro x hx
    have hx' : x = P *ᵥ (Q *ᵥ x) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    have hy : Q *ᵥ x ≠ 0 := by
      intro h; apply hx; rw [hx', h, Matrix.mulVec_zero]
    have e1 : (P * D * Q) *ᵥ x = P *ᵥ (D *ᵥ (Q *ᵥ x)) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have e2 : (P *ᵥ (D *ᵥ (Q *ᵥ x))) ⬝ᵥ M *ᵥ star x = (D *ᵥ (Q *ᵥ x)) ⬝ᵥ G *ᵥ star (Q *ᵥ x) := by
      have := key (D *ᵥ (Q *ᵥ x)) (Q *ᵥ x)
      rwa [← hx'] at this
    rw [e1, e2]
    exact hD3 _ hy

end GlobalTheory.PlaneCartan

namespace GlobalTheory.PlaneCartan
open Matrix

def swapI : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def hypI : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; -Complex.I, 0]

theorem swapI_mul : swapI * swapI = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapI, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapI_iso : swapIᵀ * hypI * swapI.map star = hypI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapI, hypI, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapI_pos (y : Fin 2 → ℂ) : ((swapI *ᵥ y) ⬝ᵥ hypI *ᵥ star y) = (Complex.normSq (y 0) + Complex.normSq (y 1) : ℂ) := by
  simp [swapI, hypI, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_conj]
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  linear_combination (-(y 1 * (starRingEnd ℂ) (y 1) + y 0 * (starRingEnd ℂ) (y 0))) * Complex.I_mul_I

theorem blk_cartan {m : ℕ} (G₁ θ₁ : Matrix (Fin m) (Fin m) ℂ) (h : IsCartan G₁ θ₁) :
    (Matrix.fromBlocks θ₁ 0 0 swapI) * (Matrix.fromBlocks θ₁ 0 0 swapI) = 1 ∧
    (Matrix.fromBlocks θ₁ 0 0 swapI)ᵀ * Matrix.fromBlocks G₁ 0 0 hypI * (Matrix.fromBlocks θ₁ 0 0 swapI).map star =
      Matrix.fromBlocks G₁ 0 0 hypI ∧
    ∀ y : Fin m ⊕ Fin 2 → ℂ, y ≠ 0 →
      0 < (((Matrix.fromBlocks θ₁ 0 0 swapI) *ᵥ y) ⬝ᵥ Matrix.fromBlocks G₁ 0 0 hypI *ᵥ star y).re := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply, h1, swapI_mul]; simp
  · rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.map_zero _ (star_zero ℂ), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [h2, swapI_iso]
  · intro y hy
    have key : ((Matrix.fromBlocks θ₁ 0 0 swapI) *ᵥ y) ⬝ᵥ Matrix.fromBlocks G₁ 0 0 hypI *ᵥ star y =
        (θ₁ *ᵥ (y ∘ Sum.inl)) ⬝ᵥ G₁ *ᵥ star (y ∘ Sum.inl) + (swapI *ᵥ (y ∘ Sum.inr)) ⬝ᵥ hypI *ᵥ star (y ∘ Sum.inr) := by
      simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Function.comp_def, Pi.star_apply]
      rfl
    rw [key, Complex.add_re, swapI_pos]
    simp only [Function.comp_apply]
    have hn : ((Complex.normSq (y (Sum.inr 0)) + Complex.normSq (y (Sum.inr 1)) : ℂ)).re =
        Complex.normSq (y (Sum.inr 0)) + Complex.normSq (y (Sum.inr 1)) := by
      simp
    rw [hn]
    have n0 := Complex.normSq_nonneg (y (Sum.inr 0))
    have n1 := Complex.normSq_nonneg (y (Sum.inr 1))
    by_cases h0 : y ∘ Sum.inl = 0
    · have hc : y (Sum.inr 0) ≠ 0 ∨ y (Sum.inr 1) ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply hy; funext i; rcases i with i | i
        · exact congrFun h0 i
        · fin_cases i
          · exact hc.1
          · exact hc.2
      rw [h0]
      simp only [star_zero, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re, zero_add]
      rcases hc with h | h
      · have := Complex.normSq_pos.2 h; linarith
      · have := Complex.normSq_pos.2 h; linarith
    · have := h3 _ h0
      linarith

end GlobalTheory.PlaneCartan

namespace GlobalTheory.PlaneCartan
open Matrix

noncomputable def cols {n₁ : ℕ} (X Y : Fin (n₁ + 2) → ℂ) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) :
    Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) ℂ :=
  Matrix.fromCols ι (Matrix.of fun i k => (![X, Y] k) i)

theorem cols_mulVec {n₁ : ℕ} (X Y : Fin (n₁ + 2) → ℂ) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (w : Fin n₁ ⊕ Fin 2 → ℂ) :
    cols X Y ι *ᵥ w = ι *ᵥ (w ∘ Sum.inl) + w (Sum.inr 0) • X + w (Sum.inr 1) • Y := by
  ext i
  simp [cols, Matrix.fromCols_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  ring

theorem cols_gram {n₁ : ℕ} (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (hM : M.conjTranspose = M)
    (hXX : X ⬝ᵥ M *ᵥ star X = 0) (hYY : Y ⬝ᵥ M *ᵥ star Y = 0) (hXY : X ⬝ᵥ M *ᵥ star Y = Complex.I)
    (hι : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) :
    (cols X Y ι)ᵀ * M * (cols X Y ι).map star = Matrix.fromBlocks (ιᵀ * M * ι.map star) 0 0 hypI := by
  have c1 : ∀ a, (fun i => cols X Y ι i (Sum.inl a)) = ι *ᵥ Pi.single a 1 := fun a => by
    ext i; simp [cols, Matrix.mulVec_single_one]
  have c2 : (fun i => cols X Y ι i (Sum.inr 0)) = X := by ext i; simp [cols]
  have c3 : (fun i => cols X Y ι i (Sum.inr 1)) = Y := by ext i; simp [cols]
  have s1 : ∀ a, (fun i => (cols X Y ι).map star i (Sum.inl a)) = star (ι *ᵥ Pi.single a 1) := fun a => by
    ext i; simp [cols, Matrix.mulVec_single_one]
  have s2 : (fun i => (cols X Y ι).map star i (Sum.inr 0)) = star X := by ext i; simp [cols]
  have s3 : (fun i => (cols X Y ι).map star i (Sum.inr 1)) = star Y := by ext i; simp [cols]
  ext (a | a) (b | b)
  · rw [entry_eq, Matrix.fromBlocks_apply₁₁, entry_eq]; rfl
  · rw [entry_eq, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    fin_cases b
    · exact (c1 a ▸ s2 ▸ (hι _).1 : _)
    · exact (c1 a ▸ s3 ▸ (hι _).2 : _)
  · rw [entry_eq, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    fin_cases a
    · show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inl b)) = 0
      rw [c2, s1, form_symm hM, (hι _).1, star_zero]
    · show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inl b)) = 0
      rw [c3, s1, form_symm hM, (hι _).2, star_zero]
  · rw [entry_eq, Matrix.fromBlocks_apply₂₂]
    fin_cases a <;> fin_cases b
    · show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 0)) = hypI 0 0
      rw [c2, s2, hXX]; simp [hypI]
    · show (fun i => cols X Y ι i (Sum.inr 0)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 1)) = hypI 0 1
      rw [c2, s3, hXY]; simp [hypI]
    · show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 0)) = hypI 1 0
      rw [c3, s2, form_symm hM, hXY]; simp [hypI]
    · show (fun i => cols X Y ι i (Sum.inr 1)) ⬝ᵥ M *ᵥ (fun i => (cols X Y ι).map star i (Sum.inr 1)) = hypI 1 1
      rw [c3, s3, hYY]; simp [hypI]

end GlobalTheory.PlaneCartan

namespace GlobalTheory.PlaneCartan
open Matrix

theorem cols_ker {n₁ : ℕ} (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (hM : M.conjTranspose = M)
    (hXX : X ⬝ᵥ M *ᵥ star X = 0) (hYY : Y ⬝ᵥ M *ᵥ star Y = 0) (hXY : X ⬝ᵥ M *ᵥ star Y = Complex.I)
    (hι : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) (hinj : Function.Injective ι.mulVec)
    (w : Fin n₁ ⊕ Fin 2 → ℂ) (h : cols X Y ι *ᵥ w = 0) : w = 0 := by
  rw [cols_mulVec] at h
  have hYX : Y ⬝ᵥ M *ᵥ star X = -Complex.I := by rw [form_symm hM, hXY]; simp
  have hX := congrArg (· ⬝ᵥ M *ᵥ star X) h
  have hY := congrArg (· ⬝ᵥ M *ᵥ star Y) h
  simp only [add_dotProduct, smul_dotProduct, zero_dotProduct, (hι _).1, (hι _).2, hXX, hYY, hXY, hYX,
    smul_eq_mul] at hX hY
  have hb : w (Sum.inr 1) = 0 := by
    have : w (Sum.inr 1) * Complex.I = 0 := by linear_combination -hX
    simpa [Complex.I_ne_zero] using this
  have ha : w (Sum.inr 0) = 0 := by
    have : w (Sum.inr 0) * Complex.I = 0 := by linear_combination hY
    simpa [Complex.I_ne_zero] using this
  rw [ha, hb, zero_smul, zero_smul, add_zero, add_zero] at h
  have hu : w ∘ Sum.inl = 0 := hinj (by rw [h, Matrix.mulVec_zero])
  funext i
  rcases i with i | i
  · exact congrFun hu i
  · fin_cases i
    · exact ha
    · exact hb

theorem exists_cartan_hyperbolic_swap : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), M.conjTranspose = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y = Complex.I →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    IsCartan (ιᵀ * M * ι.map star) θ₁ →
    ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ ∃ c : ℂ, c ≠ 0 ∧ Y = c • θ *ᵥ X := by
  intro n₁ M X Y ι θ₁ hM hXX hYY hXY hι hinj hθ₁
  set P := cols X Y ι with hP
  let e : Fin n₁ ⊕ Fin 2 ≃ Fin (n₁ + 2) := finSumFinEquiv
  set P' : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := P.submatrix id e.symm with hP'
  have hPP' : P = P'.submatrix id e := by ext i j; simp [hP']
  have hinj' : Function.Injective P'.mulVec := by
    intro v v' hv
    have h0 : P' *ᵥ (v - v') = 0 := by rw [Matrix.mulVec_sub, hv, sub_self]
    rw [hP', Matrix.submatrix_mulVec_equiv, Equiv.symm_symm] at h0
    have h1 : P *ᵥ ((v - v') ∘ e) = 0 := by simpa using h0
    have h2 := cols_ker M X Y ι hM hXX hYY hXY hι hinj _ h1
    have h3 : v - v' = 0 := by
      funext i
      have := congrFun h2 (e.symm i)
      simpa using this
    exact sub_eq_zero.1 h3
  have hU : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det P').1 (Matrix.mulVec_injective_iff_isUnit.1 hinj')
  set Q : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) ℂ := (P'⁻¹).submatrix e id with hQ
  have hPQ : P * Q = 1 := by
    rw [hPP', hQ, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hU]
    simp
  have hQP : Q * P = 1 := by
    rw [hPP', hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ hU]
    exact Matrix.submatrix_one_equiv e
  set D : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) ℂ := Matrix.fromBlocks θ₁ 0 0 swapI with hD
  obtain ⟨hD1, hD2, hD3⟩ := blk_cartan _ _ hθ₁
  have hG := cols_gram M X Y ι hM hXX hYY hXY hι
  refine ⟨P * D * Q, transport M P Q hPQ hQP _ D hG hD1 hD2 hD3, ?_, -Complex.I, by simp, ?_⟩
  · set E : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁) ℂ :=
      Matrix.fromRows (1 : Matrix (Fin n₁) (Fin n₁) ℂ) (0 : Matrix (Fin 2) (Fin n₁) ℂ) with hEdef
    have hE : P * E = ι := by
      ext i j; simp [hP, hEdef, cols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    have hDE : D * E = E * θ₁ := by
      ext (i | i) j <;> simp [hD, hEdef, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    calc P * D * Q * ι = P * D * (Q * P) * E := by
          rw [← hE]; simp only [Matrix.mul_assoc]
      _ = P * (D * E) := by
          rw [hQP, Matrix.mul_one, Matrix.mul_assoc]
      _ = ι * θ₁ := by rw [hDE, ← Matrix.mul_assoc, hE]
  · have hz : ∀ k : Fin 2, (Pi.single (Sum.inr k) (1 : ℂ) : Fin n₁ ⊕ Fin 2 → ℂ) ∘ Sum.inl = 0 := fun k => by
      funext m; simp
    have hX : X = P *ᵥ Pi.single (Sum.inr 0) 1 := by
      rw [hP, cols_mulVec, hz, Matrix.mulVec_zero]; ext i; simp
    have hY : Y = P *ᵥ Pi.single (Sum.inr 1) 1 := by
      rw [hP, cols_mulVec, hz, Matrix.mulVec_zero]; ext i; simp
    have hDs : D *ᵥ Pi.single (Sum.inr 0) 1 = Complex.I • Pi.single (Sum.inr 1) 1 := by
      ext (i | i)
      · simp [hD, Matrix.fromBlocks_mulVec]
      · fin_cases i <;> simp [hD, Matrix.fromBlocks_mulVec, swapI, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have : (P * D * Q) *ᵥ X = Complex.I • Y := by
      rw [hX, Matrix.mulVec_mulVec, show P * D * Q * P = P * D * (Q * P) by simp only [Matrix.mul_assoc], hQP,
        Matrix.mul_one, ← Matrix.mulVec_mulVec, hDs, Matrix.mulVec_smul, ← hY]
    rw [this, smul_smul]
    simp

end GlobalTheory.PlaneCartan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtensionStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), M.conjTranspose = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y = Complex.I →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    IsCartan (ιᵀ * M * ι.map star) θ₁ →
    ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ ∃ c : ℂ, c ≠ 0 ∧ Y = c • θ *ᵥ X := by
  first | exact @GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | exact GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | (intros; apply GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealSmulMemLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealSmulMemLattice
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory

theorem exists_fractionalIdeal_smul_mem_lattice :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  let I : Submodule (𝓞 E) E := L.comap f
  have hI : ∀ s, s ∈ I ↔ s • x ∈ L := fun s => by simp [I, f]
  let π : (Fin n → E) →ₗ[𝓞 E] E := LinearMap.proj (R := 𝓞 E) (φ := fun _ => E) i
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (M := L)
  have hJ : IsFractional (𝓞 E)⁰ (L.map π) := FractionalIdeal.isFractional_of_fg (hfg.map π)
  let J : FractionalIdeal (𝓞 E)⁰ E := ⟨L.map π, hJ⟩
  have hle : I ≤ ((FractionalIdeal.spanSingleton (𝓞 E)⁰ (x i)⁻¹ * J :
      FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
    intro s hs
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]
    refine ⟨s * x i, ?_, ?_⟩
    · show s * x i ∈ L.map π
      exact ⟨s • x, (hI s).1 hs, by simp [π]⟩
    · field_simp
  exact ⟨⟨I, FractionalIdeal.isFractional_of_le hle⟩, fun s => hI s⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealSmulMemLatticeStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_mem_iff_smul_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  first | exact @GlobalTheory.exists_fractionalIdeal_smul_mem_lattice | exact GlobalTheory.exists_fractionalIdeal_smul_mem_lattice | (intros; apply GlobalTheory.exists_fractionalIdeal_smul_mem_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

section Helpers
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem form_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J (c • a) b = c * form σ J a b := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J a (c • b) = σ c * form σ J a b := by
  have : (fun i => σ ((c • b) i)) = σ c • fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    (fun i => τ (a i)) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (b i)) = Complex.I * τ (form σ J a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.map_apply, Pi.star_apply, smul_eq_mul,
    map_sum, map_mul, hτ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, mul_assoc, mul_left_comm]

end Helpers

end GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

section Helpers2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}

theorem gram_skew (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (ι : Matrix (Fin n) (Fin n₁) E) (i j : Fin n₁) :
    σ ((ιᵀ * J * ι.map σ) j i) = -(ιᵀ * J * ι.map σ) i j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, sigma_sigma h, hJ,
    Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) :
    (ι.map τ)ᵀ * (Complex.I • J.map τ) * (ι.map τ).map star = Complex.I • (ιᵀ * J * ι.map σ).map τ := by
  have e : (ι.map σ).map τ = (ι.map τ).map star := Matrix.ext fun i j => by simp [hτ]
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]

theorem herm_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) : (Complex.I • J.map τ).conjTranspose = Complex.I • J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← hτ, hJ,
    map_neg, Complex.star_def, Complex.conj_I]
  ring

theorem orth_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (a : Fin n → E) (h : ∀ u, form σ J (ι *ᵥ u) a = 0) (u : Fin n₁ → ℂ) :
    (ι.map τ *ᵥ u) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (a i)) = 0 := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  have hz : ((Complex.I • J.map τ) *ᵥ star (fun i => τ (a i))) ᵥ* ι.map τ = 0 := by
    funext j
    have e := form_map τ hτ J (ι *ᵥ Pi.single j 1) a
    rw [h, map_zero, mul_zero, Matrix.mulVec_single_one] at e
    rw [Pi.zero_apply, ← e, dotProduct_comm]
    simp [Matrix.vecMul, dotProduct, Matrix.col, mul_comm]
  rw [hz, zero_dotProduct]

theorem inj_map (τ : E →+* ℂ) (ι : Matrix (Fin n) (Fin n₁) E) (h : Function.Injective ι.mulVec) :
    Function.Injective (ι.map τ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin ι)
    (LinearMap.ker_eq_bot.2 h)
  set K := LinearMap.toMatrix' g
  have hK : K * ι = 1 := by
    rw [← LinearMap.toMatrix'_toLin' ι, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
      LinearMap.toMatrix'_id]
  intro u u' e
  have := congrArg (fun z => (K.map τ) *ᵥ z) e
  simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hK, Matrix.map_one _ (map_zero τ) (map_one τ),
    Matrix.one_mulVec] at this
  exact this

end Helpers2
end GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

theorem plane_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsSkew σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsSkew σ B r s ∧ Y₁.IsSkew σ B (r - 1) (s - 1) ∧
        H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  classical
  subst hn
  have hCM : IsCMExt F E σ := hB.cm
  have hτσ : ∀ (τ : E →+* ℂ) (a : E), τ (σ a) = star (τ a) := hCM.2.2.2
  obtain ⟨θ, hθ⟩ := GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨x₀, hx₀, hxx₀⟩ := GlobalTheory.T.exists_isotropic_indefinite_skewHermitian_cm F E σ B hCM (n₁ + 2) Y.J r s hY.skew hY.sig hr hs (by omega)
  obtain ⟨y₀, ι, hxy₀, hyy₀, horth₀, hind₀, hsplit₀⟩ :=
    GlobalTheory.T.selfDualSkewHermitianLattice_splits_hyperbolicPlane F E σ hCM θ hθ n₁ Y.J Y.L hY.skew hY.lat.toIsLattice hY.dual x₀ hx₀ hxx₀
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    rw [show (0 : Fin (n₁ + 2) → E) = (0 : E) • x₀ by simp, form_smul_right, map_zero, zero_mul] at hxy₀
    exact zero_ne_one hxy₀
  obtain ⟨c, hc, hprim⟩ := GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes F E σ hCM (n₁ + 2) Y.L hY.lat x₀ y₀ hx₀ hy₀ B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc (by simpa [sigma_sigma hCM] using congrArg σ h)
  set x := c • x₀ with hxdef
  set y := (σ c)⁻¹ • y₀ with hydef
  have hxx : form σ Y.J x x = 0 := by rw [form_smul_left, form_smul_right, hxx₀, mul_zero, mul_zero]
  have hyy : form σ Y.J y y = 0 := by rw [form_smul_left, form_smul_right, hyy₀, mul_zero, mul_zero]
  have hxy : form σ Y.J x y = 1 := by
    rw [form_smul_left, form_smul_right, hxy₀, map_inv₀, sigma_sigma hCM, mul_one, mul_inv_cancel₀ hc]
  have horth : ∀ u, form σ Y.J (ι *ᵥ u) x = 0 ∧ form σ Y.J (ι *ᵥ u) y = 0 := fun u => by
    rw [form_smul_right, form_smul_right, (horth₀ u).1, (horth₀ u).2, mul_zero, mul_zero]; exact ⟨rfl, rfl⟩
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ ι *ᵥ u ∈ Y.L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s', t, u, h1, h2, h3, rfl⟩ := hsplit₀ z hz
    have e1 : (s' / c) • x = s' • x₀ := by rw [hxdef, smul_smul, div_mul_cancel₀ _ hc]
    have e2 : (t * σ c) • y = t • y₀ := by rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
    exact ⟨s' / c, t * σ c, u, e1 ▸ h1, e2 ▸ h2, h3, by rw [e1, e2]⟩
  have hind : ∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0 := by
    intro s' t u h
    rw [hxdef, hydef, smul_smul, smul_smul] at h
    obtain ⟨h1, h2, h3⟩ := hind₀ _ _ _ h
    exact ⟨(mul_eq_zero.1 h1).resolve_right hc, (mul_eq_zero.1 h2).resolve_right (inv_ne_zero hσc), h3⟩
  have hinjι : Function.Injective ι.mulVec := fun u u' h => by
    have := hind₀ 0 0 (u - u') (by simp [Matrix.mulVec_sub, h])
    exact sub_eq_zero.1 this.2.2
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_mem_iff_smul_mem_lattice E (n₁ + 2) Y.L hY.lat.toIsLattice x (smul_ne_zero hc hx₀)
  haveI hlat1 : (lowLat ι Y.L).IsLattice E := GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding E (n₁ + 2) n₁ Y.L ι hY.lat.toIsLattice hinjι

  haveI hfull : (lowLat ι Y.L).IsFullLattice E := by
    refine ⟨?_⟩
    apply eq_top_iff.mpr
    intro u _
    have hspan : ι *ᵥ u ∈ Submodule.span E (Y.L : Set (Fin (n₁ + 2) → E)) := by
      rw [hY.lat.span_eq_top]
      trivial
    obtain ⟨d, hd, hdu⟩ := exists_ne_zero_smul_mem_of_mem_span Y.L (ι *ᵥ u) hspan
    have hd' : algebraMap (𝓞 E) E d ≠ 0 := fun h => hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h))
    have hmem : d • u ∈ lowLat ι Y.L := by
      change ι *ᵥ (d • u) ∈ Y.L
      rw [← algebraMap_smul E, Matrix.mulVec_smul, algebraMap_smul]
      exact hdu
    have hmem' := Submodule.subset_span (R := E) hmem
    rw [← algebraMap_smul E] at hmem'
    exact (Submodule.smul_mem_iff _ hd').1 hmem'

  have hXX : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 := fun w => by rw [form_map _ (hτσ _), hxx, map_zero, mul_zero]
  have hYY : ∀ w, (fun i => (B.emb w).1 (y i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w => by rw [form_map _ (hτσ _), hyy, map_zero, mul_zero]
  have hXY : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = Complex.I := fun w => by rw [form_map _ (hτσ _), hxy, map_one, mul_one]
  have hO : ∀ w (u : Fin n₁ → ℂ), (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 ∧ (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w u =>
    ⟨orth_map _ (hτσ _) Y.J ι x (fun u => (horth u).1) u, orth_map _ (hτσ _) Y.J ι y (fun u => (horth u).2) u⟩
  have hsig1 : ∀ w, HasSig (Complex.I • (ιᵀ * Y.J * ι.map σ).map (B.emb w).1) (r - 1) (s - 1) := fun w => by
    rw [← gram_map _ (hτσ _)]
    exact GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement n₁ _ _ _ _ r s (hY.sig w) hr hs (hXX w) (hYY w) (by rw [hXY w]; exact Complex.I_ne_zero) (hO w)
      (inj_map _ ι hinjι)
  choose θ₁ hθ₁ using fun w => GlobalTheory.T.exists_cartanInvolution_hermitianSignature n₁ _ (r - 1) (s - 1) (hsig1 w)
  choose θW hθW using fun w => GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension n₁ (Complex.I • Y.J.map (B.emb w).1) _ _ (ι.map (B.emb w).1) (θ₁ w)
    (herm_map _ (hτσ _) hY.skew) (hXX w) (hYY w) (hXY w) (hO w) (inj_map _ ι hinjι)
    (by rw [gram_map _ (hτσ _)]; exact hθ₁ w)

  choose β₁ hβ₁ using fun v : B.P => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (lowLat ι Y.L) hCM
  choose βY hβY using fun v : B.P => GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane F E σ hCM v.1 (B.τ v) n₁ Y.L x y ι (β₁ v) i₀ i₁ h01 h1n hsplit hind
    (hprim v).1 (hprim v).2 (hβ₁ v)
  let Y₁ : Spc F E n₁ :=
    { J := ιᵀ * Y.J * ι.map σ
      L := lowLat ι Y.L
      θ := θ₁
      bas := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1 }
  let Y' : Spc F E (n₁ + 2) :=
    { J := Y.J
      L := Y.L
      θ := θW
      bas := fun v => if h : v ∈ B.P then βY ⟨v, h⟩ else 1 }
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact
      { skew := hY.skew
        sig := hY.sig
        lat := hY.lat
        dual := hY.dual
        cartan := fun w => (hθW w).1
        bas := fun v => by
          show IsSplitBasis (B.τ v) Y.L (if h : v.1 ∈ B.P then βY ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact (hβY v).1 }
  · exact
      { skew := gram_skew hCM hY.skew ι
        sig := hsig1
        lat := hfull
        dual := GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual F E σ n₁ Y.J Y.L x y ι hY.dual horth hsplit
        cartan := hθ₁
        bas := fun v => by
          show IsSplitBasis (B.τ v) (lowLat ι Y.L) (if h : v.1 ∈ B.P then β₁ ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact hβ₁ v }
  · exact
      { rank := rfl
        xx := hxx
        yy := hyy
        xy := hxy
        orth := horth
        gram := rfl
        low := fun u => Iff.rfl
        split := hsplit
        ideal := h𝔟
        cartan := fun w => ⟨(hθW w).2.1, (hθW w).2.2⟩
        bas := fun v i => by
          have e1 : (GlobalTheory.ThK.reS Y Y').bas v = βY v := dif_pos v.2
          have e2 : Y₁.bas v = β₁ v := dif_pos v.2
          rw [e1, e2]
          exact (hβY v).2 i }

end GlobalTheory.PlaneSkew
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplitStatement
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_selfDual_lattice_hyperbolic_plane_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsSkew σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsSkew σ B r s ∧ Y₁.IsSkew σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  first | exact @GlobalTheory.PlaneSkew.plane_skew | exact GlobalTheory.PlaneSkew.plane_skew | (intros; apply GlobalTheory.PlaneSkew.plane_skew <;> assumption)
end
