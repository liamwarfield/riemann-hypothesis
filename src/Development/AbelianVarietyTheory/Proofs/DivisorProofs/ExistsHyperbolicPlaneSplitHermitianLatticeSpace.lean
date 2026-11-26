module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPairSelfDualLatticeIsotropic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalComplementEmbeddingHyperbolicPai
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalComplementEmbeddingHyperbolicPai
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem exists_orthCompl_hypPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  intro F E _ _ _ _ _ σ n n₁ J x y hn hJ hxx hyy hxy
  classical
  set a : Fin n → E := J *ᵥ fun i => σ (x i) with ha_def
  set b : Fin n → E := J *ᵥ fun i => σ (y i) with hb_def
  have hfa : ∀ z, form σ J z x = z ⬝ᵥ a := fun z => rfl
  have hfb : ∀ z, form σ J z y = z ⬝ᵥ b := fun z => rfl
  have hxa : x ⬝ᵥ a = 0 := hxx
  have hxb : x ⬝ᵥ b = 1 := hxy
  have ha : a ≠ 0 := by
    intro h0
    have hv : x ᵥ* J = 0 := by
      funext j
      apply σ.toRingHom.injective
      have h1 := congrFun h0 j
      simp only [ha_def, Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hJ j i, mul_comm]
    apply one_ne_zero (α := E)
    rw [← hxb, hb_def, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  set w : Fin n → E := (a i)⁻¹ • (Pi.single i 1 - (b i) • x) with hw
  have hwa : w ⬝ᵥ a = 1 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxa, single_dotProduct]
    simp [hi]
  have hwb : w ⬝ᵥ b = 0 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxb, single_dotProduct]
    simp
  let M : Matrix (Fin 2) (Fin n) E := Matrix.of ![a, b]
  have hM : ∀ z, M *ᵥ z = ![z ⬝ᵥ a, z ⬝ᵥ b] := by
    intro z; funext k; fin_cases k <;> simp [M, Matrix.mulVec, dotProduct_comm]
  have hsurj : LinearMap.range (Matrix.mulVecLin M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨v 0 • w + v 1 • x, ?_⟩
    rw [Matrix.mulVecLin_apply, hM]
    funext k; fin_cases k <;> simp [add_dotProduct, smul_dotProduct, hwa, hwb, hxa, hxb]
  have hrank : Module.finrank E (LinearMap.ker (Matrix.mulVecLin M)) = n₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  set K := LinearMap.ker (Matrix.mulVecLin M) with hK
  have hmemK : ∀ z, z ∈ K ↔ z ⬝ᵥ a = 0 ∧ z ⬝ᵥ b = 0 := by
    intro z
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]
    constructor
    · intro h; exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
    · rintro ⟨h1, h2⟩; funext k; fin_cases k <;> simp [h1, h2]
  let bK : Module.Basis (Fin n₁) E K := Module.finBasisOfFinrankEq E K hrank
  let f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ bK.equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp bK.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  refine ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · intro u
    rw [LinearMap.toMatrix'_mulVec, hfa, hfb]
    exact (hmemK _).1 (bK.equivFun.symm u).2
  · intro z h1 h2
    have hz : z ∈ K := (hmemK z).2 ⟨h1, h2⟩
    refine ⟨bK.equivFun ⟨z, hz⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    simp [f]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalComplementEmbeddingHyperbolicPaiStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  first | exact @GlobalTheory.exists_orthCompl_hypPair | exact GlobalTheory.exists_orthCompl_hypPair | (intros; apply GlobalTheory.exists_orthCompl_hypPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealLatticeLineCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealLatticeLineCoefficients
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem latticeLine_fractionalIdeal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  have hf : Function.Injective f := by
    intro a b h
    have h' : a • x = b • x := h
    exact smul_left_injective E hx h'
  have hLfg : L.FG := hL.fg
  have hmapfg : ((L.comap f).map f).FG :=
    Submodule.FG.of_le hLfg (Submodule.map_comap_le f L)
  have hS : (L.comap f).FG := Submodule.fg_of_fg_map_injective f hf hmapfg
  exact ⟨⟨L.comap f, FractionalIdeal.isFractional_of_fg hS⟩, fun s => Iff.rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionalIdealLatticeLineCoefficientsStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_lattice_line_coefficients : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  first | exact @GlobalTheory.latticeLine_fractionalIdeal | exact GlobalTheory.latticeLine_fractionalIdeal | (intros; apply GlobalTheory.latticeLine_fractionalIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionExtendSwappingHyperbolicPa
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionExtendSwappingHyperbolicPa
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanPlane

open Matrix

theorem star_mulVec_map {m k : Type} [Fintype k] (B : Matrix m k ℂ) (v : k → ℂ) :
    star (B *ᵥ v) = B.map star *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, star_sum]

theorem form_mulVec {m k l : Type} [Fintype m] [Fintype k] [Fintype l] (A : Matrix m k ℂ) (B : Matrix m l ℂ)
    (M : Matrix m m ℂ) (u : k → ℂ) (v : l → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (B *ᵥ v) = u ⬝ᵥ (Aᵀ * M * B.map star) *ᵥ star v := by
  rw [star_mulVec_map, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ u),
    dotProduct_mulVec, dotProduct_comm]

theorem herm_swap {m : Type} [Fintype m] (M : Matrix m m ℂ) (hM : Mᴴ = M) (x y : m → ℂ) :
    y ⬝ᵥ M *ᵥ star x = star (x ⬝ᵥ M *ᵥ star y) := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by rw [← conjTranspose_apply, hM]
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_form {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, x ⬝ᵥ A *ᵥ star y = x ⬝ᵥ B *ᵥ star y) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

end GlobalTheory.CartanPlane

namespace GlobalTheory.CartanPlane
open Matrix

theorem extend_swap : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  intro n n₁ M X Yv ι P θ₁ hn hM hXX hYY hXY hιX hιY hPι hθ₁
  subst hn
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hYX : Yv ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap M hM, hXY]; simp
  have hιuX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιX, zero_dotProduct]
  have hιuY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Yv = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιY, zero_dotProduct]
  have hXιu : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuX, star_zero]
  have hYιu : ∀ u, Yv ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuY, star_zero]
  have hιι : ∀ u u', (ι *ᵥ u) ⬝ᵥ M *ᵥ star (ι *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => form_mulVec ι ι M u u'
  have hexp : ∀ u (a b : ℂ) u' (a' b' : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star (ι *ᵥ u' + a' • X + b' • Yv) =
      u ⬝ᵥ M₁ *ᵥ star u' + a * star b' + b * star a' := by
    intro u a b u' a' b'
    simp only [add_dotProduct, star_add, mulVec_add, dotProduct_add, smul_dotProduct, star_smul, mulVec_smul,
      dotProduct_smul, hιι, hιuX, hιuY, hXιu, hYιu, hXX, hYY, hXY, hYX, smul_eq_mul]
    ring
  have hcY : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star Yv = a := by
    intro u a b; have := hexp u a b 0 0 1; simpa using this
  have hcX : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star X = b := by
    intro u a b; have := hexp u a b 0 1 0; simpa using this

  have hdec : ∀ z : Fin (n₁ + 2) → ℂ, ∃ (u : Fin n₁ → ℂ) (a b : ℂ), z = ι *ᵥ u + a • X + b • Yv := by
    let Φ : ((Fin n₁ → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin (n₁ + 2) → ℂ) :=
      (Matrix.toLin' ι).comp (LinearMap.fst ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight X).comp (LinearMap.snd ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight Yv).comp (LinearMap.snd ℂ _ _)
    have hΦ : ∀ p, Φ p = ι *ᵥ p.1 + p.2 0 • X + p.2 1 • Yv := fun p => by simp [Φ]
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨u, w⟩ h0
      rw [hΦ] at h0
      have ha := hcY u (w 0) (w 1)
      have hb := hcX u (w 0) (w 1)
      simp only at h0 ha hb
      rw [h0, zero_dotProduct] at ha hb
      have hu : ι *ᵥ u = 0 := by rw [← ha, ← hb] at h0; simpa using h0
      have : u = 0 := by rw [← one_mulVec u, ← hPι, ← mulVec_mulVec, hu, mulVec_zero]
      refine Prod.ext this ?_
      ext i; fin_cases i <;> simp [← ha, ← hb]
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod])).mp hinj
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨p.1, p.2 0, p.2 1, by rw [← hp, hΦ]⟩

  set vX := M *ᵥ star X with hvX
  set vY := M *ᵥ star Yv with hvY
  set C₁ : Matrix (Fin n₁) (Fin (n₁ + 2)) ℂ := P - vecMulVec (P *ᵥ X) vY - vecMulVec (P *ᵥ Yv) vX with hC₁
  set θ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := ι * θ₁ * C₁ + vecMulVec Yv vY + vecMulVec X vX with hθdef
  have hθ : ∀ u (a b : ℂ), θ *ᵥ (ι *ᵥ u + a • X + b • Yv) = ι *ᵥ (θ₁ *ᵥ u) + b • X + a • Yv := by
    intro u a b
    have ha : vY ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = a := by rw [dotProduct_comm]; exact hcY u a b
    have hb : vX ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = b := by rw [dotProduct_comm]; exact hcX u a b
    have hC : C₁ *ᵥ (ι *ᵥ u + a • X + b • Yv) = u := by
      rw [hC₁, sub_mulVec, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, mulVec_add, mulVec_add,
        mulVec_smul, mulVec_smul, mulVec_mulVec, hPι, one_mulVec]
      simp only [op_smul_eq_smul]
      abel
    rw [hθdef, add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, ← mulVec_mulVec, ← mulVec_mulVec, hC]
    simp only [op_smul_eq_smul]
    abel
  have hext : ∀ A B : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ,
      (∀ u (a b : ℂ), A *ᵥ (ι *ᵥ u + a • X + b • Yv) = B *ᵥ (ι *ᵥ u + a • X + b • Yv)) → A = B := by
    intro A B h
    apply ext_of_mulVec_single
    intro i
    obtain ⟨u, a, b, hz⟩ := hdec (Pi.single i 1)
    rw [hz, h]
  have hθ₁θ₁ : ∀ u, θ₁ *ᵥ (θ₁ *ᵥ u) = u := fun u => by rw [mulVec_mulVec, hθ₁.1, one_mulVec]
  have hiso₁ : ∀ u u', (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star (θ₁ *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => by
    rw [form_mulVec, hθ₁.2.1]
  have hre : ∀ c : ℂ, (c * star c).re = Complex.normSq c := fun c => by
    simp [Complex.mul_re, Complex.normSq_apply]
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply hext
    intro u a b
    rw [← mulVec_mulVec, hθ, hθ, hθ₁θ₁, one_mulVec]
  · apply ext_form
    intro x y
    rw [← form_mulVec]
    obtain ⟨u, a, b, rfl⟩ := hdec x
    obtain ⟨u', a', b', rfl⟩ := hdec y
    rw [hθ, hθ, hexp, hexp, hiso₁]
    ring
  · intro x hx
    obtain ⟨u, a, b, rfl⟩ := hdec x
    rw [hθ, hexp, Complex.add_re, Complex.add_re, hre, hre]
    by_cases hu : u = 0
    · subst hu
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        simp [h.1, h.2]
      simp only [mulVec_zero, zero_dotProduct, Complex.zero_re, zero_add]
      rcases hab with h | h
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg b; linarith
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg a; linarith
    · have := hθ₁.2.2 u hu
      have := Complex.normSq_nonneg b; have := Complex.normSq_nonneg a; linarith
  · apply ext_of_mulVec_single
    intro j
    have := hθ (Pi.single j 1) 0 0
    simp only [zero_smul, add_zero] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, this]
  · have := hθ 0 1 0
    simpa using this

end GlobalTheory.CartanPlane
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionExtendSwappingHyperbolicPaStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  first | exact @GlobalTheory.CartanPlane.extend_swap | exact GlobalTheory.CartanPlane.extend_swap | (intros; apply GlobalTheory.CartanPlane.extend_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeComapMulVecLinOfLeftInverseMatrixStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 → L.IsLattice E →
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E := by
  intro E _ _ n n₁ L ι P hPι hL
  set f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E) with hf
  set g : (Fin n → E) →ₗ[𝓞 E] (Fin n₁ → E) := (Matrix.mulVecLin P).restrictScalars (𝓞 E) with hg
  have hgf : ∀ u, g (f u) = u := by
    intro u
    simp [hf, hg, Matrix.mulVec_mulVec, hPι]
  apply Submodule.IsLattice.of_fg E
  have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.fg
  have h1 : ((L.comap f).map f).FG :=
    isNoetherian_submodule.1 hN _ (Submodule.map_comap_le f L)
  have h2 : ((L.comap f).map f).map g = L.comap f := by
    rw [← Submodule.map_comp]
    ext u
    simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply, hgf]
    exact ⟨fun ⟨v, hv, he⟩ => he ▸ hv, fun hu => ⟨u, hu, rfl⟩⟩
  rw [← h2]
  exact h1.map g
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KTowerPlane

section Help
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (a b : Fin n → E) : form σ J b a = σ (form σ J a b) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => hJ j i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by simp [form, add_dotProduct]

theorem form_sub_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a - b) c = form σ J a c - form σ J b c := by simp [form, sub_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J (s • a) c = s * form σ J a c := by simp [form, smul_dotProduct]

theorem form_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a + b) = form σ J c a + form σ J c b := by
  have : (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J c (s • a) = σ s * form σ J c a := by
  have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_gram {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (u u' : Fin n₁ → E) :
    form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  have e1 : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) ι u' i
  simp only [form, e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem map_form (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    e (form σ J a b) = (fun i => e (a i)) ⬝ᵥ J.map e *ᵥ star (fun i => e (b i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, h.2.2.2 e]

theorem transpose_mulVec_eq_zero {n n₁ : ℕ} {R : Type} [CommRing R] (ι : Matrix (Fin n) (Fin n₁) R) (w : Fin n → R)
    (hw : ∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) : ιᵀ *ᵥ w = 0 := by
  funext k
  have := hw (Pi.single k 1)
  rwa [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this

theorem map_herm (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) : (J.map e)ᴴ = J.map e := by
  ext i j
  simp [Matrix.conjTranspose_apply, ← h.2.2.2 e, hJ]

theorem map_orth (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E) (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) :
    (ι.map e)ᵀ *ᵥ (J.map e *ᵥ star (fun i => e (x i))) = 0 := by
  have h0 : ιᵀ *ᵥ (J *ᵥ fun i => σ (x i)) = 0 := transpose_mulVec_eq_zero ι _ hx
  have hs : star (fun i => e (x i)) = fun i => e (σ (x i)) := funext fun i => by simp [h.2.2.2 e]
  have e2 : (J.map e *ᵥ fun i => e (σ (x i))) = fun i => e ((J *ᵥ fun i => σ (x i)) i) :=
    funext fun i => (RingHom.map_mulVec e J _ i).symm
  have e3 : (ιᵀ.map e *ᵥ fun i => e ((J *ᵥ fun i => σ (x i)) i)) = fun k => e ((ιᵀ *ᵥ (J *ᵥ fun i => σ (x i))) k) :=
    funext fun k => (RingHom.map_mulVec e ιᵀ _ k).symm
  rw [hs, ← Matrix.transpose_map, e2, e3, h0]
  funext k
  simp

theorem map_gram (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) : (ι.map e)ᵀ * J.map e * (ι.map e).map star = (ιᵀ * J * ι.map σ).map e := by
  have : (ι.map e).map star = (ι.map σ).map e := by ext i j; simp [h.2.2.2 e]
  rw [this, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

end Help

section Help2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem form_single {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j <;> simp [h]
  simp [form, this, Matrix.mulVec_single, single_dotProduct]
end Help2

theorem exists_hyperbolic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  classical
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨x₀, hx₀, hx₀x₀⟩ := GlobalTheory.T.exists_isotropic_vector_hermitian_rank_ge_three_indefinite F E σ B hB n Y r s (by omega) hr hs hY
  obtain ⟨x, y, hxx, hyy, hxy, hL, hP⟩ := GlobalTheory.T.exists_hyperbolicPair_selfDualLattice_isotropic F E σ B hB n Y r s hY x₀ hx₀ hx₀x₀
  obtain ⟨ι, P, hPι, horth, hcomp⟩ := GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair F E σ n n₁ Y.J x y hn hY.herm hxx hyy hxy
  have hyx : form σ Y.J y x = 1 := by rw [form_swap hcm hY.herm, hxy, map_one]
  have hsplit : ∀ z ∈ Y.L, ∃ u, ι *ᵥ u ∈ Y.L ∧ z = form σ Y.J z y • x + ι *ᵥ u + form σ Y.J z x • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - form σ Y.J z x • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]; ring) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    refine ⟨u, ?_, ?_⟩
    · rw [← hu]; exact Y.L.sub_mem (Y.L.sub_mem hz (hL z hz).1) (hL z hz).2
    · rw [← hu]; abel
  set L₁ := Y.L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsFullLattice E := by
    refine { toIsLattice := GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix E n n₁ Y.L ι P hPι hY.lat.toIsLattice, span_eq_top := ?_ }
    refine eq_top_iff.2 fun u _ => ?_
    have hu : ι *ᵥ u ∈ Submodule.span E (Y.L : Set (Fin n → E)) :=
      hY.lat.span_eq_top ▸ Submodule.mem_top
    obtain ⟨z, hz, d, hd⟩ := (IsLocalization.mem_span_iff (M := nonZeroDivisors (𝓞 E))).1 hu
    have hdu : (d : 𝓞 E) • u ∈ L₁ := by
      change ι *ᵥ ((d : 𝓞 E) • u) ∈ Y.L
      rw [Matrix.mulVec_smul, hd, ← IsScalarTower.algebraMap_smul E (d : 𝓞 E), smul_smul,
        IsLocalization.mk'_spec', map_one, one_smul]
      simpa only [Submodule.span_eq] using hz
    have h := (Submodule.span E (L₁ : Set (Fin n₁ → E))).smul_mem
      (IsLocalization.mk' E 1 d) (Submodule.subset_span hdu)
    rwa [← IsScalarTower.algebraMap_smul E (d : 𝓞 E), smul_smul,
      IsLocalization.mk'_spec, map_one, one_smul] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_lattice_line_coefficients E n Y.L hY.lat.toIsLattice x hx0
  set J₁ := ιᵀ * Y.J * ι.map σ with hJ₁
  have hform₁ : ∀ u u', form σ J₁ u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hMh : ∀ w, (Y.J.map (e w))ᴴ = Y.J.map (e w) := fun w => map_herm hcm _ hY.herm
  have cxx : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (x i)) = 0 := fun w => by
    rw [← map_form hcm, hxx, map_zero]
  have cyy : ∀ w, (fun i => e w (y i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 0 := fun w => by
    rw [← map_form hcm, hyy, map_zero]
  have cxy : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 1 := fun w => by
    rw [← map_form hcm, hxy, map_one]
  have cox : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (x i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι x (fun u => (horth u).1)
  have coy : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (y i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι y (fun u => (horth u).2)
  have cP : ∀ w, P.map (e w) * ι.map (e w) = 1 := fun w => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have cg : ∀ w, (ι.map (e w))ᵀ * Y.J.map (e w) * (ι.map (e w)).map star = J₁.map (e w) := fun w =>
    map_gram hcm _ Y.J ι
  have hsig₁ : ∀ w, HasSig (J₁.map (e w)) (r - 1) (s - 1) := fun w => by
    rw [← cg w]
    exact GlobalTheory.T.hasHermitianSignature_complement_hyperbolicPlane n n₁ _ _ _ _ _ r s hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (hY.sig w)
  have hθ₁ : ∀ w, ∃ θ, IsCartan (J₁.map (e w)) θ := fun w => GlobalTheory.T.exists_cartanInvolution_of_hasHermitianSignature n₁ _ _ _ (hsig₁ w)
  choose θ₁ hθ₁ using hθ₁
  have hθ : ∀ w, ∃ θ, IsCartan (Y.J.map (e w)) θ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ w ∧
      θ *ᵥ (fun i => e w (x i)) = fun i => e w (y i) := fun w =>
    GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair n n₁ _ _ _ _ _ _ hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (by rw [cg w]; exact hθ₁ w)
  choose θ hθ using hθ
  haveI := hlat₁
  have hb₁ : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) L₁ β := fun v => exists_isSplitBasis (B.τ v) L₁ hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : Pl (F := F), GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map (B.τ v) * (β₁ v).1) r j) ∧
      IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.PlaneBasis.exists_isSplitBasis_plane F E σ hcm v (B.τ v) n n₁ Y.L x y ι (β₁ v) i₀ i₁ hn h01 h1n hY.lat
      (fun z hz => by
        obtain ⟨u, hu, hz'⟩ := hsplit z hz
        exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩) (hP v).1 (hP v).2 (hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : Pl (F := F), GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y₁ : Spc F E n₁ := ⟨J₁, L₁, θ₁, bas₁⟩
  let Y' : Spc F E n := ⟨Y.J, Y.L, θ, bas⟩
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hY.lat, dual := hY.dual, cartan := fun w => (hθ w).1
            bas := fun v => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v]
              exact (hβ v).2 }
  · exact { herm := fun i j => by
              show σ (J₁ j i) = J₁ i j
              rw [← form_single (σ := σ) J₁ j i, ← form_single (σ := σ) J₁ i j, hform₁, hform₁,
                form_swap hcm hY.herm (ι *ᵥ Pi.single j 1) (ι *ᵥ Pi.single i 1)]
            sig := hsig₁
            lat := hlat₁
            dual := fun u => by
              show u ∈ L₁ ↔ ∀ u' ∈ L₁, IsIntegral ℤ (form σ J₁ u u')
              refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
              · rw [hform₁]; exact (hY.dual _).1 hu _ hu'
              · show ι *ᵥ u ∈ Y.L
                refine (hY.dual _).2 fun z hz => ?_
                obtain ⟨u', hu', hz'⟩ := hsplit z hz
                rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
                  (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
                exact H u' hu'
            cartan := hθ₁
            bas := fun v => by
              rw [show Y₁.bas v = β₁ v from hbas₁ v]
              exact hβ₁ v }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := rfl, low := fun u => Iff.rfl
            split := fun z hz => by
              obtain ⟨u, hu, hz'⟩ := hsplit z hz
              exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩
            ideal := h𝔟
            cartan := fun w => ⟨(hθ w).2.1, 1, one_ne_zero, by rw [one_smul]; exact (hθ w).2.2.symm⟩
            bas := fun v i => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show Y₁.bas v = β₁ v from hbas₁ v]
              exact (hβ v).1 i }

end GlobalTheory.KTowerPlane
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpaceStatement
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  first | exact @GlobalTheory.KTowerPlane.exists_hyperbolic_split | exact GlobalTheory.KTowerPlane.exists_hyperbolic_split | (intros; apply GlobalTheory.KTowerPlane.exists_hyperbolic_split <;> assumption)
end
