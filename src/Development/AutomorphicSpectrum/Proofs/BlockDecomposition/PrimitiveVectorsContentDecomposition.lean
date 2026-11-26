module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderQuadraticAlmostAll
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderQuadraticAlmostAll
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SW.QuadRing

open GlobalTheory.CompanionTheory.SW.GoodRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem quad_at {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F)
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    ∃ (ι : v.adicCompletionIntegers F →+* O) (δ : O) (D : v.adicCompletionIntegers F),
      (δ * δ = ι D) ∧ (∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ) ∧
      (∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) ∧
      IsUnit D ∧ IsUnit (2 : v.adicCompletionIntegers F) := by
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  have hBC' : ∀ k j, B.repr (C k) j ∈ Rs := fun k j => by
    have := hBC k j
    rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this
  have hCB' : ∀ j k, C.repr (B j) k ∈ Rs := fun j k => by
    have := hCB j k
    rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this
  have hOB : ∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ Rs := fun y =>
    ⟨fun hy j => coord_mem Rs C B hBC' y ((hO y).1 hy) j,
      fun hy => (hO y).2 fun k => coord_mem Rs B C hCB' y hy k⟩
  have hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs →
      algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O := by
    intro p q hp hq
    have h := coord_two B hB0 p q
    refine (hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [h.1]; exact hp
    · rw [h.2]; exact hq
  have hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O := by
    intro c hc
    simpa using hpq c 0 hc Rs.zero_mem
  have hδO : B 1 ∈ O := by
    have := hpq 0 1 Rs.zero_mem Rs.one_mem
    rwa [map_zero, map_one, zero_add, one_mul] at this
  let ι : (v.adicCompletionIntegers F) →+* O :=
    ((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      (fun x => hRmem x x.2)
  let δ : O := ⟨B 1, hδO⟩
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hδ : δ * δ = ι D' := Subtype.ext hBD
  have hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ := fun y => by
    have hy := (hOB y).1 y.2
    exact ⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩
  have hinj : ∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' : algebraMap K (K ⊗[F] E) (p : K) + algebraMap K (K ⊗[F] E) (q : K) * B 1 = 0 :=
      congrArg Subtype.val h
    have hc := coord_two B hB0 (p : K) (q : K)
    rw [h'] at hc
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
    exact ⟨Subtype.ext hc.1.symm, Subtype.ext hc.2.symm⟩
  have hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1 := fun r =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  exact ⟨ι, δ, D', hδ, hsp, hinj, hDu, h2u⟩

theorem quad_ring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ (ι : v.adicCompletionIntegers F →+* O) (δ : O) (D : v.adicCompletionIntegers F), (δ * δ = ι D) ∧ (∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ) ∧ (∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) ∧ IsUnit D ∧ IsUnit (2 : v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB O hO
  exact quad_at b b₂ D hb0 hD v hD1 h21 hBC hCB O hO

end GlobalTheory.CompanionTheory.SW.QuadRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderQuadraticAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_quadratic_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ (ι : v.adicCompletionIntegers F →+* O) (δ : O) (D : v.adicCompletionIntegers F), (δ * δ = ι D) ∧ (∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ) ∧ (∀ p q : v.adicCompletionIntegers F, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) ∧ IsUnit D ∧ IsUnit (2 : v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadRing.quad_ring | exact GlobalTheory.CompanionTheory.SW.QuadRing.quad_ring | (intros; apply GlobalTheory.CompanionTheory.SW.QuadRing.quad_ring <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitive
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitive
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry

open GlobalTheory.CompanionTheory.SW.QuasiRefl

section Form

variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}

theorem hform_add_fst (x x' y : Fin N → A) :
    hform τ H (x + x') y = hform τ H x y + hform τ H x' y := by
  have h : (τ ∘ (x + x')) = τ ∘ x + τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, add_dotProduct]

theorem hform_add_snd (x y y' : Fin N → A) :
    hform τ H x (y + y') = hform τ H x y + hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_add, dotProduct_add]

theorem hform_sub_fst (x x' y : Fin N → A) :
    hform τ H (x - x') y = hform τ H x y - hform τ H x' y := by
  have h : (τ ∘ (x - x')) = τ ∘ x - τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, sub_dotProduct]

theorem hform_sub_snd (x y y' : Fin N → A) :
    hform τ H x (y - y') = hform τ H x y - hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_sub, dotProduct_sub]

theorem hform_unitary {g : GL (Fin N) A} (hg : g ∈ UJ τ H) (x y : Fin N → A) :
    hform τ H ((g : Matrix (Fin N) (Fin N) A) *ᵥ x) ((g : Matrix (Fin N) (Fin N) A) *ᵥ y) =
      hform τ H x y := by
  rw [hform_mulVec']
  have hg' : cT τ (g : Matrix (Fin N) (Fin N) A) * H * (g : Matrix (Fin N) (Fin N) A) = H := hg
  rw [hg']

theorem carry (hτ : ∀ y, τ (τ y) = y)
    (hcar : ∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1)
    (hH : ∀ i j, τ (H j i) = H i j) (x y : Fin N → A)
    (hxy : hform τ H x x = hform τ H y y) (hβ : IsUnit (hform τ H x x)) :
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ x = y ∧
      ∀ z, hform τ H x z = 0 → hform τ H y z = 0 → (g : Matrix (Fin N) (Fin N) A) *ᵥ z = z := by
  have hfix : τ (hform τ H x x) = hform τ H x x := hform_conj_symm hτ hH x x
  obtain ⟨ε, z, hε, hz⟩ := hcar (hform τ H y x) (hform τ H x x) hβ hfix
  exact exists_unitary_carry A τ hτ N H hH x y ε hxy hβ hε ⟨⟨_, z, hz, (mul_comm z _).trans hz⟩, rfl⟩

theorem exists_hyperbolic_partner (hτ : ∀ y, τ (τ y) = y) (h2 : IsUnit (2 : A))
    {Hi : Matrix (Fin N) (Fin N) A} (hHi : H * Hi = 1) (hH : ∀ i j, τ (H j i) = H i j)
    (y a : Fin N → A) (hyy : hform τ H y y = 0) (hay : ∑ k, a k * y k = 1) :
    ∃ y₁ : Fin N → A, hform τ H y₁ y₁ = 0 ∧ hform τ H y y₁ = 1 := by
  have hyw : hform τ H y (Hi *ᵥ (τ ∘ a)) = 1 := by
    rw [hform_eq_dot, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
    have h : (τ ∘ y) ⬝ᵥ (τ ∘ a) = τ (∑ k, a k * y k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Function.comp_apply, map_sum, map_mul]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [h, hay, map_one]
  have hwy : hform τ H (Hi *ᵥ (τ ∘ a)) y = 1 := by
    rw [← hform_conj_symm hτ hH y (Hi *ᵥ (τ ∘ a)), hyw, map_one]
  have hww : τ (hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := hform_conj_symm hτ hH _ _
  have ht2 : 2 * (↑h2.unit⁻¹ : A) = 1 := h2.mul_val_inv
  have hτt : τ (↑h2.unit⁻¹ : A) = ↑h2.unit⁻¹ := by
    have h1 : τ (↑h2.unit⁻¹ : A) * 2 = 1 := by
      have h := congrArg τ ht2
      rw [map_mul, map_one, map_ofNat] at h
      rw [mul_comm]
      exact h
    calc τ (↑h2.unit⁻¹ : A) = τ (↑h2.unit⁻¹ : A) * (2 * ↑h2.unit⁻¹) := by rw [ht2, mul_one]
      _ = (τ (↑h2.unit⁻¹ : A) * 2) * ↑h2.unit⁻¹ := by ring
      _ = ↑h2.unit⁻¹ := by rw [h1, one_mul]
  have hτc : τ ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      (↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := by
    rw [map_mul, hτt, hww]
  refine ⟨Hi *ᵥ (τ ∘ a) - ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) • y, ?_, ?_⟩
  · rw [hform_sub_left, hform_sub_right, hform_sub_right, hyy, hwy, hyw, hτc]
    linear_combination (-1 : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) * ht2
  · rw [hform_sub_right, hyw, hyy, mul_zero, sub_zero]

end Form

theorem exists_unitary_carry_primitive :
    ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) →
    (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) →
    ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) →
    ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 →
    hform τ H y y = 0 → ∑ k, a k * y k = 1 →
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  intro A _ τ hτ h2 hcar N H Hi hHi hH e f y a hee hff hef hyy hay
  obtain ⟨y₁, hy₁, hyy₁⟩ := exists_hyperbolic_partner hτ h2 hHi hH y a hyy hay
  have hfe : hform τ H f e = 1 := by rw [← hform_conj_symm hτ hH e f, hef, map_one]
  have hy₁y : hform τ H y₁ y = 1 := by rw [← hform_conj_symm hτ hH y y₁, hyy₁, map_one]
  have hx1 : hform τ H (e + f) (e + f) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    norm_num
  have hy1 : hform τ H (y + y₁) (y + y₁) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    norm_num
  obtain ⟨g₁, hg₁, hg₁x, -⟩ := carry hτ hcar hH (e + f) (y + y₁) (by rw [hx1, hy1]) (by rw [hx1]; exact h2)
  have hvv : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) = -2 := by
    rw [hform_unitary hg₁, hform_sub_fst, hform_sub_snd, hform_sub_snd, hee, hef, hfe, hff]
    ring
  have hyy' : hform τ H (y - y₁) (y - y₁) = -2 := by
    rw [hform_sub_fst, hform_sub_snd, hform_sub_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have h2' : IsUnit (-2 : A) := h2.neg
  obtain ⟨g₂, hg₂, hg₂v, hfix⟩ := carry hτ hcar hH ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y - y₁)
    (by rw [hvv, hyy']) (by rw [hvv]; exact h2')
  have hperp1 : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y + y₁) = 0 := by
    rw [← hg₁x, hform_unitary hg₁, hform_sub_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    ring
  have hperp2 : hform τ H (y - y₁) (y + y₁) = 0 := by
    rw [hform_sub_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have hfix' := hfix (y + y₁) hperp1 hperp2
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  have hsum : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e + f) = y + y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁x, hfix']
  have hdiff : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e - f) = y - y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₂v]
  have key : (2 : A) • (((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ e) = (2 : A) • y := by
    have h : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ ((e + f) + (e - f)) = (y + y₁) + (y - y₁) := by
      rw [Matrix.mulVec_add, hsum, hdiff]
    have he : (e + f) + (e - f) = (2 : A) • e := by
      rw [two_smul]
      abel
    have hy : (y + y₁) + (y - y₁) = (2 : A) • y := by
      rw [two_smul]
      abel
    rw [he, Matrix.mulVec_smul, hy] at h
    exact h
  have h3 := congrArg (fun z => (↑h2.unit⁻¹ : A) • z) key
  simp only [smul_smul, h2.val_inv_mul, one_smul] at h3
  exact h3

end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitiveStatement
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_unitary_transitive : ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) → (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) → ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) → ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 → hform τ H y y = 0 → ∑ k, a k * y k = 1 → ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | exact GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitQuadraticOrderPrincipal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitQuadraticOrderPrincipal
namespace GlobalTheory.CompanionTheory.SplitQuadratic

theorem isPrincipalIdealRing_of_sq_eq_sq :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
      (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) →
      (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ ι δ e hδ hspan _ he h2
  obtain ⟨e', he'⟩ := he.exists_right_inv
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hee' : ι e * ι e' = 1 := by rw [← map_mul, he', map_one]
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι hh
    rwa [map_mul, map_one, map_ofNat] at this
  have hδ' : δ * δ = ι e * ι e := by rw [hδ, map_mul]

  have hu2 : (ι e' * δ) * (ι e' * δ) = 1 := by
    linear_combination (ι e' * ι e') * hδ' + (ι e * ι e' + 1) * hee'

  set ε₁ : O := ι h * (1 + ι e' * δ) with hε₁
  set ε₂ : O := ι h * (1 - ι e' * δ) with hε₂
  have h11 : ε₁ * ε₁ = ε₁ := by
    rw [hε₁]
    linear_combination (ι h * (1 + ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h22 : ε₂ * ε₂ = ε₂ := by
    rw [hε₂]
    linear_combination (ι h * (1 - ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h12 : ε₁ * ε₂ = 0 := by
    rw [hε₁, hε₂]
    linear_combination (-(ι h * ι h)) * hu2
  have hsum : ε₁ + ε₂ = 1 := by
    rw [hε₁, hε₂]
    linear_combination h2'

  let φ : R × R →+* O :=
    { toFun := fun x => ι x.1 * ε₁ + ι x.2 * ε₂
      map_one' := by
        simp only [Prod.fst_one, Prod.snd_one, map_one, one_mul]
        exact hsum
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(ι x.1 * ι y.1)) * h11 + (-(ι x.2 * ι y.2)) * h22 +
          (-(ι x.1 * ι y.2 + ι x.2 * ι y.1)) * h12
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        ring }
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p, q, rfl⟩ := hspan y
    refine ⟨(p + q * e, p - q * e), ?_⟩
    show ι (p + q * e) * ε₁ + ι (p - q * e) * ε₂ = ι p + ι q * δ
    rw [hε₁, hε₂]
    simp only [map_add (f := _), map_sub, map_mul]
    linear_combination (ι p + ι q * ι e * ι e' * δ) * h2' + (ι q * δ) * hee'
  exact IsPrincipalIdealRing.of_surjective φ hsurj

end GlobalTheory.CompanionTheory.SplitQuadratic
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitQuadraticOrderPrincipalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | exact GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | (intros; apply GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticOrderPrincipal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticOrderPrincipal
namespace GlobalTheory.CompanionTheory.QuadraticUnit

open Polynomial IsLocalRing

theorem norm_isUnit {R : Type} [CommRing R] [HenselianLocalRing R] (D : R) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (a * a - D * (b * b)) := by
  have hmax : ∀ x : R, x ∈ maximalIdeal R ↔ ¬ IsUnit x := fun x => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
  by_contra hnu
  have hm : a * a - D * (b * b) ∈ maximalIdeal R := (hmax _).2 hnu
  have hb : IsUnit b := by
    rcases hab with ha | hb
    · by_contra hb
      have hbm : b ∈ maximalIdeal R := (hmax b).2 hb
      have haa : a * a ∈ maximalIdeal R := by
        have he : a * a = (a * a - D * (b * b)) + D * (b * b) := by ring
        rw [he]
        exact add_mem hm (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hbm))
      exact (hmax _).1 haa (ha.mul ha)
    · exact hb
  obtain ⟨w, hw⟩ : ∃ w : R, b * w = 1 := ⟨_, hb.mul_val_inv⟩
  set c := a * w with hc
  have hcD : c * c - D ∈ maximalIdeal R := by
    have he : c * c - D = (a * a - D * (b * b)) * (w * w) := by
      have hw2 : D = D * ((b * w) * (b * w)) := by rw [hw]; ring
      rw [hc]
      nth_rewrite 1 [hw2]
      ring
    rw [he]
    exact Ideal.mul_mem_right _ _ hm
  have hcc : IsUnit (c * c) := by
    by_contra hcc
    have hDm : D ∈ maximalIdeal R := by
      have he : D = c * c - (c * c - D) := by ring
      rw [he]
      exact sub_mem ((hmax _).2 hcc) hcD
    exact (hmax _).1 hDm hD
  have hcu : IsUnit c := isUnit_of_mul_isUnit_left hcc
  obtain ⟨e, he, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C D) (monic_X_pow_sub_C D two_ne_zero) c
    (by simpa [sq] using hcD) (by simpa [derivative_X_pow, one_add_one_eq_two] using h2.mul hcu)
  apply hns
  refine ⟨e, ?_⟩
  have := he.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at this
  linear_combination -this

theorem isUnit_add_mul {R O : Type} [CommRing R] [HenselianLocalRing R] [CommRing O]
    (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (a b : R)
    (hab : IsUnit a ∨ IsUnit b) : IsUnit (ι a + ι b * δ) := by
  have hn := (norm_isUnit D hD h2 hns a b hab).map ι
  have he : (ι a + ι b * δ) * (ι a - ι b * δ) = ι (a * a - D * (b * b)) := by
    rw [map_sub, map_mul, map_mul, map_mul, ← hδ]
    ring
  rw [← he] at hn
  exact isUnit_of_mul_isUnit_left hn

theorem exists_eq_mul_isUnit {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R) (hδ : δ * δ = ι D)
    (hspan : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ) (hD : IsUnit D)
    (h2 : IsUnit (2 : R)) (hns : ¬ ∃ e : R, D = e * e) (y : O) :
    ∃ (g : R) (u : O), IsUnit u ∧ y = ι g * u := by
  obtain ⟨p, q, rfl⟩ := hspan y
  rcases ValuationRing.dvd_total p q with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · refine ⟨p, 1 + ι r * δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns 1 r (Or.inl isUnit_one)
  · refine ⟨q, ι r + δ, ?_, by rw [map_mul]; ring⟩
    simpa using isUnit_add_mul ι δ D hδ hD h2 hns r 1 (Or.inr isUnit_one)

theorem isPrincipalIdealRing_of_nonsquare_unit :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
      [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ _ ι δ D hδ hspan _ hD h2 hns
  refine ⟨fun I => ⟨?_⟩⟩
  obtain ⟨g₀, hg₀⟩ := (IsPrincipalIdealRing.principal (Ideal.comap ι I)).principal
  have hg₀I : ι g₀ ∈ I := by
    have hmem : g₀ ∈ Ideal.comap ι I := by
      rw [hg₀]
      exact Submodule.mem_span_singleton_self g₀
    exact Ideal.mem_comap.1 hmem
  refine ⟨ι g₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).2 hg₀I)⟩
  intro y hy
  obtain ⟨g, u, hu, rfl⟩ := exists_eq_mul_isUnit ι δ D hδ hspan hD h2 hns y
  have hg : g ∈ Ideal.comap ι I := by
    rw [Ideal.mem_comap]
    have he : ι g = ι g * u * ↑hu.unit⁻¹ := by rw [mul_assoc, hu.mul_val_inv, mul_one]
    rw [he]
    exact I.mul_mem_right _ hy
  rw [hg₀] at hg
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hg
  refine Ideal.mem_span_singleton.2 ⟨ι r * u, ?_⟩
  rw [← hr, smul_eq_mul, map_mul]
  ring

end GlobalTheory.CompanionTheory.QuadraticUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticOrderPrincipalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | exact GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | (intros; apply GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecomposition
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec

theorem hform_single {A : Type} [CommRing A] (τ : A →+* A) {N : ℕ} (H : Matrix (Fin N) (Fin N) A) (a b : Fin N) :
    hform τ H (Pi.single a 1) (Pi.single b 1) = H a b := by
  simp [hform, Pi.single_apply, Finset.sum_ite_eq]

theorem exists_content {T : Type} [CommRing T] [IsArtinianRing T] (O : Subring T) [IsPrincipalIdealRing O] {N : ℕ}
    (y : Fin N → T) (hy : ∀ k, y k ∈ O) (hfree : ∀ c : T, (∀ k, c * y k = 0) → c = 0) :
    ∃ x ∈ O, IsUnit x ∧ ∃ y₀ a : Fin N → T, (∀ k, y₀ k ∈ O) ∧ (∀ k, a k ∈ O) ∧ (∀ k, y k = x * y₀ k) ∧
      ∑ k, a k * y₀ k = 1 := by
  let yO : Fin N → O := fun k => ⟨y k, hy k⟩
  obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range yO))).principal
  have hdiv : ∀ k, ∃ t : O, t * x = yO k := fun k => by
    have h : yO k ∈ Ideal.span (Set.range yO) := Ideal.subset_span ⟨k, rfl⟩
    rw [hx] at h
    exact Ideal.mem_span_singleton'.1 h
  choose t ht using hdiv
  have hxm : x ∈ Ideal.span (Set.range yO) := by
    rw [hx]; exact Ideal.mem_span_singleton_self x
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hxm
  have hyk : ∀ k, y k = (x : T) * (t k : T) := fun k => by
    have := congrArg Subtype.val (ht k)
    simp only [Subring.coe_mul, yO] at this
    rw [← this, mul_comm]
  have hnz : (x : T) ∈ nonZeroDivisors T := by
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    exact hfree c fun k => by rw [hyk, ← mul_assoc, hc, zero_mul]
  have hu : IsUnit (x : T) := (IsArtinianRing.isUnit_iff_mem_nonZeroDivisors).2 hnz
  refine ⟨x, x.2, hu, fun k => t k, fun k => a k, fun k => (t k).2, fun k => (a k).2, hyk, ?_⟩
  have h1 : (x : T) * ∑ k, (a k : T) * (t k : T) = x * 1 := by
    have := congrArg Subtype.val ha
    simp only [Subring.coe_mul, AddSubmonoidClass.coe_finsetSum, yO] at this
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← this]
    exact Finset.sum_congr rfl fun k _ => by rw [hyk k]; ring
  exact hu.mul_left_cancel h1

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M d : ℕ}
  (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem exists_of_mem_primV (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F)
    {y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E} (hy : y ∈ primV σ J b v) :
    (∀ i, y 0 i ∈ O) ∧ ∃ a : Fin (M + 2) → Fv F v ⊗[F] E, (∀ i, a i ∈ O) ∧ ∑ k, a k * y 0 k = 1 := by
  obtain ⟨g, hg, rfl⟩ := hy
  set G : GL (Fin (M + 2)) (Fv F v ⊗[F] E) := HA.mat (Fv F v) σ (hypOne J) g with hG
  have hact : ∀ (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (t : Fin 1),
      actW (Fv F v) σ (hypOne J) g X t = (G : Matrix _ _ _) *ᵥ X t := fun _ _ => rfl
  have hlat : ∀ X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
    fun X => GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO X
  have he : (e0 (Fv F v ⊗[F] E) M) ∈ latV b v := by
    rw [hlat]
    intro a i
    induction i using Fin.cases with
    | zero => exact O.one_mem
    | succ i => exact O.zero_mem
  have hy := (hg _).2 he
  rw [hlat] at hy
  let Gi : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E) := ((G⁻¹ : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E))
  refine ⟨hy 0, fun k => Gi 0 k, fun k => ?_, ?_⟩
  · let x : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E :=
      fun _ => Gi *ᵥ Pi.single k 1
    have hgx : actW (Fv F v) σ (hypOne J) g x ∈ latV b v := by
      rw [hlat]
      intro a i
      rw [hact]
      simp only [x]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : i = k
      · subst h; simpa using O.one_mem
      · simpa [Pi.single_apply, h] using O.zero_mem
    have hx := (hg x).1 hgx
    rw [hlat] at hx
    have := hx 0 0
    simpa [x, Matrix.mulVec_single_one] using this
  · have h0 : Gi *ᵥ ((G : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ e0 (Fv F v ⊗[F] E) M 0) =
        e0 (Fv F v ⊗[F] E) M 0 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have h1 := congrFun h0 0
    rw [← hact] at h1
    simpa [Matrix.mulVec, dotProduct, e0] using h1

theorem mem_primV_of (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F)
    (hstab : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O) (hss : ∀ z, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z)
    (h2 : IsUnit (2 : O))
    (hgood : ∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O,
      (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧ ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1)
    (Hi : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E))
    (hHO : ∀ i j, JR (Fv F v) (hypOne J) i j ∈ O) (hHiO : ∀ i j, Hi i j ∈ O)
    (hmul : JR (Fv F v) (hypOne J) * Hi = 1)
    (hJ : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) (hypOne J) j i) = JR (Fv F v) (hypOne J) i j)
    (y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (hy : ∀ i, y 0 i ∈ O)
    (a : Fin (M + 2) → Fv F v ⊗[F] E) (ha : ∀ i, a i ∈ O) (hsum : ∑ k, a k * y 0 k = 1)
    (hiso : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (y 0) (y 0) = 0) : y ∈ primV σ J b v := by
  set s := sigR (Fv F v) σ with hs
  set H : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E) := JR (Fv F v) (hypOne J) with hH
  let τ : O →+* O := s.restrict O O hstab
  have hτ : ∀ a : O, ((τ a : O) : Fv F v ⊗[F] E) = s a := fun a => rfl
  let HO : Matrix (Fin (M + 2)) (Fin (M + 2)) O := fun i j => ⟨H i j, hHO i j⟩
  let HiO : Matrix (Fin (M + 2)) (Fin (M + 2)) O := fun i j => ⟨Hi i j, hHiO i j⟩
  let y0 : Fin (M + 2) → O := fun i => ⟨y 0 i, hy i⟩
  let a0 : Fin (M + 2) → O := fun i => ⟨a i, ha i⟩
  have hcoe : ∀ p q : Fin (M + 2) → O, ((hform τ HO p q : O) : Fv F v ⊗[F] E) =
      hform s H (fun i => (p i : Fv F v ⊗[F] E)) (fun i => (q i : Fv F v ⊗[F] E)) := by
    intro p q
    simp [hform, hτ, HO]
  have hval : ∀ g : GL (Fin (M + 2)) O, ((bc O.subtype g : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) =
      (g : Matrix (Fin (M + 2)) (Fin (M + 2)) O).map O.subtype := fun g => rfl
  have hmulO : HO * HiO = 1 := by
    refine Matrix.ext fun i j => Subtype.ext ?_
    have := congrFun (congrFun hmul i) j
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
    simp only [Subring.coe_mul, HO, HiO]
    rw [this]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  obtain ⟨g0, hg0, hgx⟩ := GlobalTheory.T.hyperbolic_pair_unitary_transitive O τ (fun z => Subtype.ext (hss z)) h2
    (fun p β hβ hf => by
      obtain ⟨ε, z, h1, h3⟩ := hgood p β hβ (congrArg Subtype.val hf)
      exact ⟨ε, z, Subtype.ext h1, Subtype.ext h3⟩)
    (M + 2) HO HiO hmulO (fun i j => Subtype.ext (hJ i j)) (Pi.single 0 1) (Pi.single 1 1) y0 a0
    (by rw [hform_single]; exact Subtype.ext (by simp [HO, H, JR, hypOne_zero_zero]))
    (by rw [hform_single]; exact Subtype.ext (by simp [HO, H, JR, hypOne_one_one]))
    (by rw [hform_single]; exact Subtype.ext (by simp [HO, H, JR, hypOne_zero_one]))
    (Subtype.ext (by rw [hcoe]; exact hiso))
    (Subtype.ext (by simpa [a0, y0] using hsum))
  have hmem : bc O.subtype g0 ∈ HR (Fv F v) σ (hypOne J) := by
    have h0 : cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) * HO *
        (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) = HO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) * H *
      ((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) = H
    exact h1
  let h' : HA (Fv F v) σ (hypOne J) := (⟨bc O.subtype g0, hmem⟩ : HR (Fv F v) σ (hypOne J))
  have hact : ∀ (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (t : Fin 1),
      actW (Fv F v) σ (hypOne J) h' X t = ((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ X t := fun _ _ => rfl
  refine ⟨h', fun X => ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO, GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO]
    constructor
    · intro hX t i
      have e : X t = ((bc O.subtype g0⁻¹ : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ
          (((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ X t) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
      rw [e]
      refine GlobalTheory.CompanionTheory.SW.GoodTrans.mulVec_mem O _ (fun p q => ?_) _ (fun j => ?_) i
      · rw [hval]
        exact ((g0⁻¹ : GL (Fin (M + 2)) O) : Matrix (Fin (M + 2)) (Fin (M + 2)) O) p q |>.2
      · rw [← hact]; exact hX t j
    · intro hX t i
      rw [hact]
      refine GlobalTheory.CompanionTheory.SW.GoodTrans.mulVec_mem O _ (fun p q => ?_) _ (hX t) i
      rw [hval]
      exact ((g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) p q).2
  · funext t
    rw [Fin.fin_one_eq_zero t, hact, hval]
    funext i
    have h1 := congrArg Subtype.val (congrFun hgx i)
    have he : e0 (Fv F v ⊗[F] E) M 0 = fun j => ((Pi.single 0 1 : Fin (M + 2) → O) j : Fv F v ⊗[F] E) := by
      funext j
      induction j using Fin.cases with
      | zero => simp [e0]
      | succ j => simp [e0, Pi.single_apply, Fin.succ_ne_zero]
    rw [he]
    simpa [Matrix.mulVec, dotProduct, y0] using h1

end Loc

theorem eventually_primV_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (ι : Type) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w → MeasurableSet (primV σ J b v) ∧ (∀ i, ∀ y ∈ primV σ J b v, scalT (c i) y ∈ latV b v) ∧ (∀ i j, ∀ y ∈ primV σ J b v, ∀ y' ∈ primV σ J b v, scalT (c i) y = scalT (c j) y' → i = j) ∧ (∀ y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → y ∈ latV b v → ∃ i, ∃ y₀ ∈ primV σ J b v, y = scalT (c i) y₀) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  have hND := PrimMeas.isHermND_hypOne σ J hJ
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hσ.2.2.2, hσ.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hσ d b
  filter_upwards [PrimMeas.eventually_measurableSet_primV F E σ hσ M J hJ d b,
    GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ hσ d b, GlobalTheory.T.local_order_quadratic_almost_all F E σ hσ d b,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (hypOne J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 ((hypOne J)⁻¹ i j)]
    with v hmeas hring hquad hH hHi
  obtain ⟨O, hO, hstab, -, h2, -, hgood, -⟩ := hring
  intro ι c w hc
  obtain ⟨hc1, -, -, hc4, hc5⟩ := hc
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  have hint : ∀ x, x ∈ intK b v ↔ x ∈ O := fun x => (hO x).symm
  set Hi : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E) := JR (Fv F v) (hypOne J)⁻¹ with hHidef
  have hHO : ∀ i j, JR (Fv F v) (hypOne J) i j ∈ O := fun i j => (hO _).2 (hH i j)
  have hHiO : ∀ i j, Hi i j ∈ O := fun i j => (hO _).2 (hHi i j)
  have hmul : JR (Fv F v) (hypOne J) * Hi = 1 := by
    have h1 : hypOne J * (hypOne J)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hND.2)
    have h3 := congrArg (RingHom.mapMatrix (inclR (F := F) (E := E) (Fv F v))) h1
    rw [map_mul, map_one] at h3
    exact h3
  have hJR : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) (hypOne J) j i) = JR (Fv F v) (hypOne J) i j := by
    intro i j
    show sigR (Fv F v) σ (inclR (Fv F v) (hypOne J j i)) = inclR (Fv F v) (hypOne J i j)
    rw [← hND.1 i j]
    rfl
  have hprim := fun y hy a ha hsum hiso => mem_primV_of σ J b v O hO hstab hss h2 hgood Hi hHO hHiO hmul hJR y hy a ha hsum hiso
  have hex := fun {y} (hy : y ∈ primV σ J b v) => exists_of_mem_primV σ J b v O hO hy
  have hlat : ∀ X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
    fun X => GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO X
  have hpir : IsPrincipalIdealRing O := by
    obtain ⟨ι', δ, D, h1, h3, h4, h5, h6⟩ := hquad O hO
    haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
    haveI : HenselianLocalRing (v.adicCompletionIntegers F) := GlobalTheory.henselianLocalRing_of_isAdicComplete _
    by_cases hsq : ∃ e, D = e * e
    · obtain ⟨e, rfl⟩ := hsq
      exact GlobalTheory.T.split_quadratic_order_principal _ O ι' δ e h1 h3 h4 (isUnit_of_mul_isUnit_left h5) h6
    · exact GlobalTheory.T.unramified_quadratic_order_principal _ O ι' δ D h1 h3 h4 h5 h6 hsq
  haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := by
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
    infer_instance
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  refine ⟨hmeas, fun i y hy => ?_, fun i j y hy y' hy' he => ?_, fun y hli hg hy => ?_⟩
  · have h1 := (hex hy).1
    rw [hlat]
    intro a k
    rw [Fin.fin_one_eq_zero a]
    exact O.mul_mem ((hint _).1 (hc1 i).2) (h1 k)
  · obtain ⟨h1, a, ha, hs⟩ := hex hy
    obtain ⟨h1', a', ha', hs'⟩ := hex hy'
    have hek : ∀ k, c i * y 0 k = c j * y' 0 k := fun k => congrFun (congrFun he 0) k
    set u := ∑ k, a k * y' 0 k with hu
    set u' := ∑ k, a' k * y 0 k with hu'
    have huO : u ∈ O := O.sum_mem fun k _ => O.mul_mem (ha k) (h1' k)
    have hu'O : u' ∈ O := O.sum_mem fun k _ => O.mul_mem (ha' k) (h1 k)
    have e1 : c i = c j * u := by
      calc c i = c i * ∑ k, a k * y 0 k := by rw [hs, mul_one]
        _ = c j * u := by
          rw [hu, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by linear_combination (a k) * hek k
    have e2 : c j = c i * u' := by
      calc c j = c j * ∑ k, a' k * y' 0 k := by rw [hs', mul_one]
        _ = c i * u' := by
          rw [hu', Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by linear_combination -(a' k) * hek k
    have huu : u * u' = 1 := by
      have : c i * (u * u') = c i * 1 := by
        calc c i * (u * u') = (c i * u') * u := by ring
          _ = c i * 1 := by rw [← e2, ← e1, mul_one]
      exact (hc1 i).1.mul_left_cancel this
    exact hc5 i j u ((hint _).2 huO) u' ((hint _).2 hu'O) huu e1
  · rw [hlat] at hy
    have hfree : ∀ t : Fv F v ⊗[F] E, (∀ k, t * y 0 k = 0) → t = 0 := by
      intro t ht
      have h1 := Fintype.linearIndependent_iff.1 hli (fun _ => t) (by
        funext k
        simpa [Fin.sum_univ_succ] using ht k)
      exact h1 0
    obtain ⟨x, hxO, hxu, y₀, a, hy₀, ha, hyx, hs⟩ := exists_content O (y 0) (hy 0) hfree
    obtain ⟨i, u, huO, u', hu'O, huu, hxc⟩ := hc4 x ((hint _).2 hxO) hxu
    rw [hint] at huO hu'O
    refine ⟨i, fun _ k => u * y₀ k, hprim _ (fun k => O.mul_mem huO (hy₀ k)) (fun k => u' * a k)
      (fun k => O.mul_mem hu'O (ha k)) ?_ ?_, ?_⟩
    · calc ∑ k, u' * a k * (u * y₀ k) = (u * u') * ∑ k, a k * y₀ k := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = 1 := by rw [huu, hs, one_mul]
    · have h0 : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (y 0) (y 0) = 0 := congrFun (congrFun hg 0) 0
      have hsc : ∀ (t : Fv F v ⊗[F] E) (p : Fin (M + 2) → Fv F v ⊗[F] E),
          hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (fun k => t * p k) (fun k => t * p k) =
            sigR (Fv F v) σ t * t * hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) p p := by
        intro t p
        simp only [hform, Finset.mul_sum, map_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hyy : y 0 = fun k => x * y₀ k := funext hyx
      rw [hyy, hsc] at h0
      have hxs : IsUnit (sigR (Fv F v) σ x * x) := (hxu.map (sigR (Fv F v) σ)).mul hxu
      have h00 := hxs.mul_right_eq_zero.1 h0
      show hform _ _ (fun k => u * y₀ k) (fun k => u * y₀ k) = 0
      rw [hsc, h00, mul_zero]
    · funext t k
      rw [Fin.fin_one_eq_zero t]
      show y 0 k = c i * (u * y₀ k)
      rw [hyx k, hxc]; ring

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecompositionStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vectors_content_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (ι : Type) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w → MeasurableSet (primV σ J b v) ∧ (∀ i, ∀ y ∈ primV σ J b v, scalT (c i) y ∈ latV b v) ∧ (∀ i j, ∀ y ∈ primV σ J b v, ∀ y' ∈ primV σ J b v, scalT (c i) y = scalT (c j) y' → i = j) ∧ (∀ y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → y ∈ latV b v → ∃ i, ∃ y₀ ∈ primV σ J b v, y = scalT (c i) y₀) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition <;> assumption)
end
