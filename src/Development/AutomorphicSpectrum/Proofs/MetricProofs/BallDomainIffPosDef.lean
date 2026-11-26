module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDef
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDef
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

theorem exists_sqLen {m : Type} [Fintype m] (x : m → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ star x ⬝ᵥ x = (r : ℂ) ∧ (x ≠ 0 → 0 < r) := by
  have h0 : 0 ≤ star x ⬝ᵥ x := dotProduct_star_self_nonneg x
  have hz := Complex.nonneg_iff.1 h0
  have heq : star x ⬝ᵥ x = (((star x ⬝ᵥ x).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz.2.symm
  refine ⟨(star x ⬝ᵥ x).re, hz.1, heq, fun hx => ?_⟩
  have hp : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.2 hx
  exact (Complex.pos_iff.1 hp).1

theorem qf_one_sub {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ ((1 - Aᴴ * A) *ᵥ w) = star w ⬝ᵥ w - star (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
  rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]

theorem posDef_adjoint {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ)
    (h : (1 - Aᴴ * A).PosDef) : (1 - A * Aᴴ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · simp [IsHermitian, conjTranspose_sub, conjTranspose_mul]
  have hq := qf_one_sub Aᴴ v
  rw [conjTranspose_conjTranspose] at hq
  rw [hq]
  obtain ⟨c, hc0, hc, hcp⟩ := exists_sqLen v
  obtain ⟨a, ha0, ha, hap⟩ := exists_sqLen (Aᴴ *ᵥ v)
  rw [hc, ha, ← Complex.ofReal_sub]
  have hcpos := hcp hv
  suffices hac : a < c from by exact_mod_cast sub_pos.2 hac
  by_cases hw : Aᴴ *ᵥ v = 0
  · have : a = 0 := by
      have : (a : ℂ) = 0 := by rw [← ha, hw]; simp
      exact_mod_cast this
    rw [this]; exact hcpos
  have hapos := hap hw
  set w := Aᴴ *ᵥ v with hwdef
  obtain ⟨b, hb0, hb, -⟩ := exists_sqLen (A *ᵥ w)
  have hba : b < a := by
    have h1 := (posDef_iff_dotProduct_mulVec.1 h).2 hw
    rw [qf_one_sub, ha, hb, ← Complex.ofReal_sub] at h1
    have : (0 : ℝ) < a - b := by exact_mod_cast h1
    linarith
  have hpv : star (A *ᵥ w) ⬝ᵥ v = (a : ℂ) := by
    rw [star_mulVec, ← dotProduct_mulVec, ← hwdef, ha]
  have hvp : star v ⬝ᵥ (A *ᵥ w) = (a : ℂ) := by
    rw [dotProduct_mulVec, ← star_star (star v ᵥ* A)]
    rw [star_vecMul, star_star, ← hwdef, ha]
  have hu := dotProduct_star_self_nonneg ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v)
  have hexp : star ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) ⬝ᵥ ((c : ℂ) • (A *ᵥ w) - (a : ℂ) • v) =
      ((c * (c * b - a ^ 2) : ℝ) : ℂ) := by
    simp only [star_sub, star_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, hb, hc, hpv, hvp]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    push_cast
    ring
  rw [hexp] at hu
  have hu' : 0 ≤ c * (c * b - a ^ 2) := by exact_mod_cast hu
  have h2 : 0 ≤ c * b - a ^ 2 := nonneg_of_mul_nonneg_right hu' hcpos
  nlinarith

theorem posDef_adjoint_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    (1 - Aᴴ * A).PosDef ↔ (1 - A * Aᴴ).PosDef :=
  ⟨posDef_adjoint A, fun h => by simpa using posDef_adjoint Aᴴ (by simpa using h)⟩

theorem posDef_blockDiagonal_iff {m o : Type} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (M : o → Matrix m m ℂ) : (blockDiagonal M).PosDef ↔ ∀ k, (M k).PosDef := by
  constructor
  · intro h k
    have hinj : Function.Injective (fun i : m => (i, k)) := fun a b hab => (Prod.ext_iff.1 hab).1
    have := h.submatrix hinj
    convert this using 1
    ext a b
    simp [blockDiagonal_apply]
  · intro h
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, blockDiagonal_conjTranspose]
      congr 1
      funext k
      exact (h k).1
    have hmv : ∀ i k, (blockDiagonal M *ᵥ x) (i, k) = (M k *ᵥ fun i => x (i, k)) i := by
      intro i k
      simp only [mulVec, dotProduct, Fintype.sum_prod_type_right, blockDiagonal_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    have hsum : star x ⬝ᵥ (blockDiagonal M *ᵥ x) =
        ∑ k, star (fun i => x (i, k)) ⬝ᵥ (M k *ᵥ fun i => x (i, k)) := by
      simp only [dotProduct, Fintype.sum_prod_type_right, hmv]
      rfl
    rw [hsum]
    obtain ⟨⟨i, k⟩, hp⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun k _ => (h k).posSemidef.dotProduct_mulVec_nonneg _) ⟨k, Finset.mem_univ _, ?_⟩
    refine (posDef_iff_dotProduct_mulVec.1 (h k)).2 (Function.ne_iff.2 ⟨i, ?_⟩)
    simpa using hp

theorem posDef_fromBlocks_diag_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) : (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  constructor
  · intro h
    constructor
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inl : m → m ⊕ n) Sum.inl = A := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inl_injective
    · have h1 : (fromBlocks A 0 0 D).submatrix (Sum.inr : n → m ⊕ n) Sum.inr = D := by
        ext a c; simp
      exact h1 ▸ h.submatrix Sum.inr_injective
  · rintro ⟨hA, hD⟩
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · rw [IsHermitian, fromBlocks_conjTranspose, hA.1, hD.1]
      simp
    have hsum : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
        star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
      rw [fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type]
    rw [hsum]
    have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
    rcases p with i | i
    · refine add_pos_of_pos_of_nonneg ((posDef_iff_dotProduct_mulVec.1 hA).2 (Function.ne_iff.2 ⟨i, ?_⟩)) h2
      simpa using hp
    · refine add_pos_of_nonneg_of_pos h1 ((posDef_iff_dotProduct_mulVec.1 hD).2 (Function.ne_iff.2 ⟨i, ?_⟩))
      simpa using hp

theorem posDef_transpose_block {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (Z : Matrix m n ℂ) :
    (1 - Zᵀᴴ * Zᵀ).PosDef ↔ (1 - Zᴴ * Z).PosDef := by
  rw [posDef_adjoint_iff Z, ← PosDef.transpose_iff (M := 1 - Z * Zᴴ)]
  have : (1 - Z * Zᴴ)ᵀ = 1 - Zᵀᴴ * Zᵀ := by
    rw [transpose_sub, transpose_one, transpose_mul]
    congr 2
  rw [this]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.MemBall

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ


open MemBall in
theorem mem_ballDom_iff_posDef_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  have hblk : (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t =
      blockDiagonal fun τ => fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0
        (1 - (ballMat q t τ)ᵀᴴ * (ballMat q t τ)ᵀ) := by
    rw [bigZ, blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
    congr 1
    funext τ
    simp only [Pi.sub_apply, Pi.one_apply]
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [conjTranspose_zero, mul_zero, add_zero, zero_add, ← fromBlocks_one]
    ext (a | a) (c | c) <;> simp [Matrix.one_apply]
  have hsub : (1 : Matrix (Fin g) (Fin g) ℂ) - (bigZe e q t)ᴴ * bigZe e q t =
      ((1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ) - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    rw [bigZe, conjTranspose_submatrix, submatrix_mul_equiv]
    ext a c
    simp [Matrix.one_apply]
  have hequiv : ((1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm).PosDef ↔
      (1 - (bigZ q t)ᴴ * bigZ q t).PosDef :=
    ⟨fun h => by simpa using h.submatrix e.injective, fun h => h.submatrix e.symm.injective⟩
  rw [hsub, hequiv, hblk, MemBall.posDef_blockDiagonal_iff]
  simp only [MemBall.posDef_fromBlocks_diag_iff, MemBall.posDef_transpose_block, and_self]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDefStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_domain_iff_pos_def : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphisms
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphisms
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

section Ext

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem exists_basis (e : Λ →+ V) (hspan : Submodule.span E (e.range : Set V) = ⊤) :
    ∃ (I : Type) (b : Module.Basis I E V) (xs : I → Λ), ∀ i, b i = e (xs i) := by
  obtain ⟨B, hB, hsp, hli⟩ := exists_linearIndependent E (e.range : Set V)
  have hx : ∀ i : B, ∃ x, e x = i.1 := fun i => AddMonoidHom.mem_range.1 (hB i.2)
  choose xs hxs using hx
  refine ⟨B, Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hspan]), xs, fun i => ?_⟩
  rw [Module.Basis.mk_apply, hxs]

theorem exists_clear {I : Type} (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) (b : Module.Basis I E V) (xs : I → Λ)
    (hb : ∀ i, b i = e (xs i)) (x : Λ) :
    ∃ (d : 𝓞 E) (s : Finset I) (a : I → 𝓞 E), d ≠ 0 ∧ d • x = ∑ i ∈ s, a i • xs i := by
  classical
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (b.repr (e x)).support (fun i => b.repr (e x) i)
  have h2 : ∀ i ∈ (b.repr (e x)).support, ∃ a : 𝓞 E, (a : E) = (d : E) * b.repr (e x) i := by
    intro i hi
    obtain ⟨a, ha⟩ := hint i hi
    refine ⟨a, ?_⟩
    rw [show (a : E) = algebraMap (𝓞 E) E a from rfl, ha, Algebra.smul_def]
  choose! a ha using h2
  refine ⟨d, (b.repr (e x)).support, a, nonZeroDivisors.ne_zero hd, he ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum]
  conv_lhs => rw [← b.linearCombination_repr (e x), Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hs, ← hb, ha i hi, smul_smul]

theorem exists_ext (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x)
    (hspan : Submodule.span E (e.range : Set V) = ⊤) (f : Λ →ₗ[𝓞 E] Λ) :
    ∃ Φ : V →ₗ[E] V, ∀ x, Φ (e x) = e (f x) := by
  obtain ⟨I, b, xs, hb⟩ := exists_basis e hspan
  refine ⟨b.constr E fun i => e (f (xs i)), fun x => ?_⟩
  obtain ⟨d, s, a, hd, hx⟩ := exists_clear e he hs b xs hb x
  have hdE : (d : E) ≠ 0 := by simpa using hd
  have h1 : (d : E) • (b.constr E fun i => e (f (xs i))) (e x) = (d : E) • e (f x) := by
    rw [← map_smul, ← hs, ← hs, ← map_smul, hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hs, map_smul, ← hb, Module.Basis.constr_basis]
  exact smul_right_injective _ hdE h1

theorem exists_extEquiv (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x)
    (hspan : Submodule.span E (e.range : Set V) = ⊤) (φ : Λ ≃ₗ[𝓞 E] Λ) :
    ∃ Φ : V ≃ₗ[E] V, ∀ x, Φ (e x) = e (φ x) := by
  obtain ⟨Φ₁, h₁⟩ := exists_ext e he hs hspan (φ : Λ →ₗ[𝓞 E] Λ)
  obtain ⟨Φ₂, h₂⟩ := exists_ext e he hs hspan (φ.symm : Λ →ₗ[𝓞 E] Λ)
  refine ⟨LinearEquiv.ofLinear Φ₁ Φ₂ ?_ ?_, fun x => h₁ x⟩
  · refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [h₁, h₂]
  · refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [h₁, h₂]

theorem exists_lat (e : Λ →+ V) (he : Function.Injective e)
    (hs : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) (γ : V ≃ₗ[E] V)
    (h₁ : ∀ x, ∃ y, e y = γ (e x)) (h₂ : ∀ x, ∃ y, e y = γ.symm (e x)) :
    ∃ φ : Λ ≃ₗ[𝓞 E] Λ, ∀ x, e (φ x) = γ (e x) := by
  choose f hf using h₁
  choose k hk using h₂
  refine ⟨{ toFun := f, invFun := k, map_add' := fun x y => he ?_, map_smul' := fun a x => he ?_,
            left_inv := fun x => he ?_, right_inv := fun x => he ?_ }, hf⟩
  · simp [hf]
  · simp [hf, hs]
  · simp [hf, hk]
  · simp [hf, hk]

theorem eq_zero_of_trace {xi u : E} (hxi : xi ≠ 0)
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (xi * ((a : E) * u)) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨z, hz⟩ := Algebra.trace_surjective ℚ E 1
  have halg : IsAlgebraic ℤ (z / (xi * u)) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 := h (IsIntegralClosure.mk' (𝓞 E) _ hint)
  rw [show ((IsIntegralClosure.mk' (𝓞 E) _ hint : 𝓞 E) : E) = _ from
    IsIntegralClosure.algebraMap_mk' (𝓞 E) _ hint] at h1
  have h2 : xi * (m • (z / (xi * u)) * u) = (m : ℚ) • z := by
    rw [zsmul_eq_mul, Algebra.smul_def]
    simp only [eq_intCast, map_intCast]
    field_simp
  rw [h2, map_smul, hz] at h1
  simp at h1
  exact hm h1

end Ext

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ}
  {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ}

theorem xi_ne_zero (C : LatEmb F) : C.xi ≠ 0 := by
  have hΨ : ∃ τ : Ψ, True := by
    by_contra hn
    have hn' : ∀ τ : Ψ, False := fun τ => hn ⟨τ, trivial⟩
    let s : 𝓞 E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding.comp (algebraMap (𝓞 E) E)
    have h := (F.cm.2 s).2 (fun ⟨τ, _⟩ => hn' τ)
    exact hn' h.choose
  obtain ⟨τ, -⟩ := hΨ
  intro h0
  have h1 := C.xi_eq τ
  rw [h0, map_zero] at h1
  have he : C.eps τ ≠ 0 := by
    intro h
    have := C.eps_sq τ
    rw [h] at this
    norm_num at this
  have hc : C.c * C.eps τ ≠ 0 := mul_ne_zero C.c_pos.ne' he
  have : ((C.c * C.eps τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  exact (mul_ne_zero Complex.I_ne_zero this) h1.symm

theorem sesq_eq (C : LatEmb F) (φ : autGrp (E := E) F.form) (x y : Λ) :
    C.h.toSesq (C.e (φ.1 y)) (C.e (φ.1 x)) = C.h.toSesq (C.e y) (C.e x) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_trace (xi_ne_zero C) fun a => ?_
  have h1 := C.form_eq (a • φ.1 x) (φ.1 y)
  have h2 := C.form_eq (a • x) y
  have h3 : F.form (a • φ.1 x) (φ.1 y) = F.form (a • x) y := by
    rw [← map_smul]
    exact φ.2 _ _
  rw [h3, h2, C.e_smul, C.e_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  rw [mul_sub, mul_sub, map_sub, sub_eq_zero]
  exact h1.symm

theorem ext_unitary (C : LatEmb F) (φ : autGrp (E := E) F.form)
    (Φ : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (hΦ : ∀ x, Φ (C.e x) = C.e (φ.1 x)) :
    Φ ∈ C.h.unitaryGroup := by
  obtain ⟨I, b, xs, hb⟩ := exists_basis C.e C.integral.isLattice.span_eq_top
  intro v w
  have key : (C.h.toSesq.comp (Φ : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E))).compl₂
      (Φ : (Fin (j + j') → E) →ₗ[E] (Fin (j + j') → E)) = C.h.toSesq := by
    refine LinearMap.ext_basis b b fun p q => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hb, hΦ]
    exact sesq_eq C φ _ _
  exact LinearMap.congr_fun₂ key v w

open scoped Pointwise in
theorem stab_apply_mem (C : LatEmb F) (γ : latticeStab C.h C.e.range) (x : Λ) :
    ∃ y, C.e y = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  have hs : (γ : C.h.unitaryGroup) • C.e.range = C.e.range := MulAction.mem_stabilizer_iff.1 γ.2
  have h1 : (γ : C.h.unitaryGroup) • C.e x ∈ (γ : C.h.unitaryGroup) • C.e.range :=
    AddSubgroup.smul_mem_pointwise_smul _ _ _ ⟨x, rfl⟩
  rw [hs] at h1
  exact h1

theorem exists_of_stab (C : LatEmb F) (γ : latticeStab C.h C.e.range) :
    ∃ φ : autGrp (E := E) F.form, ∀ x, C.e (φ.1 x) =
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  obtain ⟨φ, hφ⟩ := exists_lat C.e C.e_inj C.e_smul
    ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E))
    (stab_apply_mem C γ) (stab_apply_mem C γ⁻¹)
  refine ⟨⟨φ, fun x y => ?_⟩, hφ⟩
  have hu := (γ : C.h.unitaryGroup).2 (C.e y) (C.e x)
  apply Int.cast_injective (α := ℚ)
  rw [C.form_eq, C.form_eq, hφ, hφ]
  exact congrArg (fun t => Algebra.trace ℚ E (C.xi * t)) hu


open scoped Pointwise in
theorem exists_of_aut (C : LatEmb F) (φ : autGrp (E := E) F.form) :
    ∃ γ : latticeStab C.h C.e.range, ∀ x,
      ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) = C.e (φ.1 x) := by
  obtain ⟨Φ, hΦ⟩ := exists_extEquiv C.e C.e_inj C.e_smul C.integral.isLattice.span_eq_top φ.1
  have hU := ext_unitary C φ Φ hΦ
  refine ⟨⟨⟨Φ, hU⟩, ?_⟩, hΦ⟩
  refine MulAction.mem_stabilizer_iff.2 ?_
  ext v
  change v ∈ Φ • C.e.range ↔ _
  rw [AddSubgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨φ.1 x, (hΦ x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨C.e (φ.1.symm y), ⟨_, rfl⟩, ?_⟩
    change Φ (C.e (φ.1.symm y)) = _
    rw [hΦ, LinearEquiv.apply_symm_apply]

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ α : latticeStab C.h C.e.range ≃* autGrp (E := E) F.form, ∀ γ x, C.e ((α γ).1 x) = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  choose A hA using exists_of_stab C
  choose B hB using exists_of_aut C
  have hspan := C.integral.isLattice.span_eq_top
  refine ⟨{ toFun := A, invFun := B, left_inv := fun γ => ?_, right_inv := fun φ => ?_,
            map_mul' := fun a b => ?_ }, hA⟩
  · refine Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
      (LinearMap.ext_on hspan ?_)))
    rintro _ ⟨x, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [hB, hA]
  · exact Subtype.ext (LinearEquiv.ext fun x => C.e_inj (by rw [hA, hB]))
  · refine Subtype.ext (LinearEquiv.ext fun x => C.e_inj ?_)
    change C.e ((A (a * b)).1 x) = C.e ((A a).1 ((A b).1 x))
    rw [hA, hA, hA]
    rfl

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphismsStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_equiv_automorphisms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ α : latticeStab C.h C.e.range ≃* autGrp (E := E) F.form, ∀ γ x, C.e ((α γ).1 x) = ((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.exists_alpha <;> assumption)
end
end
