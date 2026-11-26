module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieMetric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLineDegreeFormula
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLieMetricBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsOrthogonalLieMetric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsOrthogonalLieMetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.MetricOrth

theorem exists_ext (E : Type) [Field E] [NumberField E] (φ : 𝓞 E →+* ℂ) :
    ∃ τ : E →+* ℂ, τ.comp (algebraMap (𝓞 E) E) = φ := by
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro n hn
    have h0 : φ (algebraMap ℤ (𝓞 E) n) = 0 := hn
    have h1 : (n : ℂ) = 0 := by simpa using h0
    have h2 : n = 0 := by exact_mod_cast h1
    simp [h2]
  refine ⟨IsFractionRing.lift hinj, ?_⟩
  ext a
  simp

def resEquiv (E : Type) [Field E] [NumberField E] : (E →+* ℂ) ≃ (𝓞 E →+* ℂ) :=
  Equiv.ofBijective (fun τ => τ.comp (algebraMap (𝓞 E) E))
    ⟨fun τ τ' h => IsFractionRing.injective_comp_algebraMap (A := 𝓞 E) h, fun φ => exists_ext E φ⟩

instance fintypeIntEmb (E : Type) [Field E] [NumberField E] : Fintype (𝓞 E →+* ℂ) := Fintype.ofEquiv _ (resEquiv E)

theorem exists_coeff (E : Type) [Field E] [NumberField E] :
    ∃ (Ix : Type) (_ : Fintype Ix) (α : Ix → 𝓞 E) (d : (𝓞 E →+* ℂ) → Ix → ℂ) (m : Ix → ℤ),
      (∀ τ : 𝓞 E →+* ℂ, ∑ a, d τ a * τ (α a) = 1) ∧
      (∀ σ τ : 𝓞 E →+* ℂ, σ ≠ τ → ∑ a, d τ a * σ (α a) = 0) ∧
      (∀ (τ : 𝓞 E →+* ℂ) a, starRingEnd ℂ (d τ a) = d ((starRingEnd ℂ).comp τ) a) ∧
      (∑ a, m a • α a = 1) ∧ ∀ a, ∑ τ, d τ a = m a := by
  classical
  let Ix := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b := RingOfIntegers.basis E
  let T := 𝓞 E →+* ℂ
  have hcard : Fintype.card Ix = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e₁ : Ix ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let e₂ : Ix ≃ T := (e₁.trans (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm).trans (resEquiv E)
  let N : Matrix Ix Ix ℂ := Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis E) e₁
  have hN : N.det ≠ 0 := by
    intro h
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis E) e₁
    have h2 := Algebra.discr_not_zero_of_basis ℚ (integralBasis E)
    apply h2
    have : algebraMap ℚ ℂ (Algebra.discr ℚ (integralBasis E)) = 0 := by
      rw [h1]; show N.det ^ 2 = 0; rw [h]; simp
    simpa using this
  let A : Matrix T Ix ℂ := Matrix.of fun σ a => σ (b a)
  have hA : A = Nᵀ.submatrix e₂.symm (Equiv.refl Ix) := by
    ext σ a
    obtain ⟨j, rfl⟩ := e₂.surjective σ
    simp only [A, Matrix.of_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.transpose_apply, N,
      Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, Equiv.symm_symm]
    simp [e₂, resEquiv, b, integralBasis_apply]
    rfl
  have hNu : IsUnit Nᵀ.det := by
    rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hN
  let B : Matrix Ix T ℂ := (Nᵀ)⁻¹.submatrix (Equiv.refl Ix) e₂.symm
  have hAB : A * B = 1 := by
    rw [hA, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hNu, Matrix.submatrix_one_equiv]
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e₂.symm).1 hAB
  have hAB' : ∀ σ τ, ∑ a, B a τ * σ (b a) = (1 : Matrix T T ℂ) σ τ := fun σ τ => by
    rw [← hAB, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hBA' : ∀ a c, ∑ τ : T, B a τ * τ (b c) = (1 : Matrix Ix Ix ℂ) a c := fun a c => by
    rw [← hBA, Matrix.mul_apply]
    rfl
  have hcc : ∀ τ : T, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := fun τ => by
    ext x; simp
  let cj : T ≃ T := ⟨fun τ => (starRingEnd ℂ).comp τ, fun τ => (starRingEnd ℂ).comp τ, hcc, hcc⟩
  let B' : Matrix Ix T ℂ := Matrix.of fun a τ => starRingEnd ℂ (B a (cj τ))
  have hAB2 : A * B' = 1 := by
    ext σ τ
    have h1 := congrArg (starRingEnd ℂ) (hAB' (cj σ) (cj τ))
    have h2 : (1 : Matrix T T ℂ) (cj σ) (cj τ) = (1 : Matrix T T ℂ) σ τ := by
      simp [Matrix.one_apply, cj.injective.eq_iff]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    rw [Matrix.mul_apply]
    have h3 : starRingEnd ℂ ((1 : Matrix T T ℂ) σ τ) = (1 : Matrix T T ℂ) σ τ := by
      by_cases h : σ = τ <;> simp [Matrix.one_apply, h]
    rw [h3] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [A, B', Matrix.of_apply, map_mul]
    have : starRingEnd ℂ ((cj σ) (b a)) = σ (b a) := by
      show starRingEnd ℂ (starRingEnd ℂ (σ (b a))) = _
      simp
    rw [this, mul_comm]
  have hB' : B' = B := by
    calc B' = (B * A) * B' := by rw [hBA, Matrix.one_mul]
      _ = B * (A * B') := Matrix.mul_assoc _ _ _
      _ = B := by rw [hAB2, Matrix.mul_one]
  refine ⟨Ix, inferInstance, fun a => b a, fun τ a => B a τ, fun a => b.repr 1 a, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hAB' τ τ]; simp
  · intro σ τ h
    rw [hAB' σ τ]; simp [Matrix.one_apply, h]
  · intro τ a
    have := congrFun (congrFun hB' a) (cj τ)
    simp only [B', Matrix.of_apply] at this
    have h2 : cj (cj τ) = τ := hcc τ
    rw [h2] at this
    exact this
  · exact b.sum_repr 1
  · intro a
    have h1 : ∀ τ : T, (1 : ℂ) = ∑ c, (b.repr 1 c : ℂ) * τ (b c) := fun τ => by
      have := congrArg τ (b.sum_repr 1)
      simpa using this.symm
    calc ∑ τ : T, B a τ = ∑ τ : T, B a τ * ∑ c, (b.repr 1 c : ℂ) * τ (b c) :=
          Finset.sum_congr rfl fun τ _ => by rw [← h1 τ, _root_.mul_one]
      _ = ∑ c, (b.repr 1 c : ℂ) * ∑ τ : T, B a τ * τ (b c) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => by ring
      _ = (b.repr 1 a : ℂ) := by
          simp only [hBA', Matrix.one_apply]
          simp

theorem core_sum {V : Type} [AddCommGroup V] [Module ℂ V] {T : Type} [Fintype T] (core : InnerProductSpace.Core ℂ V)
    (P : T → V →ₗ[ℂ] V) (hP : ∑ τ, P τ = 1) :
    ∃ core' : InnerProductSpace.Core ℂ V, ∀ x y, core'.inner x y = ∑ τ, core.inner (P τ x) (P τ y) := by
  refine ⟨{ inner := fun x y => ∑ τ, core.inner (P τ x) (P τ y)
            conj_inner_symm := ?_
            re_inner_nonneg := ?_
            add_left := ?_
            smul_left := ?_
            definite := ?_ }, fun _ _ => rfl⟩
  · intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    exact Finset.sum_congr rfl fun τ _ => core.conj_inner_symm _ _
  · intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    exact Finset.sum_nonneg fun τ _ => core.re_inner_nonneg _
  · intro x y z
    simp only [map_add (f := _), core.add_left, Finset.sum_add_distrib]
  · intro x y r
    simp only [map_smul, core.smul_left, Finset.mul_sum]
  · intro x hx
    have h1 : ∑ τ, RCLike.re (core.inner (P τ x) (P τ x)) = 0 := by
      have := congrArg RCLike.re hx
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_zero] using this
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => core.re_inner_nonneg (P τ x)).1 h1
    have h3 : ∀ τ, P τ x = 0 := by
      intro τ
      apply core.definite
      have hc := core.conj_inner_symm (P τ x) (P τ x)
      apply Complex.ext
      · simpa using h2 τ (Finset.mem_univ _)
      · have := congrArg Complex.im hc
        simp at this
        simp
        linarith
    have : x = ∑ τ, P τ x := by
      have := congrArg (fun f : V →ₗ[ℂ] V => f x) hP
      simpa [LinearMap.sum_apply] using this.symm
    rw [this]
    exact Finset.sum_eq_zero fun τ _ => h3 τ

theorem core_zero_left {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (y : V) :
    core.inner 0 y = 0 := by
  have h := core.smul_left 0 y 0
  simpa using h

theorem core_zero_right {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (x : V) :
    core.inner x 0 = 0 := by
  rw [← core.conj_inner_symm, core_zero_left, map_zero]

theorem core_sum_left {V : Type} [AddCommGroup V] [Module ℂ V] {Ix : Type} (core : InnerProductSpace.Core ℂ V)
    (s : Finset Ix) (f : Ix → ℂ) (u : Ix → V) (y : V) :
    core.inner (∑ a ∈ s, f a • u a) y = ∑ a ∈ s, starRingEnd ℂ (f a) * core.inner (u a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using core_zero_left core y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, core.smul_left, ih]

theorem core_expand {V : Type} [AddCommGroup V] [Module ℂ V] {Ix : Type} [Fintype Ix]
    (core : InnerProductSpace.Core ℂ V) (f g : Ix → ℂ) (u w : Ix → V) :
    core.inner (∑ a, f a • u a) (∑ b, g b • w b) =
      ∑ a, ∑ b, starRingEnd ℂ (f a) * g b * core.inner (u a) (w b) := by
  rw [core_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← core.conj_inner_symm, core_sum_left, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_conj, core.conj_inner_symm]
  ring

section Geo

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

theorem valAt_act (M : LieModel G ξ Li) {O : Type} [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω Li)
    (hρ : M.IsActOf act.act ρ) (z : Sp ℂ ⟶ X) (r : O) {e : Li} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z (ρ r e) (w ≫ act.act r) := by
  obtain ⟨hs, v, ⟨ht, hv⟩, hw⟩ := h
  haveI := act.hom r
  refine ⟨hs, v ≫ act.act r, ⟨ht.comp_monHom _, ?_⟩, ?_⟩
  · rw [hρ r e, Over.comp_left, hv, Over.comp_left]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, hw, Over.comp_left]
    exact Category.assoc _ _ _

theorem eig_act {V : Type} [AddCommGroup V] [Module ℂ V] {z : Sp ℂ ⟶ X} (Mz : LieModel G z V) {O : Type} [CommRing O]
    (act : OAct O G) (ρz : O →+* Module.End ℂ V) (hρz : Mz.IsActOf act.act ρz) {τ : O →+* ℂ} {x : V}
    (h : IsLieEigen act z τ (Mz.pt x)) (r : O) : ρz r x = τ r • x := by
  apply Mz.inj
  apply Over.OverMorphism.ext
  rw [Mz.smul, hρz r x]
  exact h.2 r

theorem exists_orth (E : Type) [Field E] [NumberField E] [IsCommMonObj G] {K : Type} {J : K → Type}
    {y : (Σ k, J k) → Ω} (M : LieModel G ξ Li) (act : OAct (𝓞 E) G) (ρ : 𝓞 E →+* Module.End Ω Li)
    (hρ : M.IsActOf act.act ρ) (h₀ : LieMetric M y) : ∃ h : LieMetric M y, h.Orth act := by
  obtain ⟨Ix, _, α, d, m, hd1, hd0, hdc, hm1, hm2⟩ := exists_coeff E
  let c : Ix → Ix → ℂ := fun a b => ∑ τ, starRingEnd ℂ (d τ a) * d τ b
  have hcc : ∀ τ : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := fun τ => by
    ext x; simp
  let cj : (𝓞 E →+* ℂ) ≃ (𝓞 E →+* ℂ) := ⟨fun τ => (starRingEnd ℂ).comp τ, fun τ => (starRingEnd ℂ).comp τ, hcc, hcc⟩
  have hc : ∀ a b, starRingEnd ℂ (c a b) = c a b := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c, map_sum, map_mul, Complex.conj_conj]
    refine Fintype.sum_equiv cj _ _ fun τ => ?_
    show d τ a * starRingEnd ℂ (d τ b) = starRingEnd ℂ (d (cj τ) a) * d (cj τ) b
    have h1 : d (cj τ) a = starRingEnd ℂ (d τ a) := (hdc τ a).symm
    have h2 : d (cj τ) b = starRingEnd ℂ (d τ b) := (hdc τ b).symm
    rw [h1, h2, Complex.conj_conj]
  let ip' : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ := fun z v w =>
    ∑ a, ∑ b, c a b * h₀.ip z (v ≫ act.act (α a)) (w ≫ act.act (α b))
  have hsum : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρz : 𝓞 E →+* Module.End ℂ V),
      ∑ τ, ∑ a, d τ a • ρz (α a) = 1 := by
    intro V _ _ ρz
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hm2, Int.cast_smul_eq_zsmul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one ρz, ← hm1, map_sum]
    simp only [map_zsmul]
  have key : ∀ (z : Sp ℂ ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V)
      (ρz : 𝓞 E →+* Module.End ℂ V), Mz.IsActOf act.act ρz → ∀ core : InnerProductSpace.Core ℂ V,
      (∀ a b, core.inner a b = h₀.ip z (Mz.pt a) (Mz.pt b)) → ∀ x x',
      ip' z (Mz.pt x) (Mz.pt x') =
        ∑ τ, core.inner ((∑ a, d τ a • ρz (α a)) x) ((∑ a, d τ a • ρz (α a)) x') := by
    intro z V _ _ Mz ρz hρz core hcore x x'
    have h1 : ∀ τ, core.inner ((∑ a, d τ a • ρz (α a)) x) ((∑ a, d τ a • ρz (α a)) x') =
        ∑ a, ∑ b, starRingEnd ℂ (d τ a) * d τ b * core.inner (ρz (α a) x) (ρz (α b) x') := by
      intro τ
      rw [← core_expand]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hcore, hρz (α a) x, hρz (α b) x', ← Finset.sum_mul]
  refine ⟨{ ip := ip', herm := ?_, conj := ?_, cont := ?_ }, ?_⟩
  · intro z V _ _ Mz
    obtain ⟨ρz, hρz, -⟩ := lieModel_exists_unique_act X G ℂ z V Mz (𝓞 E) act.act act.hom act.one act.mul act.add
    obtain ⟨core, hcore⟩ := h₀.herm z V Mz
    obtain ⟨core', h'⟩ := core_sum core (fun τ => ∑ a, d τ a • ρz (α a)) (hsum ρz)
    exact ⟨core', fun a b => (h' a b).trans (key z V Mz ρz hρz core hcore a b).symm⟩
  · intro z v w v' w' hv hw
    show ip' _ v' w' = starRingEnd ℂ (ip' z v w)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ip', map_sum, map_mul, hc]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    exact h₀.conj z _ _ _ _ (by rw [Over.comp_left, hv, Over.comp_left, Category.assoc])
      (by rw [Over.comp_left, hw, Over.comp_left, Category.assoc])
  · intro a b
    choose F hF1 hF2 using fun i j => h₀.cont (ρ (α i) a) (ρ (α j) b)
    refine ⟨fun w => ∑ i, ∑ j, c i j * F i j w, ?_, ?_⟩
    · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
        continuousOn_const.mul ((hF1 i j).mono ?_)
      rintro w ⟨z, va, vb, hw, ha, hb⟩
      exact ⟨z, va ≫ act.act (α i), vb ≫ act.act (α j), hw, valAt_act M act ρ hρ z _ ha,
        valAt_act M act ρ hρ z _ hb⟩
    · intro z w va vb hw ha hb
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hF2 i j z w _ _ hw (valAt_act M act ρ hρ z _ ha) (valAt_act M act ρ hρ z _ hb)]
  · intro z τ τ' v w hne hv hw
    obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists X G ℂ z
    obtain ⟨ρz, hρz, -⟩ := lieModel_exists_unique_act X G ℂ z V Mz (𝓞 E) act.act act.hom act.one act.mul act.add
    obtain ⟨core, hcore⟩ := h₀.herm z V Mz
    obtain ⟨x, rfl⟩ := Mz.onto v hv.1
    obtain ⟨x', rfl⟩ := Mz.onto w hw.1
    have hP : ∀ (σ υ : 𝓞 E →+* ℂ) (u : V), IsLieEigen act z υ (Mz.pt u) → σ ≠ υ →
        (∑ a, d σ a • ρz (α a)) u = 0 := by
      intro σ υ u hu hne'
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, eig_act Mz act ρz hρz hu, smul_smul]
      rw [← Finset.sum_smul, hd0 υ σ hne'.symm, zero_smul]
    show ip' z _ _ = 0
    rw [key z V Mz ρz hρz core hcore x x']
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases hσ : σ = τ
    · rw [hP σ τ' x' hw (hσ ▸ hne), core_zero_right]
    · rw [hP σ τ x hv hσ, core_zero_left]

end Geo

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ h : LieMetric 𝔐.M y, h.Orth 𝔐.t.act := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hch : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  obtain ⟨h₀⟩ := GlobalTheory.T.exists_lie_metric 𝔐.X Ω K J y 𝔐.ξ hch 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.Li 𝔐.M
  exact exists_orth E 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act h₀

end GlobalTheory.CompanionTheory.Ar.MetricOrth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsOrthogonalLieMetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_lie_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ h : LieMetric 𝔐.M y, h.Orth 𝔐.t.act := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MetricOrth.main | exact GlobalTheory.CompanionTheory.Ar.MetricOrth.main | (intros; apply GlobalTheory.CompanionTheory.Ar.MetricOrth.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHermitianBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHermitianBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFibre

open GroundTheory.Heights₂.Heights NumberField.ComplexEmbedding

@[instance_reducible]
def coreOfEquiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (c : InnerProductSpace.Core ℂ W) (Φ : V ≃ₗ[ℂ] W) : InnerProductSpace.Core ℂ V where
  inner x y := c.inner (Φ x) (Φ y)
  conj_inner_symm x y := c.conj_inner_symm (Φ x) (Φ y)
  re_inner_nonneg x := c.re_inner_nonneg (Φ x)
  add_left x y z := by simp only [map_add (f := _)]; exact c.add_left _ _ _
  smul_left x y r := by simp only [map_smul]; exact c.smul_left _ _ _
  definite x hx := Φ.injective (by rw [map_zero]; exact c.definite _ hx)

theorem core_add_right {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (x y z : V) :
    c.inner x (y + z) = c.inner x y + c.inner x z := by
  rw [← c.conj_inner_symm x (y + z), c.add_left, map_add (f := _), c.conj_inner_symm, c.conj_inner_symm]

theorem core_smul_right {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (x y : V) (r : ℂ) :
    c.inner x (r • y) = r * c.inner x y := by
  rw [← c.conj_inner_symm x (r • y), c.smul_left, map_mul, c.conj_inner_symm]
  simp

theorem core_zero_left {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (y : V) :
    c.inner 0 y = 0 := by
  have := c.add_left 0 0 y
  simpa using this

theorem core_zero_right {V : Type} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V) (x : V) :
    c.inner x 0 = 0 := by
  rw [← c.conj_inner_symm x 0, core_zero_left, map_zero]

theorem pure_smul {L : Type} [Field L] {E : Type} [AddCommGroup E] [Module (𝓞 L) E] (σ : L →+* ℂ)
    (a : ComplexAt σ) (e : E) :
    a ⊗ₜ[𝓞 L] e = ((ComplexAt.ofComplex σ).symm a : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
  rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def, _root_.mul_one]
  simp

theorem spMap_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  apply RingHom.ext
  intro a
  apply TrivSqZeroExt.ext <;> simp [dualMap]

theorem exists_fibreLift {L : Type} [Field L] {E : Type} [AddCommGroup E] [Module (𝓞 L) E] (σ : L →+* ℂ)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (j : E →ₛₗ[σ.comp (algebraMap (𝓞 L) L)] Q) :
    ∃ f : Fibre σ E →ₗ[ℂ] Q, ∀ e, f ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = j e := by
  letI : Module (𝓞 L) Q := Module.compHom Q (σ.comp (algebraMap (𝓞 L) L))
  let B : ComplexAt σ →ₗ[𝓞 L] E →ₗ[𝓞 L] Q := LinearMap.mk₂ (𝓞 L)
    (fun a e => ((ComplexAt.ofComplex σ).symm a : ℂ) • j e)
    (fun a b e => by rw [map_add (f := _), add_smul])
    (fun r a e => by
      change ((ComplexAt.ofComplex σ).symm (r • a) : ℂ) • j e = (σ (r : L) : ℂ) • _
      rw [ComplexAt.smul_def, map_mul, mul_smul]
      simp)
    (fun a e e' => by rw [map_add (f := _), smul_add])
    (fun r a e => by
      have hr : j (r • e) = (σ (r : L) : ℂ) • j e := j.map_smulₛₗ r e
      change ((ComplexAt.ofComplex σ).symm a : ℂ) • j (r • e) =
        (σ (r : L) : ℂ) • (((ComplexAt.ofComplex σ).symm a : ℂ) • j e)
      rw [hr, smul_comm])
  refine ⟨{ toFun := TensorProduct.lift B, map_add' := map_add _, map_smul' := ?_ }, fun e => ?_⟩
  · intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      change ((ComplexAt.ofComplex σ).symm (c • a) : ℂ) • j e = c • ((ComplexAt.ofComplex σ).symm a : ℂ) • j e
      rw [ComplexAt.complex_smul_def, map_mul, mul_smul]
      simp
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  · change TensorProduct.lift B _ = _
    rw [TensorProduct.lift.tmul]
    change ((ComplexAt.ofComplex σ).symm 1 : ℂ) • j e = j e
    simp

def oneTmul {L : Type} [Field L] (E : Type) [AddCommGroup E] [Module (𝓞 L) E] (σ : L →+* ℂ) :
    E →ₛₗ[σ.comp (algebraMap (𝓞 L) L)] Fibre σ E where
  toFun e := (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e
  map_add' := TensorProduct.tmul_add _
  map_smul' a e := by
    rw [← TensorProduct.smul_tmul, pure_smul]
    simp [ComplexAt.smul_def]

section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem lifts_unique {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ X} {E : Type} [AddCommGroup E] [Module R E]
    (MB : LieModel G x E) (c : R →+* R') {x' : Sp R' ⟶ X} {e : E} {v v' : epsAt x' ⟶ G}
    (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (MB.pt e).left)) (h' : (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (MB.pt e).left)) : v = v' := by
  rw [Category.comp_id] at h h'
  exact Over.OverMorphism.ext (h.trans h'.symm)

theorem lie_universal [IsCommMonObj G] [Smooth G.hom] {R C : Type} [CommRing R] [CommRing C] (c : R →+* C) {x : Sp R ⟶ X}
    {E : Type} [AddCommGroup E] [Module R E] {V : Type} [AddCommGroup V] [Module C V]
    (MB : LieModel G x E) (Mz : LieModel G (spMap c ≫ x) V) (j : E →ₛₗ[c] V)
    (hj : ∀ e, ((Mz.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (MB.pt e).left))
    {Q : Type} [AddCommGroup Q] [Module C Q] (g : E →ₛₗ[c] Q) :
    ∃ g' : V →ₗ[C] Q, (∀ e, g' (j e) = g e) ∧ ∀ g₂ : V →ₗ[C] Q, (∀ e, g₂ (j e) = g e) → g₂ = g' := by
  letI : Algebra R C := c.toAlgebra
  letI : Module R V := Module.compHom V c
  letI : Module R Q := Module.compHom Q c
  haveI : IsScalarTower R C V := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    exact mul_smul _ _ _⟩
  haveI : IsScalarTower R C Q := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    exact mul_smul _ _ _⟩
  let j' : E →ₗ[R] V :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a e => j.map_smulₛₗ a e }
  let g₀ : E →ₗ[R] Q :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun a e => g.map_smulₛₗ a e }
  have hb : IsBaseChange C j' := GlobalTheory.T.lie_model_isBaseChange X G R C x E V MB Mz j' hj
  exact ⟨hb.lift g₀, fun e => hb.lift_eq g₀ e, fun g₂ h2 =>
    hb.algHom_ext' _ _ (LinearMap.ext fun e => (h2 e).trans (hb.lift_eq g₀ e).symm)⟩
end

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X}
  {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  {M : LieModel G ξ Li} {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ X}
  {E : Type} [AddCommGroup E] [Module (𝓞 L) E]

theorem exists_fibreEquiv (MB : LieModel G z E) (σ : L →+* ℂ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (Mz : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) V)
      (Φ : Fibre σ E ≃ₗ[ℂ] V),
      ∀ e, ((Mz.pt (Φ ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e))).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left) := by
  obtain ⟨V, iA, iM, ⟨Mz⟩⟩ := lieModel_exists X G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts X G (𝓞 L) ℂ (σ.comp (algebraMap (𝓞 L) L)) z E V MB Mz
  obtain ⟨f, hf⟩ := exists_fibreLift σ j
  obtain ⟨g, hg, -⟩ := lie_universal _ MB Mz j hj (oneTmul E σ)
  obtain ⟨i, -, hi⟩ := lie_universal _ MB Mz j hj j
  have hfg : f ∘ₗ g = LinearMap.id := by
    rw [hi (f ∘ₗ g) (fun e => ?_), hi LinearMap.id (fun e => rfl)]
    change f (g (j e)) = j e
    rw [hg]; exact hf e
  have hgf : g ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [pure_smul, map_smul, map_smul]
      change _ • g (f _) = _
      rw [hf, hg]
      rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine ⟨V, iA, iM, Mz, LinearEquiv.ofLinear f g hfg hgf, fun e => ?_⟩
  change MB.Lifts _ _ e (Mz.pt (f _))
  rw [hf]
  exact hj e

theorem exists_core (h : LieMetric M y) (MB : LieModel G z E) (σ : L →+* ℂ) :
    ∃ (core : InnerProductSpace.Core ℂ (Fibre σ E))
      (P : Fibre σ E → (epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G)),
      (∀ a b, core.inner a b = h.ip _ (P a) (P b)) ∧
        ∀ e, ((P ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left) := by
  obtain ⟨V, iA, iM, Mz, Φ, hΦ⟩ := exists_fibreEquiv MB σ
  obtain ⟨core, hcore⟩ := h.herm _ V Mz
  exact ⟨coreOfEquiv core Φ, fun a => Mz.pt (Φ a), fun a b => hcore _ _, hΦ⟩

theorem ip_conj (h : LieMetric M y) (MB : LieModel G z E) (σ : L →+* ℂ) (e f : E)
    {v w : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G}
    {v' w' : epsAt (spMap ((NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G}
    (hv : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left))
    (hw : (w.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt f).left))
    (hv' : (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L))) ≫ (MB.pt e).left))
    (hw' : (w'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L))) ≫ (MB.pt f).left)) :
    h.ip _ v' w' = starRingEnd ℂ (h.ip _ v w) := by
  have key : ∀ (z₁ z₂ : Sp ℂ ⟶ X) (_ : z₂ = spMap (starRingEnd ℂ) ≫ z₁) (v w : epsAt z₁ ⟶ G) (v' w' : epsAt z₂ ⟶ G),
      v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left →
      h.ip z₂ v' w' = starRingEnd ℂ (h.ip z₁ v w) := by
    intro z₁ z₂ hz v w v' w' h1 h2
    subst hz
    exact h.conj z₁ v w v' w' h1 h2
  have hc : (NumberField.ComplexEmbedding.conjugate σ).comp (algebraMap (𝓞 L) L) =
      (starRingEnd ℂ).comp (σ.comp (algebraMap (𝓞 L) L)) := by
    ext a; rfl
  have hdm : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B),
      GlobalTheory.CompanionTheory.Ar.dualMap f = dualMap f := fun f => by
    apply RingHom.ext; intro a; apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, dualMap]
  rw [Category.comp_id, hdm] at hv hw hv' hw'
  refine key _ _ ?_ v w v' w' ?_ ?_
  · rw [← Category.assoc, spMap_spMap', hc]
  · rw [hv, hv', hc, dualMap_comp', ← Category.assoc, spMap_spMap']
  · rw [hw, hw', hc, dualMap_comp', ← Category.assoc, spMap_spMap']

theorem form_conj_of_pure (core : ∀ σ : L →+* ℂ, InnerProductSpace.Core ℂ (Fibre σ E))
    (h : ∀ (σ : L →+* ℂ) (e f : E),
      (core (NumberField.ComplexEmbedding.conjugate σ)).inner
        ((1 : ComplexAt (NumberField.ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e)
        ((1 : ComplexAt (NumberField.ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] f) =
      starRingEnd ℂ ((core σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f)))
    (σ : L →+* ℂ) (x y : Fibre σ E) :
    (core (NumberField.ComplexEmbedding.conjugate σ)).inner (conjMap σ E x) (conjMap σ E y) =
      starRingEnd ℂ ((core σ).inner x y) := by
  have h1 : ∀ e : E, conjMap σ E ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) =
      (1 : ComplexAt (NumberField.ComplexEmbedding.conjugate σ)) ⊗ₜ[𝓞 L] e := fun e => by
    rw [conjMap_tmul, map_one]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, core_zero_left]
  | add x x' hx hx' => simp only [map_add (f := _), (core _).add_left, hx, hx']
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, core_zero_right]
    | add y y' hy hy' => simp only [map_add (f := _), core_add_right, hy, hy']
    | tmul b f =>
      rw [pure_smul σ a e, pure_smul σ b f, conjMap_smul, conjMap_smul, h1, h1, (core _).smul_left, core_smul_right,
        (core _).smul_left, core_smul_right, h]
      simp only [map_mul, Complex.conj_conj]

end

end GlobalTheory.CompanionTheory.Ar.LieFibre


open GlobalTheory.CompanionTheory.Ar.LieFibre GroundTheory.Heights₂.Heights in
theorem GlobalTheory.CompanionTheory.Ar.lie_fibre_exists : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X), ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB := by
  intro X Ω _ K _ J _ y ξ G _ _ _ Li _ _ M h L _ _ z
  obtain ⟨E, iA, iM, ⟨MB⟩⟩ := lieModel_exists X G (𝓞 L) z
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G (𝓞 L) z E MB
  choose core P hcore hlift using fun σ : L →+* ℂ => exists_core h MB σ
  have hconj := form_conj_of_pure core (fun σ e f => by
    rw [hcore, hcore]
    exact ip_conj h MB σ e f (hlift σ e) (hlift σ f) (hlift _ e) (hlift _ f))
  refine ⟨@HermitianBundle.mk L _ _ E iA iM hf hp ⟨core, hconj⟩, MB, ?_⟩
  intro σ x x' v v' hv hv'
  change (core σ).inner _ _ = _
  rw [hcore, lifts_unique MB _ (hlift σ x) hv, lifts_unique MB _ (hlift σ x') hv']
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHermitianBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_metric_hermitian_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X), ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lie_fibre_exists | exact GlobalTheory.CompanionTheory.Ar.lie_fibre_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.lie_fibre_exists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagHeight
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopFibre

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

theorem centre_comp_specializes (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom ψ) ≫ z) ⤳ centre z := by
  have h := (IsLocalRing.specializes_closedPoint
    (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint R'))).map z.continuous
  exact h


set_option backward.isDefEq.respectTransparency false in
theorem stalkSpecializes_comp_stalkClosedPointTo (ψ : R →+* R') (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_comp_specializes ψ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom ψ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (Spec.map (CommRingCat.ofHom ψ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_comp {ξ : Spec (CommRingCat.of Ω) ⟶ X} (ψ : R →+* R') {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R}
    (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom ψ) ≫ z)) :
    ValAt ξ (Spec.map (CommRingCat.ofHom ψ) ≫ z) a (ψ r) := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_comp_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_comp_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalkSpecializes_comp_stalkClosedPointTo ψ z)

theorem coordsAt_comp {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q) {K : Type} {J : K → Type}
    {y : (Σ k, J k) → Ω} {L L' : Type} [Field L] [Field L'] (ψ : L →+* L') {z : Spec (CommRingCat.of L) ⟶ X}
    {w : (Σ k, J k) → L} (h : CoordsAt ξ y z w) :
    CoordsAt ξ y (Spec.map (CommRingCat.ofHom ψ) ≫ z) fun p => ψ (w p) := by
  refine ⟨fun k => (h.1 k).imp fun c hc => hc.map ψ, fun k c hc => ?_⟩
  have hc' : IsUnit (w ⟨k, c⟩) := by
    rw [isUnit_iff_ne_zero] at hc ⊢
    exact fun h0 => hc (by simp [h0])
  refine ⟨(h.2 k c hc').1, fun i => ?_⟩
  obtain ⟨r, hr, e⟩ := (h.2 k c hc').2 i
  exact ⟨ψ r, valAt_comp ψ hr (hall _), by simp only [e, map_mul]⟩

end Values

theorem logBound_mono {C C' t : ℝ} (h0 : 0 ≤ C) (h : C ≤ C') (ht : 0 ≤ t) :
    C * Real.log (2 + C + t) + C ≤ C' * Real.log (2 + C' + t) + C' := by
  have h1 : 0 ≤ Real.log (2 + C + t) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 + C + t) ≤ Real.log (2 + C' + t) := Real.log_le_log (by linarith) (by linarith)
  have h3 := mul_le_mul h h2 h1 (h0.trans h)
  linarith

theorem fibreInput : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S R.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → R.Ω), 1 ≤ D.p + D.q → Fl.RootLines R.xdeg e → Ht.FibreInput R := by
  intro h1 h2 h3 h4 h5 E _ _ _ H D l Xo c Y S _ R 𝔐 Fl e hpq hroot
  obtain ⟨h, horth⟩ := GlobalTheory.T.exists_orthogonal_lie_metric E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐
  obtain ⟨C₁, hC₁, hslope⟩ := GlobalTheory.T.hodge_cpt_lie_metric_bound h1 h2 h3 h4 h5 E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 h hpq
  have hdeg : (fun r => (R.x 1 r).a) = R.xdeg := funext fun r => R.x_deg 1 r
  obtain ⟨C₂, hht⟩ := GlobalTheory.T.flag_line_degree_formula E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 Fl h (R.x 1) e (R.x_smooth 1)
    (hdeg.symm ▸ hroot)
  have hch : CharZero R.Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), fun L _ _ w hw => ?_⟩
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.number_field_point_integral_model 𝔐.X R.Ω R.K R.ι R.y 𝔐.ξ hch 𝔐.all 𝔐.tie L w hw
  obtain ⟨L', _, _, ε, hs⟩ := hslope L z₀
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨B, MB, hB⟩ := GlobalTheory.T.lie_metric_hermitian_bundle 𝔐.X R.Ω R.K R.ι R.y 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M h L'
    (spMap (RingOfIntegers.mapRingHom ε) ≫ z₀)
  obtain ⟨A, hA, hW⟩ := GlobalTheory.T.orthogonal_metric_flag_degree E H D l Xo c Y S R.Ω R.K R.ι R.y 𝔐 Fl h horth L' _ B MB hB
  have hpt : spMap (algebraMap (𝓞 L') L') ≫ spMap (RingOfIntegers.mapRingHom ε) ≫ z₀ =
      spMap ε ≫ spMap (algebraMap (𝓞 L) L) ≫ z₀ := by
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hz : CoordsAt 𝔐.ξ R.y (spMap (algebraMap (𝓞 L') L') ≫ spMap (RingOfIntegers.mapRingHom ε) ≫ z₀)
      fun p => ε (w p) := by
    rw [hpt]
    exact coordsAt_comp 𝔐.all ε hz₀
  have hext : ∀ r, Ht.lineHt (R.x 1 r) L' (fun p => ε (w p)) = Ht.lineHt (R.x 1 r) L w := fun r => by
    simpa using GlobalTheory.T.line_height_invariant_scaling R.K R.ι (R.x 1 r) L L' ε w (fun _ => 1) hw.1 fun _ => one_ne_zero
  obtain ⟨ha, hb⟩ := hht L' _ _ hz B MB A hB hW
  refine ⟨L', inferInstance, inferInstance, ε, B, A, hA, fun τ i => ?_, fun τ i => ?_, ?_⟩
  · rw [← hext]
    exact (ha τ i).trans (le_max_right _ _)
  · rw [← hext]
    exact (hb τ i).trans (le_max_right _ _)
  · exact (hs B MB hB).trans
      (EReal.coe_le_coe_iff.2 (logBound_mono hC₁ (le_max_left _ _) (le_max_right _ _)))

end GlobalTheory.CompanionTheory.Ar.TopFibre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagHeightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_flag_height : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S R.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → R.Ω), 1 ≤ D.p + D.q → Fl.RootLines R.xdeg e → Ht.FibreInput R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput | exact GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput | (intros; apply GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput <;> assumption)
end
