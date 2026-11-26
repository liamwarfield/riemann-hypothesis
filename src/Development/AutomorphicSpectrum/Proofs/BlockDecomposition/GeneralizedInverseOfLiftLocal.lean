module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem form_mem_of_mem_smul_top {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (J : Ideal A) (φ : N →ₗ[A] A) {n : N} (h : n ∈ J • (⊤ : Submodule A N)) : φ n ∈ J := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intro r hr n _
    rw [map_smul, smul_eq_mul]
    exact J.mul_mem_right _ hr
  · intro x y hx hy
    rw [map_add (f := _)]
    exact J.add_mem hx hy

theorem exists_step_of_sup_span {A : Type} [CommRing A] (K I : Ideal A) (S : Finset A)
    (hS : K ⊔ Ideal.span (S : Set A) = I) (hne : K ≠ I) :
    ∃ (J : Ideal A) (t : A), K ≤ J ∧ J ≠ I ∧ J ⊔ Ideal.span {t} = I := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact absurd (by simpa using hS) hne
  | insert a S' _ ih =>
    by_cases h : K ⊔ Ideal.span (S' : Set A) = I
    · exact ih h
    · refine ⟨K ⊔ Ideal.span (S' : Set A), a, le_sup_left, h, ?_⟩
      rw [← hS, Finset.coe_insert, Ideal.span_insert, sup_assoc, sup_comm (Ideal.span {a})]

theorem eq_zero_of_lift_of_mem_maximalIdeal_smul (A Q N : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N) (hL : Lift b)
    (hb : ∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) : b = 0 := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A Q).FG)
  let v := Module.finBasis A N
  let g : Fin (Module.finrank A N) × S → A := fun p ↦ v.coord p.1 (b p.2)
  let I : Ideal A := Ideal.span (Set.range g)
  have hIfg : I.FG := ⟨(Set.finite_range g).toFinset, by simp [I]⟩

  have hcoord : ∀ q i, v.coord i (b q) ∈ I := by
    intro q
    have hq : q ∈ Submodule.span A (S : Set Q) := by rw [hS]; trivial
    induction hq using Submodule.span_induction with
    | mem x hx =>
      intro i
      exact Ideal.subset_span ⟨(i, ⟨x, hx⟩), rfl⟩
    | zero => intro i; simp
    | add x y _ _ hx hy =>
      intro i
      rw [map_add (f := _), map_add (f := _)]
      exact I.add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      rw [map_smul, map_smul, smul_eq_mul]
      exact I.mul_mem_left _ (hx i)

  have hval : ∀ q, b q ∈ I • (⊤ : Submodule A N) := by
    intro q
    rw [← v.sum_repr (b q)]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hcoord q i) trivial
  have hIm : I ≤ IsLocalRing.maximalIdeal A := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hb p.2)
  have hI : I = ⊥ := by
    by_contra hI
    set m := IsLocalRing.maximalIdeal A with hm
    have hjac : m ≤ Ideal.jacobson (⊥ : Ideal A) := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have hne : m * I ≠ I := by
      intro h
      exact hI (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m I hIfg
        (by rw [smul_eq_mul, h]) hjac)
    obtain ⟨T, hT⟩ := hIfg
    have hsup : m * I ⊔ Ideal.span (T : Set A) = I := by
      have hT' : Ideal.span (T : Set A) = I := hT
      rw [hT']
      exact sup_eq_right.2 (Ideal.mul_le_right : m * I ≤ I)
    obtain ⟨J, t, hKJ, hJI, hJt⟩ := exists_step_of_sup_span (m * I) I T hsup hne
    have hJle : J ≤ I := hJt ▸ le_sup_left
    have htI : t ∈ I := by
      rw [← hJt]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)
    have hJtop : J ≠ ⊤ := fun h ↦ by
      have : (1 : A) ∈ m := hIm (hJle (h ▸ Submodule.mem_top))
      exact (Ideal.ne_top_iff_one m).1 (IsLocalRing.maximalIdeal.isMaximal A).ne_top this
    have hxt : ∀ x ∈ IsLocalRing.maximalIdeal A, x * t ∈ J :=
      fun x hx ↦ hKJ (Ideal.mul_mem_mul hx htI)

    have hstep : ∀ y ∈ I • (⊤ : Submodule A Q), b y ∈ J • (⊤ : Submodule A N) := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr q _
        rw [map_smul]
        have h1 : r • b q ∈ I • m • (⊤ : Submodule A N) :=
          Submodule.smul_mem_smul hr (hb q)
        have h2 : I • m • (⊤ : Submodule A N) ≤ J • (⊤ : Submodule A N) := by
          rw [← Submodule.mul_smul, mul_comm]
          exact Submodule.smul_mono_left hKJ
        exact h2 h1
      · intro x y hx hy
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hy
    have hzJ : ∀ z, b z ∈ J • (⊤ : Submodule A N) := by
      intro z
      obtain ⟨x, hx, hxz⟩ := hL J t hJtop hxt z (by rw [hJt]; exact hval z)
      rw [hJt] at hxz
      have h := Submodule.sub_mem _ hx (hstep _ hxz)
      rwa [← map_sub, sub_sub_cancel] at h
    apply hJI
    refine le_antisymm hJle (Ideal.span_le.2 ?_)
    rintro _ ⟨p, rfl⟩
    exact form_mem_of_mem_smul_top _ _ (hzJ p.2)
  ext q
  apply v.repr.injective
  ext i
  have := hcoord q i
  rw [hI, Ideal.mem_bot] at this
  simpa using this

end GlobalTheory.CompanionTheory.PerfVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximalStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_reduction_zero_of_maximal : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → (∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) → b = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul | exact GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul | (intros; apply GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocal
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.GenInv

variable {A : Type} [CommRing A] {M M' : Type} [AddCommGroup M] [Module A M]
  [AddCommGroup M'] [Module A M']

noncomputable def proj (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) : M →ₗ[A] LinearMap.ker σ :=
  LinearMap.codRestrict _ (LinearMap.id - σ.smulRight v) (fun x => by
    simp [LinearMap.mem_ker, h])

theorem proj_coe (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : M) :
    (proj σ v h x : M) = x - σ x • v := rfl

theorem proj_ker (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) (x : LinearMap.ker σ) :
    proj σ v h x = x :=
  Subtype.ext (by simp [proj_coe, LinearMap.mem_ker.1 x.2])

theorem apply_mem_smul_top (f : M →ₗ[A] M') (I : Ideal A) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : f x ∈ I • (⊤ : Submodule A M') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem ker_finite [Module.Finite A M] (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    Module.Finite A (LinearMap.ker σ) :=
  Module.Finite.of_surjective (proj σ v h) (fun x => ⟨x, proj_ker σ v h x⟩)

theorem ker_free [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.Free A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI : Module.Projective A (LinearMap.ker σ) :=
    Module.Projective.of_split (LinearMap.ker σ).subtype (proj σ v h)
      (LinearMap.ext fun x => proj_ker σ v h x)
  haveI : Module.FinitePresentation A (LinearMap.ker σ) :=
    Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

noncomputable def kerEquiv (σ : M →ₗ[A] A) (v : M) (h : σ v = 1) :
    M ≃ₗ[A] A × LinearMap.ker σ :=
  LinearEquiv.ofLinear (σ.prod (proj σ v h))
    (LinearMap.coprod (LinearMap.toSpanSingleton A M v) (LinearMap.ker σ).subtype)
    (by
      ext x
      · simp [h]
      · simp [proj_coe, h]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [proj_coe, LinearMap.mem_ker.1 x.2])
    (by
      ext x
      simp [proj_coe])

theorem finrank_ker [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (σ : M →ₗ[A] A) (v : M)
    (h : σ v = 1) : Module.finrank A M = 1 + Module.finrank A (LinearMap.ker σ) := by
  haveI := ker_finite σ v h
  haveI := ker_free σ v h
  rw [(kerEquiv σ v h).finrank_eq, Module.finrank_prod, Module.finrank_self]

theorem exists_form [IsLocalRing A] [Module.Finite A M] [Module.Free A M] (y : M)
    (hy : y ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
    ∃ σ : M →ₗ[A] A, σ y = 1 := by
  classical
  let e := Module.Free.chooseBasis A M
  by_cases h : ∀ i, e.repr y i ∈ IsLocalRing.maximalIdeal A
  · refine absurd ?_ hy
    rw [← e.sum_repr y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have hu : IsUnit (e.repr y i) := by
      by_contra hn
      exact hi ((IsLocalRing.mem_maximalIdeal _).2 hn)
    obtain ⟨u, hu⟩ := hu
    refine ⟨((↑u⁻¹ : A)) • e.coord i, ?_⟩
    simp [← hu]

noncomputable def restr (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) :
    LinearMap.ker (σ ∘ₗ b) →ₗ[A] LinearMap.ker σ :=
  b.restrict (fun x hx => by simpa using hx)

theorem restr_coe (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x : LinearMap.ker (σ ∘ₗ b)) :
    (restr b σ x : M') = b x := rfl

theorem restr_proj (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M) (h : σ (b x₀) = 1) (q : M) :
    restr b σ (proj (σ ∘ₗ b) x₀ h q) = proj σ (b x₀) h (b q) :=
  Subtype.ext (by simp [restr_coe, proj_coe])

theorem lift_restr [IsLocalRing A] (b : M →ₗ[A] M') (σ : M' →ₗ[A] A) (x₀ : M)
    (h : σ (b x₀) = 1) (hb : Lift b) : Lift (restr b σ) := by
  intro J t hJ ht z hz
  obtain ⟨x, hx, hxz⟩ := hb J t hJ ht z (apply_mem_smul_top (LinearMap.ker σ).subtype _ hz)
  refine ⟨proj (σ ∘ₗ b) x₀ h x, ?_, ?_⟩
  · rw [restr_proj]
    exact apply_mem_smul_top (proj σ (b x₀) h) _ hx
  · have e : proj (σ ∘ₗ b) x₀ h x - z = proj (σ ∘ₗ b) x₀ h (x - z) := by
      rw [map_sub, proj_ker]
    rw [e]
    exact apply_mem_smul_top _ _ hxz

theorem generalized_inverse_of_lift_rank [IsLocalRing A] : ∀ (n : ℕ) (Q N : Type) [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N] (b : Q →ₗ[A] N), Module.finrank A N = n → Lift b →
    ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q N _ _ _ _ _ _ _ _ b hn hb
    by_cases h : ∀ q, b q ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)
    · refine ⟨0, ?_⟩
      rw [GlobalTheory.T.lift_reduction_zero_of_maximal A Q N b hb h]
      simp
    · push_neg at h
      obtain ⟨x₀, hx₀⟩ := h
      obtain ⟨σ, hσ⟩ := exists_form _ hx₀
      have hσ' : (σ ∘ₗ b) x₀ = 1 := hσ
      haveI := ker_finite σ (b x₀) hσ
      haveI := ker_free σ (b x₀) hσ
      haveI := ker_finite (σ ∘ₗ b) x₀ hσ'
      haveI := ker_free (σ ∘ₗ b) x₀ hσ'
      have hlt : Module.finrank A (LinearMap.ker σ) < n := by
        have := finrank_ker σ (b x₀) hσ
        omega
      obtain ⟨s₁, hs₁⟩ := ih _ hlt (LinearMap.ker (σ ∘ₗ b)) (LinearMap.ker σ) (restr b σ) rfl
        (lift_restr b σ x₀ hσ hb)
      refine ⟨σ.smulRight x₀ + (LinearMap.ker (σ ∘ₗ b)).subtype ∘ₗ s₁ ∘ₗ proj σ (b x₀) hσ, ?_⟩
      ext q
      have h1 : restr b σ (s₁ (restr b σ (proj (σ ∘ₗ b) x₀ hσ' q))) =
          restr b σ (proj (σ ∘ₗ b) x₀ hσ' q) := LinearMap.congr_fun hs₁ _
      rw [restr_proj] at h1
      have h2 := congrArg (Subtype.val) h1
      rw [restr_coe, proj_coe] at h2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, map_add (f := _),
        map_smul, Submodule.subtype_apply]
      rw [h2]
      abel

end GlobalTheory.CompanionTheory.PerfVB.GenInv

theorem GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift :
    ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
      [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N]
      (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b :=
  fun A Q N _ _ _ _ _ _ _ _ _ _ b hb =>
    GenInv.generalized_inverse_of_lift_rank (A := A) _ Q N b rfl hb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocalStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalized_inverse_of_lift_local : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift | exact GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift <;> assumption)
end
