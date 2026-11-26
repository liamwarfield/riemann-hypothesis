module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCmCompositumMaximalRealSubfield
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem rcsup_mem_real {L M' : Type} [Field L] [Field M'] (f : L →+* M') (hL : IsTotallyReal L) (x : L) :
    f x ∈ maximalRealSubfield M' := by
  intro φ
  have h : x ∈ maximalRealSubfield L := by
    rw [IsTotallyReal.maximalRealSubfield_eq_top]; trivial
  exact h (φ.comp f)

private theorem rcsup_map_real {M M' : Type} [Field M] [Field M'] (g : M →+* M') {x : M}
    (hx : x ∈ maximalRealSubfield M) : g x ∈ maximalRealSubfield M' :=
  fun φ => hx (φ.comp g)

private theorem rcsup_cm_of_pair {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (d : K) (hd0 : d ≠ 0)
    (hd : ∀ φ : K →+* ℂ, star (φ d) = - φ d)
    (hspan : ∀ y : K, ∃ a ∈ maximalRealSubfield K, ∃ b ∈ maximalRealSubfield K, y = a + b * d) :
    IsCMField K := by
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h0 : (s : K) + (t : K) * d = 0 := by
      simpa [Subfield.smul_def] using hst
    have h1 : φ s + φ t * φ d = 0 := by
      rw [← map_mul, ← map_add (f := _), h0, map_zero]
    have h2 : φ s - φ t * φ d = 0 := by
      have := congrArg star h1
      rw [star_add, star_mul', s.2 φ, t.2 φ, hd φ, star_zero] at this
      linear_combination this
    have h3 : φ s = 0 := by linear_combination (h1 + h2) / 2
    have hs : (s : K) = 0 := (map_eq_zero φ).mp h3
    have ht : (t : K) = 0 := by
      rw [hs, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right hd0
    exact ⟨Subtype.ext hs, Subtype.ext ht⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro y _
    obtain ⟨a, ha, b, hb, rfl⟩ := hspan y
    have e : a + b * d = (⟨a, ha⟩ : maximalRealSubfield K) • (1 : K) + (⟨b, hb⟩ : maximalRealSubfield K) • d := by
      simp [Subfield.smul_def]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hrk : Module.finrank (maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
    simp
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := { finrank_eq_two' := hrk }
  exact {}

theorem UpperTheory.solvable_cm_compositum_maximalRealSubfield :
    UpperTheory.V.Af.Sol.RCSup := by
  intro L M M' _ _ _ _ _ _ _ f hL htop hM
  rcases hM with hM | hM
  · left
    rw [← maximalRealSubfield_eq_top_iff_isTotallyReal, eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact rcsup_mem_real f hL z
    | algebraMap r => exact rcsup_mem_real _ hM r
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | mul x y _ _ hx hy => exact mul_mem (hx trivial) (hy trivial)
  · right
    haveI : IsTotallyComplex M' := isTotallyComplex_of_algebra M M'
    obtain ⟨x, hx⟩ : ∃ x : M, IsCMField.complexConj M x ≠ x := by
      by_contra h
      apply IsCMField.complexConj_ne_one M
      ext x
      by_contra h'
      exact h ⟨x, h'⟩
    set δ : M := x - IsCMField.complexConj M x with hδ
    have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hx.symm
    have hcδ : IsCMField.complexConj M δ = -δ := by
      rw [hδ, map_sub, IsCMField.complexConj_apply_apply]; ring
    have hd : ∀ φ : M' →+* ℂ, star (φ (algebraMap M M' δ)) = - φ (algebraMap M M' δ) := by
      intro φ
      have := IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M M')) δ
      rw [hcδ, map_neg] at this
      exact this.symm
    have hsq : algebraMap M M' δ * algebraMap M M' δ ∈ maximalRealSubfield M' := by
      intro φ
      rw [map_mul, star_mul', hd φ]; ring
    refine rcsup_cm_of_pair (algebraMap M M' δ) ((_root_.map_ne_zero _).mpr hδ0) hd ?_
    intro y
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨f z, rcsup_mem_real f hL z, 0, zero_mem _, by simp⟩
    | algebraMap r =>
      refine ⟨algebraMap M M' ((r + IsCMField.complexConj M r) / 2), rcsup_map_real _ ?_,
        algebraMap M M' ((r - IsCMField.complexConj M r) / (2 * δ)), rcsup_map_real _ ?_, ?_⟩
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcδ]
        field_simp
        ring
      · rw [← map_mul, ← map_add (f := _)]
        congr 1
        field_simp
        ring
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a * a' + b * b' * (algebraMap M M' δ * algebraMap M M' δ),
        add_mem (mul_mem ha ha') (mul_mem (mul_mem hb hb') hsq),
        a * b' + b * a', add_mem (mul_mem ha hb') (mul_mem hb ha'), by ring⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CharacterExtendsToGaloisGroup
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem ext_two {Γ H A : Type} [Group Γ] [Group H] [CommGroup A] (i : H →* Γ) (hi : Function.Injective i)
    (δ : H →* A) (c : Γ) (hcc : c * c = 1) (hc : ∀ s, i s ≠ c) (hall : ∀ g, ∃ s, i s = g ∨ i s = g * c)
    (hinv : ∀ s, ∃ t, i t = c * i s * c ∧ δ t = δ s) :
    ∃ δ' : Γ →* A, δ'.comp i = δ ∧ δ' c = 1 := by
  choose p hp using hall
  have huniq : ∀ g s, (i s = g ∨ i s = g * c) → p g = s := by
    intro g s hs
    rcases hp g with h | h <;> rcases hs with h' | h'
    · exact hi (h.trans h'.symm)
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc ((p g)⁻¹ * s))
    · exact absurd (by rw [map_mul, map_inv, h, h', inv_mul_cancel_left]) (hc (s⁻¹ * p g))
    · exact hi (h.trans h'.symm)
  refine ⟨MonoidHom.mk' (fun g => δ (p g)) fun g g' => ?_, MonoidHom.ext fun s => ?_, ?_⟩
  · rcases hp g with h | h
    · rw [huniq (g * g') (p g * p g') (by
        rw [map_mul, h]
        rcases hp g' with h' | h'
        · exact Or.inl (by rw [h'])
        · exact Or.inr (by rw [h', mul_assoc])), map_mul]
    · obtain ⟨t, ht, hδ⟩ := hinv (p g')
      rw [huniq (g * g') (p g * t) (by
        rw [map_mul, h, ht, mul_assoc g c, mul_assoc c (i _), ← mul_assoc c c, hcc, one_mul]
        rcases hp g' with h' | h'
        · exact Or.inr (by rw [h', mul_assoc])
        · exact Or.inl (by rw [h', mul_assoc g', hcc, mul_one])), map_mul, hδ]
  · change δ (p (i s)) = δ s
    rw [huniq _ s (Or.inl rfl)]
  · change δ (p c) = 1
    rw [huniq c 1 (Or.inr (by rw [map_one, hcc])), map_one]

private theorem conj_on {F M Ω : Type} [Field F] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra F Ω]
    [Algebra M Ω] {c : G F Ω} (hc : IsConjEl c) (x : M) :
    c (algebraMap M Ω x) = algebraMap M Ω (IsCMField.complexConj M x) := by
  obtain ⟨j, hj⟩ := hc
  refine j.injective ?_
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj M (j.comp (algebraMap M Ω)) x).symm

private theorem conj_comm {K M : Type} [Field K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    (σ : M ≃ₐ[K] M) (x : M) : IsCMField.complexConj M (σ x) = σ (IsCMField.complexConj M x) := by
  let φ : M →+* ℂ := Classical.choice inferInstance
  refine φ.injective ?_
  rw [IsCMField.complexEmbedding_complexConj]
  exact (IsCMField.complexEmbedding_complexConj M (φ.comp (σ : M →+* M)) x).symm

private theorem lift_fix {F M Ω : Type} [Field F] [Field M] [Field Ω] [Algebra F M] [Algebra F Ω] [Algebra M Ω]
    [IsScalarTower F M Ω] (g : G F Ω) (hg : ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) :
    ∃ s : G M Ω, resG F M Ω s = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hg, AlgEquiv.ext fun _ => rfl⟩

private theorem ex_conj (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ c : G (maximalRealSubfield K) Ω, IsConjEl c := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  let φ : K →+* ℂ := Classical.choice inferInstance
  letI : Algebra K ℂ := φ.toAlgebra
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := K) (S := Ω) (M := ℂ)).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := maximalRealSubfield K) j
    (ComplexEmbedding.conjugate j) (RingHom.ext fun x =>
      ((mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))).symm)
  exact ⟨σ.symm, j, fun x => DFunLike.congr_fun hσ x⟩

theorem UpperTheory.character_extends_to_galois_group :
    UpperTheory.V.Af.Sol.ExtChar := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ
  have kill : ∀ t : G K Ω, (∀ x : M, t (algebraMap M Ω x) = algebraMap M Ω x) → δ t = 1 := fun t ht => by
    obtain ⟨s, rfl⟩ := lift_fix t ht
    exact DFunLike.congr_fun hδ s
  obtain ⟨c, hc⟩ := ex_conj K Ω
  have hcc : c * c = 1 := by
    obtain ⟨j, hj⟩ := hc
    exact AlgEquiv.ext fun x => j.injective (by
      rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply])
  have hKM : ∀ (g : G (maximalRealSubfield K) Ω), (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) →
      ∃ s : G K Ω, resG (maximalRealSubfield K) K Ω s = g ∧ δ s = 1 := fun g hg => by
    obtain ⟨s, rfl⟩ := lift_fix (M := K) g fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω, hg]
    exact ⟨s, rfl, kill s hg⟩
  obtain ⟨δ', h1, h2⟩ := ext_two (resG (maximalRealSubfield K) K Ω) (AlgEquiv.restrictScalars_injective _) δ c hcc
    (fun s hs => IsCMField.complexConj_ne_one K (AlgEquiv.ext fun x => (algebraMap K Ω).injective (by
      rw [← conj_on hc, ← hs]
      exact s.commutes x)))
    (fun g => by
      have h2 : Nat.card (K ≃ₐ[maximalRealSubfield K] K) = 2 :=
        (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K) ▸
          IsGalois.card_aut_eq_finrank (maximalRealSubfield K) K
      rw [Nat.card_eq_two_iff' 1] at h2
      by_cases hg : g.restrictNormal K = 1
      · obtain ⟨s, hs⟩ := lift_fix (M := K) g fun x => by
          rw [← AlgEquiv.restrictNormal_commutes, hg, AlgEquiv.one_apply]
        exact ⟨s, Or.inl hs⟩
      · have hg' := h2.unique hg (IsCMField.complexConj_ne_one K)
        obtain ⟨s, hs⟩ := lift_fix (M := K) (g * c) fun x => by
          rw [AlgEquiv.mul_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes, hg',
            IsCMField.complexConj_apply_apply]
        exact ⟨s, Or.inr hs⟩)
    (fun s => by
      obtain ⟨t, ht, hδt⟩ := hKM (c * resG _ K Ω s * c * (resG _ K Ω s)⁻¹) fun x => by
        obtain ⟨y, rfl⟩ := (s.restrictNormal M).surjective x
        change c (s (c (s.symm _))) = _
        rw [AlgEquiv.restrictNormal_commutes, s.symm_apply_apply, conj_on hc, ← AlgEquiv.restrictNormal_commutes,
          conj_on hc, conj_comm, IsCMField.complexConj_apply_apply, AlgEquiv.restrictNormal_commutes]
      exact ⟨t * s, by rw [map_mul, ht, inv_mul_cancel_right], by rw [map_mul, hδt, one_mul]⟩)
  have h3 : ∀ g : G (maximalRealSubfield K) Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → δ' g = 1 :=
    fun g hg => by
      obtain ⟨s, rfl, hs⟩ := hKM g hg
      exact (DFunLike.congr_fun h1 s).trans hs
  refine ⟨δ', h1, fun d hd => ?_, ?_⟩
  · have h4 := h3 (d * c) fun x => by
      rw [AlgEquiv.mul_apply, conj_on hc, conj_on hd, IsCMField.complexConj_apply_apply]
    rwa [map_mul, h2, mul_one] at h4
  · let f : M →ₐ[maximalRealSubfield K] Ω := IsScalarTower.toAlgHom (maximalRealSubfield K) M Ω
    haveI : FiniteDimensional (maximalRealSubfield K) f.fieldRange :=
      (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun g hg => ?_) (IntermediateField.fixingSubgroup_isOpen f.fieldRange)
    exact h3 g fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurExtension
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurScalar
noncomputable def UpperTheory.Reformulated.B.Qi17.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qi17.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qi17.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qi17.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.Qi17.schur_scalar :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qi17.IsIrr r →
        ∀ (g : GL (Fin n) k),
          (∀ (s : Γ), (r : Γ → GL (Fin n) k) s * g = g * (r : Γ → GL (Fin n) k) s) →
            ∃ (c : kˣ), (↑g : Matrix (Fin n) (Fin n) k) = (↑c : k) • (1 : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n r hr g hg
  obtain ⟨hne, -, hmin⟩ := hr
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hinv : UpperTheory.Reformulated.B.Qi17.IsInv r
      (Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c) := by
    intro s v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    have h : (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
        = (r s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hg s]
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have htop := (hmin _ le_top hinv).resolve_left hc
  have hgc : (g : Matrix (Fin n) (Fin n) k) = c • (1 : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c := by
      rw [htop]; exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hgc
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
    apply hv
    have h1 : (1 : Matrix (Fin n) (Fin n) k) = 0 := by
      rw [← g.mul_inv, hgc, zero_mul]
    rw [← Matrix.one_mulVec v, h1, Matrix.zero_mulVec]
  exact ⟨Units.mk0 c hc0, hgc⟩
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem irr_nontrivial {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) : Nontrivial (Fin n → k) := by
  obtain ⟨hne, -, -⟩ := hirr
  by_contra hc
  rw [not_nontrivial_iff_subsingleton] at hc
  exact hne (Subsingleton.elim _ _)

private theorem smul_one_inj {k : Type} [Field k] {n : ℕ} [Nontrivial (Fin n → k)] (a b : k)
    (h : a • (1 : Matrix (Fin n) (Fin n) k) = b • 1) : a = b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.mulVec v) h
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  exact smul_left_injective k hv h2

private theorem schur_scalar {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : GL (Fin n) k) (hg : ∀ s, r s * g = g * r s) :
    ∃ c : kˣ, (g : Matrix (Fin n) (Fin n) k) = (c : k) • 1 :=
  _root_.UpperTheory.Reformulated.B.Qi17.schur_scalar r hirr g hg

theorem UpperTheory.schur_extension :
    UpperTheory.V.Af.Sol.SchurExt := by
  intro Γ Γ' k _ _ _ _ n r r₁ φ hN hirr hiso
  obtain ⟨g, hg⟩ := hiso
  have hnt := irr_nontrivial _ hirr
  simp only [MonoidHom.comp_apply] at hg
  have hcomm : ∀ s t, (r.comp φ) t * (r s * (g * r₁ s * g⁻¹)⁻¹) =
      (r s * (g * r₁ s * g⁻¹)⁻¹) * (r.comp φ) t := by
    intro s t
    obtain ⟨u, hu⟩ := hN.conj_mem' (φ t) ⟨t, rfl⟩ s
    have h1 := hg u
    rw [hu] at h1
    simp only [map_mul, map_inv] at h1
    have h2 : r (φ t) * r s = r s * ((r s)⁻¹ * r (φ t) * r s) := by group
    rw [MonoidHom.comp_apply, ← mul_assoc, h2, h1, hg t]
    group
  choose c hc using fun s => schur_scalar _ hirr _ (hcomm s)
  have hr : ∀ s, (r s : Matrix (Fin n) (Fin n) k) =
      (c s : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    intro s
    have h1 : r s = (r s * (g * r₁ s * g⁻¹)⁻¹) * (g * r₁ s * g⁻¹) := by group
    rw [h1, Units.val_mul, hc s, Matrix.smul_mul, Matrix.one_mul]
  have huniq : ∀ s (a : kˣ), (r s : Matrix (Fin n) (Fin n) k) =
      (a : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) → c s = a := by
    intro s a ha
    apply Units.ext
    apply smul_one_inj (n := n)
    rw [← hc s, Units.val_mul, ha, Matrix.smul_mul, Units.mul_inv]
  have hmul : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply huniq
    have h1 : g * r₁ (s * t) * g⁻¹ = (g * r₁ s * g⁻¹) * (g * r₁ t * g⁻¹) := by
      rw [map_mul]; group
    rw [map_mul r, Units.val_mul, hr s, hr t, h1, Units.val_mul (g * r₁ s * g⁻¹), Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Units.val_mul (c s)]
  refine ⟨MonoidHom.mk' c hmul, ?_, g, ?_⟩
  · ext t
    have : c (φ t) = 1 := huniq _ _ (by rw [← hg t]; simp)
    simp [this]
  · intro s
    apply Units.ext
    rw [hr s]
    simp only [Units.val_mul, tw_val, MonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConjInertiaDiagonalOfIsTypeWD
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ) (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (r : G L Ω →* GL (Fin n) (Qbar l)) (χ : Fin n → Ine (F := L) A →* (Qbar l)ˣ) (x : WD h), IsWDOf ι r x → IsTypeWD h (fun i => W.pushCh ι.toRingHom (χ i)) x → ∃ g : GL (Fin n) (Qbar l), ∀ t : Ine (F := L) A, ((g * r t * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = Matrix.diagonal fun i => (χ i t : Qbar l) := by
  intro l _ L Ω _ _ _ _ _ ι n A w h _hl r χ x hWD hType
  classical
  obtain ⟨t, _ht, φ, hφ, N, a, hMon, hFS, hax⟩ := hWD
  obtain ⟨b, hbx, hbN, hbρ⟩ := hType
  have hiso : a.Iso b := WD.mk_eq_mk.mp (hax.trans hbx.symm)
  obtain ⟨e, he1, he2⟩ := hiso
  obtain ⟨_hNnil, U, hUo, hU⟩ := hMon
  obtain ⟨haN, hFS⟩ := hFS
  have htoEnd : ∀ X : Matrix (Fin n) (Fin n) (Qbar l),
      toEndC ι X = Matrix.toLin' (X.map ι) := fun X => rfl
  have haN0 : a.N = 0 := by
    apply LinearMap.ext
    intro v
    have h0 := he2 v
    rw [hbN, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at h0
    exact h0
  have hN0 : N = 0 := by
    have h0 : Matrix.toLin' (N.map ι) = Matrix.toLin' (0 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← htoEnd, ← haN, haN0, map_zero]
    have h2 := Matrix.toLin'.injective h0
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa using h3
  have hpow : ∀ s : Ine (F := L) A, ∃ m : ℕ, 0 < m ∧ s ^ m ∈ U := by
    intro s
    have hUn : (U : Set (Ine (F := L) A)) ∈ nhds (1 : Ine (F := L) A) := hUo.mem_nhds U.one_mem
    obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ _).mp hUn
    obtain ⟨E, hEfin, hEu⟩ := (krullTopology_mem_nhds_one_iff L Ω u).mp hu
    let f : ℕ → (E →ₐ[L] Ω) := fun k => ((s : G L Ω) ^ k).toAlgHom.comp E.val
    obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
    have key : ∀ i j : ℕ, i < j → f i = f j → s ^ (j - i) ∈ U := by
      intro i j hlt hf
      apply hsub
      apply hEu
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hy' := congrArg (fun φ : E →ₐ[L] Ω => φ ⟨y, hy⟩) hf
      simp only [f, AlgHom.comp_apply] at hy'
      have hj : (s : G L Ω) ^ j = (s : G L Ω) ^ i * (s : G L Ω) ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hj] at hy'
      have hy'' : ((s : G L Ω) ^ i) y = ((s : G L Ω) ^ i) (((s : G L Ω) ^ (j - i)) y) := hy'
      have := ((s : G L Ω) ^ i).injective hy''
      show ((s ^ (j - i) : Ine (F := L) A) : G L Ω) • y = y
      rw [Subgroup.coe_pow]
      exact this.symm
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨j - i, Nat.sub_pos_of_lt hlt, key i j hlt hfij⟩
    · exact ⟨i - j, Nat.sub_pos_of_lt hlt, key j i hlt hfij.symm⟩
  have hrs : ∀ s : Ine (F := L) A,
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) = a.ρ (ineIncl h s) := by
    intro s
    obtain ⟨m, hm, hsm⟩ := hpow s
    have hrm : (r (s : G L Ω)) ^ m = 1 := by
      apply Units.ext
      have h1 := hU _ hsm
      rw [hN0, smul_zero, IsNilpotent.exp_zero] at h1
      rw [← map_pow, ← Subgroup.coe_pow, h1, Units.val_one]
    set f : Module.End ℂ (Fin n → ℂ) :=
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) with hf
    have hfm : f ^ m = 1 := by
      rw [hf, ← htoEnd, ← map_pow, ← Units.val_pow_eq_pow_val, hrm, Units.val_one, map_one]
    have hfss : f.IsSemisimple := by
      apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (p := Polynomial.X ^ m - Polynomial.C 1)
      · exact (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero).squarefree
      · simp [hfm]
    obtain ⟨hcomm, hnil⟩ := hFS (ineIncl h s)
    have hwd : toEndC ι (wdMat t hφ r N (ineIncl h s)) = f := by
      simp only [wdMat, hN0, smul_zero, IsNilpotent.exp_zero, mul_one]
      rfl
    simp only [hwd] at hcomm hnil
    have hss2 : (f - a.ρ (ineIncl h s)).IsSemisimple :=
      hfss.sub_of_commute hcomm.symm (a.semisimple _)
    exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss2)
  let P : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e : Module.End ℂ (Fin n → ℂ))
  let Pi : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e.symm : Module.End ℂ (Fin n → ℂ))
  have hPPi : P * Pi = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e : Module.End ℂ (Fin n → ℂ)).comp (e.symm : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  have hPiP : Pi * P = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e.symm : Module.End ℂ (Fin n → ℂ)).comp (e : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  let Φ := ι.symm.toRingHom.mapMatrix (m := Fin n)
  let g : GL (Fin n) (Qbar l) :=
    ⟨Φ P, Φ Pi, by rw [← map_mul, hPPi, map_one], by rw [← map_mul, hPiP, map_one]⟩
  refine ⟨g, fun s => ?_⟩
  have hA : a.ρ (ineIncl h s) = (e.symm : Module.End ℂ (Fin n → ℂ)).comp
      ((b.ρ (ineIncl h s)).comp (e : Module.End ℂ (Fin n → ℂ))) := by
    apply LinearMap.ext
    intro v
    simp [← he1]
  have hR : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι =
      Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P := by
    have h1 := congrArg LinearMap.toMatrix' (hrs s)
    rw [LinearMap.toMatrix'_toLin', hA, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hbρ s,
      LinearMap.toMatrix'_toLin', ← mul_assoc] at h1
    rw [h1]
    rfl
  have hback : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Φ ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) := by
    ext i j
    simp [Φ]
  show Φ P * (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * Φ Pi = _
  rw [hback, hR, ← map_mul, ← map_mul]
  rw [show P * (Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P) * Pi =
      Matrix.diagonal (fun i => ι (χ i s : Qbar l)) by
    rw [← mul_assoc, ← mul_assoc, hPPi, one_mul, mul_assoc, hPPi, mul_one]]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Φ]
  · simp [Φ, Matrix.diagonal_apply_ne _ hij]
end
