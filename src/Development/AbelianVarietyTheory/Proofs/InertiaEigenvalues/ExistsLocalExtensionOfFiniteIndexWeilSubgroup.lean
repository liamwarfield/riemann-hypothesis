module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseNearOfDecompositionFixedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPosPowGaloisFixingFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPosPowGaloisFixingFinset
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.PowFix

theorem exists_pos_pow_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (x : Ω) (hx : IsIntegral E x) : ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
  classical
  have hfin : ((minpoly E x).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  haveI := hfin.to_subtype
  let f : ℕ → (minpoly E x).rootSet Ω := fun n => ⟨(σ ^ n) x, by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    rw [show ((σ ^ n) x) = ((σ ^ n : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) x from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h' : (σ ^ a) x = (σ ^ b) x := congrArg Subtype.val h
  have key : ∀ a b : ℕ, a < b → (σ ^ a) x = (σ ^ b) x → ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
    intro a b hlt he
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : σ ^ b = σ ^ a * σ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e, AlgEquiv.mul_apply] at he
    exact ((σ ^ a).injective he).symm
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact key a b hlt h'
  · exact key b a hlt h'.symm

theorem pow_apply_eq_of_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (τ : Ω ≃ₐ[E] Ω) (x : Ω) (h : τ x = x) (j : ℕ) : (τ ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

theorem exists_pos_pow_fix : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  intro E Ω _ _ _ _ _ σ s
  classical
  have hint : ∀ x : Ω, IsIntegral E x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral
  choose k hk0 hk using fun x : Ω => exists_pos_pow_apply_eq σ x (hint x)
  refine ⟨∏ x ∈ s, k x, Finset.prod_pos fun x _ => hk0 x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k hx
  rw [hc, pow_mul]
  exact pow_apply_eq_of_apply_eq _ x (hk x) c

end GlobalTheory.PowFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPosPowGaloisFixingFinsetStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_pow_galois_fixing_finset : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  first | exact @GlobalTheory.PowFix.exists_pos_pow_fix | exact GlobalTheory.PowFix.exists_pos_pow_fix | (intros; apply GlobalTheory.PowFix.exists_pos_pow_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupOrbitRootSameStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupOrbitRootSameStabilizer
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Count

theorem decOrbit_root_count : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β β' : Ω) (S : Finset Ω), (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) → ∀ g : Polynomial E, g.Monic → g.natDegree = S.card → aeval β' g = 0 → (∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β) → (∀ σ : G E Ω, ∃ d ∈ Dec (F := E) A, σ β' = d β') ∧ (∀ σ ∈ Dec (F := E) A, σ β = β → σ β' = β') := by
  intro E Ω _ _ _ _ _ A β β' S hS g hg hdeg hroot hstab
  classical

  let φ : Ω → Ω := fun x => if h : ∃ d ∈ Dec (F := E) A, d β = x then (Classical.choose h) β' else 0
  have hφ : ∀ x ∈ S, ∃ d ∈ Dec (F := E) A, d β = x ∧ φ x = d β' := by
    intro x hx
    have h := (hS x).1 hx
    refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
    simp only [φ, dif_pos h]

  have hg0 : g ≠ 0 := hg.ne_zero
  have hconj : ∀ σ : G E Ω, σ β' ∈ (g.aroots Ω).toFinset := by
    intro σ
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨hg0, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, hroot, map_zero]

  have hinj : Set.InjOn φ S := by
    intro x hx y hy hxy
    obtain ⟨d, hd, rfl, hdx⟩ := hφ x hx
    obtain ⟨e, he, rfl, hey⟩ := hφ y hy
    have h1 : (e⁻¹ * d) β' = β' := by
      rw [AlgEquiv.mul_apply, ← hdx, hxy, hey]
      exact (AlgEquiv.symm_apply_apply e β')
    have h2 := hstab _ ((Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem he) hd) h1
    rw [AlgEquiv.mul_apply] at h2
    have := congrArg e h2
    simpa using this
  have hsub : S.image φ ⊆ (g.aroots Ω).toFinset := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨d, -, -, hdx⟩ := hφ x hx
    rw [hdx]; exact hconj d
  have hcard : (g.aroots Ω).toFinset.card ≤ (S.image φ).card := by
    rw [Finset.card_image_of_injOn hinj, ← hdeg]
    calc (g.aroots Ω).toFinset.card ≤ (g.aroots Ω).card := Multiset.toFinset_card_le _
      _ ≤ (g.map (algebraMap E Ω)).natDegree := Polynomial.card_roots' _
      _ = g.natDegree := Polynomial.natDegree_map _
  have heq : S.image φ = (g.aroots Ω).toFinset := Finset.eq_of_subset_of_card_le hsub hcard

  have hin : ∀ σ : G E Ω, ∃ x ∈ S, φ x = σ β' := by
    intro σ
    have := hconj σ
    rw [← heq] at this
    exact Finset.mem_image.1 this

  have hkey : ∀ τ ∈ Dec (F := E) A, τ β' = φ (τ β) := by
    intro τ hτ
    obtain ⟨x, hx, hxe⟩ := hin τ
    obtain ⟨d, hd, rfl, hdx⟩ := hφ x hx
    have h1 : (d⁻¹ * τ) β' = β' := by
      rw [AlgEquiv.mul_apply, ← hxe, hdx]
      exact (AlgEquiv.symm_apply_apply d β')
    have h2 := hstab _ ((Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hd) hτ) h1
    rw [AlgEquiv.mul_apply] at h2
    have h3 : τ β = d β := by
      have := congrArg d h2
      simpa using this
    rw [h3, ← hxe]
  refine ⟨fun σ => ?_, fun σ hσ hσβ => ?_⟩
  · obtain ⟨x, hx, hxe⟩ := hin σ
    obtain ⟨d, hd, -, hdx⟩ := hφ x hx
    exact ⟨d, hd, by rw [← hxe, hdx]⟩
  · have h1 := hkey σ hσ
    have h0 := hkey 1 (Dec (F := E) A).one_mem
    rw [h1, hσβ]
    exact h0.symm

end GlobalTheory.Count
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupOrbitRootSameStabilizerStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decompositionGroup_orbit_root_same_stabilizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β β' : Ω) (S : Finset Ω), (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) → ∀ g : Polynomial E, g.Monic → g.natDegree = S.card → aeval β' g = 0 → (∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β) → (∀ σ : G E Ω, ∃ d ∈ Dec (F := E) A, σ β' = d β') ∧ (∀ σ ∈ Dec (F := E) A, σ β = β → σ β' = β') := by
  first | exact @GlobalTheory.Count.decOrbit_root_count | exact GlobalTheory.Count.decOrbit_root_count | (intros; apply GlobalTheory.Count.decOrbit_root_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingLeFiniteIndexWeilSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingLeFiniteIndexWeilSubgroup
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilOpenFin

theorem exists_finset_fix_le : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  intro E Ω _ _ _ _ _ A w h h1 h2 h3 H hH hopen
  classical

  have hfix : ∀ (g : G E Ω) (t : Finset Ω), (∀ x ∈ t, g x = x) → ∀ n : ℤ, ∀ x ∈ t, (g ^ n) x = x := by
    intro g t hg n x hx
    have hm : g ∈ MulAction.stabilizer (G E Ω) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hg x hx
    have := (MulAction.mem_stabilizer_iff).mp (Subgroup.zpow_mem _ hm n)
    rwa [AlgEquiv.smul_def] at this
  obtain ⟨s₁, hs₁⟩ := h3 (H.comap (ineIncl h)) hopen
  let φ : Weil h := frob h
  obtain ⟨m, hm0, hm⟩ := h1 (φ : G E Ω) s₁
  have hN : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  set k : ℕ := m * H.normalCore.index with hk
  have hk0 : 0 < k := Nat.mul_pos hm0 (Nat.pos_of_ne_zero hN)
  let ψ : Weil h := φ ^ k
  have hψH : ψ ∈ H := by
    apply Subgroup.normalCore_le
    show φ ^ (m * H.normalCore.index) ∈ H.normalCore
    rw [pow_mul]; exact Subgroup.pow_index_mem _ _
  have hψdeg : deg ψ = k := by simp [ψ, φ]
  have hψfix : ∀ x ∈ s₁, (ψ : G E Ω) x = x := by
    intro x hx
    have := hfix _ s₁ hm (H.normalCore.index : ℤ) x hx
    simpa [ψ, φ, hk, pow_mul] using this
  obtain ⟨ζ, hζ⟩ := h2 k hk0
  refine ⟨insert ζ s₁, fun τ hτ => ?_⟩
  obtain ⟨i, hi⟩ := hζ τ (hτ ζ (Finset.mem_insert_self _ _))
  let ρ : Weil h := τ * ψ ^ (-i)
  have hρdeg : deg ρ = 0 := by
    simp only [ρ, deg_mul, deg_zpow, hψdeg, hi]; ring
  have hρIne : (ρ : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp hρdeg
  have hρfix : ∀ x ∈ s₁, (ρ : G E Ω) x = x := by
    intro x hx
    have e1 := hfix _ s₁ hψfix (-i) x hx
    show ((τ : G E Ω) * ((ψ ^ (-i) : Weil h) : G E Ω)) x = x
    rw [AlgEquiv.mul_apply, Subgroup.coe_zpow, e1]
    exact hτ x (Finset.mem_insert_of_mem hx)
  have hρM := hs₁ ⟨ρ, hρIne⟩ hρfix
  have hρH : ρ ∈ H := by
    have : ineIncl h ⟨ρ, hρIne⟩ ∈ H := hρM
    exact this
  have : τ = ρ * ψ ^ i := by simp [ρ]
  rw [this]
  exact H.mul_mem hρH (H.zpow_mem hψH i)

end GlobalTheory.WeilOpenFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingLeFiniteIndexWeilSubgroupStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_fixing_le_finiteIndex_weilSubgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  first | exact @GlobalTheory.WeilOpenFin.exists_finset_fix_le | exact GlobalTheory.WeilOpenFin.exists_finset_fix_le | (intros; apply GlobalTheory.WeilOpenFin.exists_finset_fix_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinset
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem GlobalTheory.stab_finset_eq_stab_primitive : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  intro E Ω _ _ _ _ _ s
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E (s : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E K
  refine ⟨(α : Ω), fun σ => ?_⟩
  have key : IntermediateField.adjoin E {(α : Ω)} = K := by
    have h1 := congrArg (IntermediateField.map K.val) hα
    rw [IntermediateField.adjoin_map] at h1
    have hm : IntermediateField.map K.val ⊤ = K := by
      ext y; constructor
      · rintro ⟨z, -, rfl⟩; exact z.2
      · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [hm] at h1
    simpa [Set.image_singleton] using h1

  have gen : ∀ (T : Set Ω), (∀ x ∈ T, σ x = x) → ∀ y ∈ IntermediateField.adjoin E T, σ y = y := by
    intro T hT y hy
    have := IntermediateField.algHom_ext_of_eq_adjoin E (S := IntermediateField.adjoin E T) (s := T) rfl
      (φ₁ := ((σ : Ω →ₐ[E] Ω)).comp (IntermediateField.adjoin E T).val)
      (φ₂ := (IntermediateField.adjoin E T).val) (fun x hx => by simp [hT x hx])
    exact congrArg (fun φ => φ ⟨y, hy⟩) this
  constructor
  · intro h x hx
    have hxK : x ∈ IntermediateField.adjoin E {(α : Ω)} := by
      rw [key]; exact IntermediateField.subset_adjoin E _ hx
    exact gen {(α : Ω)} (by simpa using h) x hxK
  · intro h
    exact gen (s : Set Ω) (fun x hx => h x hx) (α : Ω) α.2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinsetStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_element_stabilizer_finset : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  first | exact @GlobalTheory.stab_finset_eq_stab_primitive | exact GlobalTheory.stab_finset_eq_stab_primitive | (intros; apply GlobalTheory.stab_finset_eq_stab_primitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroup
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_finset_fix_subset_of_isOpen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)),
    IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A,
      (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  intro E Ω _ _ _ _ _ A M hM
  obtain ⟨U, hU, hUM⟩ := isOpen_induced_iff.mp hM
  have h1 : (1 : G E Ω) ∈ U := by
    have : (1 : Ine (F := E) A) ∈ (Subtype.val ⁻¹' U) := by rw [hUM]; exact M.one_mem
    simpa using this
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds h1)
  have hfg : L.toSubalgebra.FG := by
    apply Subalgebra.fg_of_fg_toSubmodule
    exact Module.Finite.iff_fg.mp hL
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun σ hσ => ?_⟩
  have hmem : (σ : G E Ω) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ∈ Algebra.adjoin E (t : Set Ω) := by rw [ht]; exact hx
    have key : Set.EqOn ((σ : G E Ω) : Ω →ₐ[E] Ω) (AlgHom.id E Ω) (Algebra.adjoin E (t : Set Ω)) :=
      AlgHom.eqOn_adjoin_iff.mpr (fun y hy => hσ y hy)
    exact key hx'
  have : σ ∈ (Subtype.val ⁻¹' U : Set (Ine (F := E) A)) := hLU hmem
  rw [hUM] at this
  exact this

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroupStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  first | exact @GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | exact GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | (intros; apply GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicBasePolynomialRootNearDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicBasePolynomialRootNearDecomposition
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_monic_base_root_near : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  intro E Ω _ _ _ _ _ A hdense f hf hfix β hβ r hr
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set n := f.natDegree with hn
  have hvr : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have hvrn : A.valuation r ^ n ≠ 0 := pow_ne_zero _ hvr
  have happ : ∀ i, ∃ e : E,
      A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i < A.valuation r ^ n := by
    intro i
    by_cases hb : β = 0
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · obtain ⟨e, he⟩ := hdense (f.coeff 0) (fun d hd => hfix d hd 0) (r ^ n) (pow_ne_zero _ hr)
        exact ⟨e, by simpa [map_pow] using he⟩
      · refine ⟨0, ?_⟩
        simp only [hb, map_zero, zero_pow hi.ne', mul_zero]
        exact zero_lt_iff.mpr hvrn
    · have hbi : β ^ i ≠ 0 := pow_ne_zero _ hb
      obtain ⟨e, he⟩ := hdense (f.coeff i) (fun d hd => hfix d hd i) (r ^ n / β ^ i)
        (div_ne_zero (pow_ne_zero _ hr) hbi)
      refine ⟨e, ?_⟩
      have hvb : A.valuation β ^ i ≠ 0 := by
        rw [← map_pow]; exact (Valuation.ne_zero_iff _).mpr hbi
      rw [map_div₀, map_pow, map_pow] at he
      calc A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i
          < A.valuation r ^ n / A.valuation β ^ i * A.valuation β ^ i :=
            mul_lt_mul_of_pos_right he (zero_lt_iff.mpr hvb)
        _ = A.valuation r ^ n := div_mul_cancel₀ _ hvb
  choose c hc using happ
  let p : E[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp : p.degree < n := degree_sum_fin_lt _
  let g : E[X] := X ^ n + p
  have hgm : g.Monic := monic_X_pow_add hp
  have hgd : g.natDegree = n := by
    show (X ^ n + p).natDegree = n
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have h0 : f.eval β = β ^ n + ∑ i ∈ Finset.range n, f.coeff i * β ^ i := by
    conv_lhs => rw [hf.as_sum]
    simp [Polynomial.eval_finsetSum, ← hn]
  have hga : aeval β g = β ^ n + ∑ i ∈ Finset.range n, algebraMap E Ω (c i) * β ^ i := by
    show aeval β (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_pow, aeval_X, map_sum, map_mul, aeval_C]
    rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap E Ω (c i) * β ^ i) n]
  have hgβ : aeval β g = ∑ i ∈ Finset.range n, (algebraMap E Ω (c i) - f.coeff i) * β ^ i := by
    have : aeval β g = aeval β g - f.eval β := by rw [hβ, sub_zero]
    rw [this, hga, h0]
    simp [sub_mul, Finset.sum_sub_distrib]
  have hvg : A.valuation (aeval β g) < A.valuation r ^ n := by
    rw [hgβ]
    refine Valuation.map_sum_lt _ hvrn fun i _ => ?_
    rw [map_mul, map_pow]; exact hc i
  set G := g.map (algebraMap E Ω) with hG
  have hGm : G.Monic := hgm.map _
  have hGd : G.natDegree = n := by rw [hG, natDegree_map, hgd]
  have hprod : (G.roots.map fun a => X - C a).prod = G :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hGm IsAlgClosed.card_roots_eq_natDegree
  have hev : aeval β g = (G.roots.map fun a => β - a).prod := by
    rw [aeval_def, ← eval_map, ← hG]
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hex : ∃ a ∈ G.roots, A.valuation (β - a) < A.valuation r := by
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation r ^ n ≤ A.valuation (aeval β g) := by
      rw [hev, map_multiset_prod, Multiset.map_map]
      have hcard : (G.roots.map (A.valuation ∘ fun a => β - a)).card = n := by
        rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hGd]
      calc A.valuation r ^ n = A.valuation r ^ (G.roots.map (A.valuation ∘ fun a => β - a)).card := by
            rw [hcard]
        _ ≤ _ := Multiset.pow_card_le_prod (by
            intro x hx
            obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
            exact hcon a ha)
    exact absurd hvg (not_lt.mpr h1)
  obtain ⟨a, ha, hva⟩ := hex
  refine ⟨g, hgm, hgd, a, ?_, ?_⟩
  · have := (mem_roots hGm.ne_zero).mp ha
    rw [aeval_def, ← eval_map]; exact this
  · rwa [Valuation.map_sub_swap]

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicBasePolynomialRootNearDecompositionStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  first | exact @GlobalTheory.WeilDeligne.exists_monic_base_root_near | exact GlobalTheory.WeilDeligne.exists_monic_base_root_near | (intros; apply GlobalTheory.WeilDeligne.exists_monic_base_root_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersion
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem krasner_val_lt_apply_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (a b : Ω) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hb' : A.valuation b ≠ 0 := by simpa using hb
    have hsb : σ b ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr hb
    have hsb' : A.valuation (σ b) ≠ 0 := by simpa using hsb
    rw [← div_lt_one₀ (zero_lt_iff.mpr hb'), ← div_lt_one₀ (zero_lt_iff.mpr hsb'),
      ← map_div₀, ← map_div₀, ← map_div₀, valuation_apply_lt_one_iff hσ]

theorem krasner_stabiliser (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (β β' : Ω)
    (h : ∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) :
    ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  intro σ hσ hfix
  by_contra hne
  have hσi : σ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hσ
  have hne' : (σ⁻¹ : G E Ω) β ≠ β := by
    intro he
    apply hne
    conv_lhs => rw [← he]
    exact mul_inv_apply β
  have h1 := h σ hσ hne
  have h2 := h σ⁻¹ hσi hne'
  rw [← krasner_val_lt_apply_iff hσ, map_sub σ, map_sub σ, mul_inv_apply, hfix] at h2
  have e : β - σ β = (β - β') + (β' - σ β) := by ring
  have h3 : A.valuation (β - σ β) = A.valuation (σ β - β) := Valuation.map_sub_swap _ _ _
  have h4 : A.valuation (β - β') = A.valuation (β' - β) := Valuation.map_sub_swap _ _ _
  have key : A.valuation (β - σ β) < A.valuation (β - σ β) := by
    conv_lhs => rw [e]
    refine Valuation.map_add_lt _ ?_ h2
    rw [h4, h3]; exact h1
  exact lt_irrefl _ key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersionStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (β β' : Ω), (∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) → ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  first | exact @GlobalTheory.krasner_stabiliser | exact GlobalTheory.krasner_stabiliser | (intros; apply GlobalTheory.krasner_stabiliser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Dorbit
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.LocalExtField

open Polynomial

theorem dorbit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β : Ω), ∃ S : Finset Ω, (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) ∧ ∃ f : Polynomial Ω, f.Monic ∧ f.natDegree = S.card ∧ (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) ∧ f.eval β = 0 := by
  intro E Ω _ _ _ _ _ A β
  classical
  have hint : IsIntegral E β := Algebra.IsIntegral.isIntegral β
  have hfin : {x : Ω | ∃ d ∈ Dec (F := E) A, d β = x}.Finite := by
    refine (Polynomial.rootSet_finite (minpoly E β) Ω).subset ?_
    rintro x ⟨d, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [show d β = (d : Ω →ₐ[E] Ω) β from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hS : ∀ x, x ∈ hfin.toFinset ↔ ∃ d ∈ Dec (F := E) A, d β = x := fun x => hfin.mem_toFinset
  refine ⟨hfin.toFinset, hS, ∏ x ∈ hfin.toFinset, (X - C x),
    monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x), ?_, ?_, ?_⟩
  · rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]; simp
  · intro d hd i
    have hperm : hfin.toFinset.image d = hfin.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨d', hd', rfl⟩ := (hS y).1 hy
        exact (hS _).2 ⟨d * d', mul_mem hd hd', rfl⟩
      · rw [Finset.card_image_of_injective _ d.injective]
    have key : (∏ x ∈ hfin.toFinset, (X - C x)).map (d : Ω →+* Ω) = ∏ x ∈ hfin.toFinset, (X - C x) := by
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      conv_rhs => rw [← hperm]
      rw [Finset.prod_image (fun x _ y _ h => d.injective h)]
      rfl
    have := congrArg (fun p => p.coeff i) key
    simpa [Polynomial.coeff_map] using this
  · rw [eval_prod]
    exact Finset.prod_eq_zero ((hS β).2 ⟨1, one_mem _, rfl⟩) (by simp)

end GlobalTheory.LocalExtField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingIffPreservesSubgroupOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingIffPreservesSubgroupOrbit
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem orbit_stab_cut_finite (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω) :
    ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  classical
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set S : Set Ω := {t | ∃ τ ∈ H, τ y = t} with hSdef
  have hS : S.Finite := by
    refine ((minpoly E y).rootSet_finite Ω).subset ?_
    rintro t ⟨τ, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv]
    simp [minpoly.aeval]
  set O := hS.toFinset with hOdef
  have hmemO : ∀ t, t ∈ O ↔ ∃ τ ∈ H, τ y = t := fun t => by simp [O, S]
  set P : Polynomial Ω := ∏ t ∈ O, (X - C t) with hP
  refine ⟨(Finset.range (P.natDegree + 1)).image P.coeff, fun σ => ?_⟩
  have key : (∀ x ∈ (Finset.range (P.natDegree + 1)).image P.coeff, σ x = x) ↔
      P.map (σ : Ω →+* Ω) = P := by
    constructor
    · intro h
      ext n
      rw [coeff_map]
      by_cases hn : n ≤ P.natDegree
      · exact h _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]; simp
    · intro h x hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
      have := congrArg (fun p => p.coeff n) h
      simpa [coeff_map] using this
  have hmap : P.map (σ : Ω →+* Ω) = ∏ t ∈ O, (X - C (σ t)) := by
    simp [hP, Polynomial.map_prod]
  rw [key, hmap]
  constructor
  · intro h τ hτ
    have h0 : (∏ t ∈ O, (X - C (σ t))).eval (σ (τ y)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero ((hmemO _).2 ⟨τ, hτ, rfl⟩) (by simp)
    rw [h, hP, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨t, ht, ht0⟩ := h0
    obtain ⟨τ', hτ', rfl⟩ := (hmemO t).1 ht
    refine ⟨τ', hτ', ?_⟩
    simpa [sub_eq_zero] using ht0
  · intro h
    have hinj : Function.Injective (σ : Ω → Ω) := σ.injective
    have hsub : O.image σ ⊆ O := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨τ, hτ, rfl⟩ := (hmemO t).1 ht
      obtain ⟨τ', hτ', he⟩ := h τ hτ
      exact (hmemO _).2 ⟨τ', hτ', he.symm⟩
    have heq : O.image σ = O :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
    calc ∏ t ∈ O, (X - C (σ t)) = ∏ u ∈ O.image σ, (X - C u) :=
          by
          rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
      _ = P := by rw [heq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingIffPreservesSubgroupOrbitStatement
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω), ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  first | exact @GlobalTheory.orbit_stab_cut_finite | exact GlobalTheory.orbit_stab_cut_finite | (intros; apply GlobalTheory.orbit_stab_cut_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalExtField

theorem exists_localExt_of_finiteIndex : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ (L : IntermediateField E Ω), FiniteDimensional E L ∧ IsLocalExt L h ∧ ∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G E Ω) (x : Ω) = x := by
  intro E Ω _ _ _ _ _ A w h H hH hO
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_fixing_le_finiteIndex_weilSubgroup E Ω A w h (GlobalTheory.T.exists_pos_pow_galois_fixing_finset E Ω) (GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree E Ω A w h) (GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup E Ω A) H hH hO
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_primitive_element_stabilizer_finset E Ω s
  have hyH : ∀ σ : Weil h, (σ : G E Ω) y = y → σ ∈ H := fun σ hσ => hs σ ((hy σ).1 hσ)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit E Ω (H.map (Weil h).subtype) y
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_primitive_element_stabilizer_finset E Ω s'
  have hβH : ∀ σ : Weil h, (σ : G E Ω) β = β ↔ σ ∈ H := by
    intro σ
    rw [hβ, hs']
    constructor
    · intro hσ
      obtain ⟨τ', hτ', e⟩ := hσ 1 (one_mem _)
      obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ'
      have e1 : (σ : G E Ω) y = (τ₀ : G E Ω) y := by simpa using e
      have h2 : (τ₀⁻¹ * σ : Weil h) ∈ H := by
        apply hyH
        rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, e1, ← AlgEquiv.mul_apply,
          inv_mul_cancel, AlgEquiv.one_apply]
      simpa using H.mul_mem hτ₀ h2
    · intro hσ τ hτ
      refine ⟨(σ : G E Ω) * τ, Subgroup.mul_mem _ (Subgroup.mem_map_of_mem _ hσ) hτ, ?_⟩
      rfl
  obtain ⟨S, hS, f, hfm, hfdeg, hfinv, hfβ⟩ := GlobalTheory.LocalExtField.dorbit E Ω A β
  obtain ⟨r, hr0, hr⟩ : ∃ r : Ω, r ≠ 0 ∧ ∀ d ∈ Dec (F := E) A, d β ≠ β →
      A.valuation r ≤ A.valuation (d β - β) := by
    by_cases hne : (S.erase β).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (S.erase β).exists_min_image (fun x => A.valuation (x - β)) hne
      exact ⟨x - β, sub_ne_zero.mpr (Finset.ne_of_mem_erase hx), fun d hd hdβ =>
        hmin _ (Finset.mem_erase.mpr ⟨hdβ, (hS _).mpr ⟨d, hd, rfl⟩⟩)⟩
    · exact ⟨1, one_ne_zero, fun d hd hdβ =>
        absurd ⟨d β, Finset.mem_erase.mpr ⟨hdβ, (hS _).mpr ⟨d, hd, rfl⟩⟩⟩ hne⟩
  obtain ⟨g, hgm, hgdeg, β', hβ'g, hβ'⟩ :=
    GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition E Ω A (GlobalTheory.T.exists_base_near_of_decomposition_fixed E Ω A w h) f hfm hfinv β hfβ r hr0
  have hkr := GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version E Ω A β β' (fun d hd hdβ => lt_of_lt_of_le hβ' (hr d hd hdβ))
  obtain ⟨hall, hback⟩ := GlobalTheory.T.decompositionGroup_orbit_root_same_stabilizer E Ω A β β' S hS g hgm (hgdeg.trans hfdeg) hβ'g hkr
  have hint : IsIntegral E β' := Algebra.IsIntegral.isIntegral β'
  have agree : ∀ σ τ : G E Ω, σ β' = τ β' → ∀ x ∈ IntermediateField.adjoin E {β'}, σ x = τ x := by
    intro σ τ e x hx
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hx
    exact (AlgHom.eqOn_adjoin_iff (φ := (σ : Ω →ₐ[E] Ω)) (ψ := (τ : Ω →ₐ[E] Ω))).2
      (by intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact e) hx
  refine ⟨IntermediateField.adjoin E {β'}, IntermediateField.adjoin.finiteDimensional hint, ?_, ?_⟩
  · intro σ
    obtain ⟨d, hd, hσd⟩ := hall σ
    obtain ⟨τ, hτ, hτd⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h d hd β'
    exact ⟨⟨τ, hτ⟩, fun x => agree τ σ (hτd.trans hσd.symm) x x.2⟩
  · intro σ
    rw [← hβH σ]
    constructor
    · intro hσβ x
      have hσβ' := hback σ (Weil_le_Dec h σ.2) hσβ
      exact agree σ 1 (by simpa using hσβ') x x.2
    · intro hfix
      exact hkr σ (Weil_le_Dec h σ.2) (hfix ⟨β', IntermediateField.mem_adjoin_simple_self E β'⟩)

end GlobalTheory.LocalExtField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ (L : IntermediateField E Ω), FiniteDimensional E L ∧ IsLocalExt L h ∧ ∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G E Ω) (x : Ω) = x := by
  first | exact @GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | exact GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | (intros; apply GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex <;> assumption)
end
