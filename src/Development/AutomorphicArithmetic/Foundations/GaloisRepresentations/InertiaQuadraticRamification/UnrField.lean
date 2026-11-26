module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.AsmUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInjectiveCharacter
theorem UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char :
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
    ∃ (lam0 : (ZMod p)ˣ →* ℂˣ), Function.Injective (⇑lam0 : (ZMod p)ˣ → ℂˣ) := by
  intro p inst
  haveI : NeZero (Nat.card (ZMod p)ˣ) := ⟨Nat.card_pos.ne'⟩
  have hcard : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ) :=
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ (Nat.card (ZMod p)ˣ)).symm
  let e : (ZMod p)ˣ ≃* rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ := mulEquivOfCyclicCardEq hcard
  exact ⟨(rootsOfUnity (Nat.card (ZMod p)ˣ) ℂ).subtype.comp e.toMonoidHom,
    (Subgroup.subtype_injective _).comp e.injective⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.MainUnr
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshSplit
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem under_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {t : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A t) :
    IsPlaceOver A (t.under (𝓞 ℚ)) := fun x => by
  rw [IsScalarTower.algebraMap_apply ℚ F Ω]
  exact hA (algebraMap _ _ x)

private theorem res_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ g ∈ Dec (F := F) A :=
  GlobalTheory.AboveL.mem_dec_congr A _ g fun _ => rfl

private theorem res_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g : G F Ω) :
    (AlgEquiv.restrictScalarsHom ℚ g : G ℚ Ω) ∈ Ine (F := ℚ) A ↔ g ∈ Ine (F := F) A := by
  rw [mem_Ine, mem_Ine]
  exact Iff.rfl

private theorem eq_of_natCast_mem {p : ℕ} (hp : p.Prime) {a b : HeightOneSpectrum (𝓞 ℚ)}
    (ha : ((p : ℕ) : 𝓞 ℚ) ∈ a.asIdeal) (hb : ((p : ℕ) : 𝓞 ℚ) ∈ b.asIdeal) : a = b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hmax : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsMaximal := by
    have h := Ideal.map_isMaximal_of_equiv Rat.ringOfIntegersEquiv.symm (p := Ideal.span {(p : ℤ)})
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h
  have key : ∀ c : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ c.asIdeal →
      c.asIdeal = Ideal.span {((p : ℕ) : 𝓞 ℚ)} := fun c hc =>
    (hmax.eq_of_le c.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hc)).symm
  exact HeightOneSpectrum.ext ((key a ha).trans (key b hb).symm)

private theorem natCast_normV_mem (u : HeightOneSpectrum (𝓞 ℚ)) (h : (normV u).Prime) :
    ((normV u : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
  have hne : Nat.card (𝓞 ℚ ⧸ u.asIdeal) ≠ 0 := by
    have h0 := h.ne_zero
    unfold normV at h0
    exact h0
  haveI : Finite (𝓞 ℚ ⧸ u.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 ℚ ⧸ u.asIdeal)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold normV
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero _

private theorem core {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (hFC : FreshChar) (V : Subgroup (G F Ω)) (hV : IsOpen (V : Set (G F Ω)))
    (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (n : ℕ) (hn : 0 < n) :
    ∃ ψ : G F Ω →* ℂˣ, Good ψ.ker ∧
      (∀ (t : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A t →
        Ine (F := F) A ≤ ψ.ker ∨ Dec (F := F) A ≤ V) ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ V ∧
        ∃ τ ∈ Ine (F := F) A, orderOf (ψ τ) = n := by
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  let res : G F Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ
  have hres_inj : Function.Injective res := fun g h hgh => AlgEquiv.ext fun x => by
    have e := congrArg (fun σ : G ℚ Ω => σ x) hgh
    exact e
  have hVo : IsOpen ((V.map res : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) :=
    GlobalTheory.KLift.isOpen_map_restrictScalars V hV
  obtain ⟨ψ₀, hG₀, hpow₀, hT₀, u₀, hu₀T, hp, hu₀, hram⟩ := hFC ℚ Ω (V.map res) hVo
    ((fun t : HeightOneSpectrum (𝓞 F) => t.under (𝓞 ℚ)) '' T) (hT.image _) n hn
  have decV : ∀ A : ValuationSubring Ω, IsPlaceOver A u₀ → Dec (F := F) A ≤ V := by
    intro A hA g hg
    obtain ⟨h, hhV, hh⟩ := (hu₀ A hA).1 ((res_dec A g).2 hg)
    rwa [hres_inj hh] at hhV
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω u₀
  obtain ⟨u, hu⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := ℚ) (K := F) hA₀
  have eu : u.under (𝓞 ℚ) = u₀ := eq_of_isPlaceOver (under_place hu) hA₀
  have hunder : ∀ A : ValuationSubring Ω, IsPlaceOver A u → IsPlaceOver A u₀ := by
    intro A hA
    rw [← eu]
    exact under_place hA
  refine ⟨ψ₀.comp res, ?_, ?_, ?_, ?_, u, ?_, ?_⟩
  · refine ⟨hG₀.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ F Ω),
      Abelianization.commutator_subset_ker _, fun j c hc => ?_⟩
    exact hG₀.real j (res c) hc
  · intro t A hA
    by_cases hpt : ((normV u₀ : ℕ) : 𝓞 ℚ) ∈ (t.under (𝓞 ℚ)).asIdeal
    · right
      have e : t.under (𝓞 ℚ) = u₀ := eq_of_natCast_mem hp hpt (natCast_normV_mem u₀ hp)
      apply decV
      rw [← e]
      exact under_place hA
    · left
      intro g hg
      exact hram _ A (under_place hA) hpt _ ((res_ine A g).2 hg)
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hpow₀,
      MonoidHom.one_apply, MonoidHom.one_apply]
  · intro t ht A hA g hg
    exact hT₀ _ ⟨t, ht, rfl⟩ A (under_place hA) _ ((res_dec A g).2 hg)
  · intro huT
    exact hu₀T ⟨u, huT, eu⟩
  · intro A hA
    refine ⟨decV A (hunder A hA), ?_⟩
    obtain ⟨τ₀, hτ₀, ho⟩ := (hu₀ A (hunder A hA)).2
    obtain ⟨h, -, hh⟩ := (hu₀ A (hunder A hA)).1 (Ine_le_Dec A hτ₀)
    refine ⟨h, (res_ine A h).1 (by rw [show res h = τ₀ from hh]; exact hτ₀), ?_⟩
    show orderOf (ψ₀ (res h)) = n
    rw [show res h = τ₀ from hh]
    exact ho

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshSplit :
    FreshChar → FreshSplit := by
  intro hFC E Ω _ _ _ _ _ _ U hU T hT n hn
  haveI := isAlgClosure_plus (E := E) (Ω := Ω)
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ψ, h1, h2, h3, h4, u, hu, h5⟩ := core hFC (U ⊓ fixGrp (maximalRealSubfield E) Ω E)
    (hU.inter (isOpen_fixGrp _ Ω E)) T hT n hn
  exact ⟨ψ, h1, fun t A hA => (h2 t A hA).imp_right fun h g hg => (h hg).2, h3, h4, u, hu,
    fun A hA => ⟨fun g hg => ((h5 A hA).1 hg).1, (h5 A hA).2⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.MoveRoot
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.moveRoot :
    MoveRoot := by
  intro Ω _ _ _ U hU ℓ hℓ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 (hU.mem_nhds U.one_mem)
  haveI := hEfin
  set b := Module.finrank ℚ E + 2 with hb
  have hn : 0 < ℓ ^ b := pow_pos hℓ.pos b
  haveI : NeZero ((ℓ ^ b : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨ζ0, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ b) Ω)
    (Polynomial.degree_cyclotomic_pos _ Ω hn).ne'
  have hprim : IsPrimitiveRoot ζ0 (ℓ ^ b) := Polynomial.isRoot_cyclotomic_iff.1 hζ0
  have hnot : ζ0 ∉ E := by
    intro hmem
    have h0 := minpoly.natDegree_le (A := ℚ) (⟨ζ0, hmem⟩ : E)
    have h0' := IntermediateField.minpoly_eq (K := ℚ) (S := E) ⟨ζ0, hmem⟩
    have h1 : (minpoly ℚ ζ0).natDegree ≤ Module.finrank ℚ E := h0' ▸ h0
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim hn,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hℓ (by omega)] at h1
    have h2 : b - 1 < ℓ ^ (b - 1) := Nat.lt_pow_self hℓ.one_lt
    have h3 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    have h4 : ℓ ^ (b - 1) ≤ Module.finrank ℚ E :=
      (Nat.le_mul_of_pos_right _ h3).trans h1
    generalize ℓ ^ (b - 1) = N at h2 h4
    omega
  have hex : ∃ σ ∈ E.fixingSubgroup, σ ζ0 ≠ ζ0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    exact hcon
  obtain ⟨σ, hσE, hσ⟩ := hex
  refine ⟨b, σ, hEsub hσE, fun ζ hζ hfix => hσ ?_⟩
  haveI : NeZero (ℓ ^ b) := ⟨hn.ne'⟩
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
  rw [← hm, map_pow, hfix]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.CharOrd
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_injective_char (p : ℕ) [Fact p.Prime] :
    ∃ lam0 : (ZMod p)ˣ →* ℂˣ, Function.Injective lam0 :=
  _root_.UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char p

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.charOrd : CharOrd := by
  intro p _ ℓ k a hℓ hdvd
  obtain ⟨lam0, hinj⟩ := exists_injective_char p
  have hm0 : 0 < orderOf (a ^ 2) := orderOf_pos _
  have h2m : orderOf a ∣ 2 * orderOf (a ^ 2) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  have hlk : ℓ ^ k ∣ orderOf (a ^ 2) := by
    have h1 : ℓ ^ (k + 1) ∣ 2 * orderOf (a ^ 2) := hdvd.trans h2m
    by_cases h2 : ℓ = 2
    · subst h2
      rw [pow_succ, mul_comm] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    · have hc : Nat.Coprime (ℓ ^ (k + 1)) 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hℓ Nat.prime_two).mpr h2)
      exact (Dvd.intro _ (pow_succ ℓ k).symm).trans (hc.dvd_of_dvd_mul_left h1)
  obtain ⟨e, he⟩ := hlk
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      omega
    · exact h
  have hlpos : 0 < ℓ ^ k := pow_pos hℓ.pos k
  refine ⟨lam0 ^ (2 * e), ?_, ?_⟩
  · rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    simp
  · have h1 : (lam0 ^ (2 * e)) a = (lam0 (a ^ 2)) ^ e := by
      rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    have h2 : orderOf (lam0 (a ^ 2)) = ℓ ^ k * e := by
      rw [orderOf_injective lam0 hinj, he]
    rw [h1, orderOf_pow' _ hepos.ne', h2, Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ hepos]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.OrdPrime
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open scoped Pointwise

private theorem op_isPlaceOver {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hA : A.valuation (p : Ω) < 1) : IsPlaceOver A v := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by rw [map_intCast]; simp)⟩
  have hint : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hcast : algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := by simp
  rw [hcast]
  by_cases hd : (p : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    constructor
    · intro _
      have : (((p : ℤ) * m : ℤ) : 𝓞 ℚ) = (p : 𝓞 ℚ) * (m : 𝓞 ℚ) := by push_cast; rfl
      rw [this]
      exact v.asIdeal.mul_mem_right _ hv
    · intro _
      have : ((((p : ℤ) * m : ℤ)) : Ω) = (p : Ω) * (m : Ω) := by push_cast; rfl
      rw [this, Valuation.map_mul]
      exact mul_lt_one_of_lt_of_le hA (hint m)
  · obtain ⟨a, b, hab⟩ := (Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 hd
    constructor
    · intro h
      exfalso
      have e : (1 : Ω) = (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) := by
        have := congrArg (fun t : ℤ => (t : Ω)) hab
        push_cast at this
        exact this.symm
      have h1 : A.valuation (1 : Ω) < 1 := by
        rw [e]
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul, mul_comm]; exact mul_lt_one_of_lt_of_le hA (hint a)
        · rw [Valuation.map_mul, mul_comm]; exact mul_lt_one_of_lt_of_le h (hint b)
      simp at h1
    · intro h
      exfalso
      have e : (1 : 𝓞 ℚ) = (a : 𝓞 ℚ) * (p : 𝓞 ℚ) + (b : 𝓞 ℚ) * (n : 𝓞 ℚ) := by
        have := congrArg (fun t : ℤ => (t : 𝓞 ℚ)) hab
        push_cast at this
        exact this.symm
      have h1 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
        rw [e]
        exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ h)
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

private theorem op_normV (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

private theorem op_ringHom_eq {Y Ω : Type} [Field Y] [NumberField Y] [Field Ω] [CharZero Ω] (j₁ j₂ : Y →+* Ω)
    (h : ∀ i, j₁ (Module.finBasis ℚ Y i) = j₂ (Module.finBasis ℚ Y i)) (y : Y) : j₁ y = j₂ y := by
  have := (Module.finBasis ℚ Y).ext (f₁ := (RingHom.toRatAlgHom j₁).toLinearMap)
    (f₂ := (RingHom.toRatAlgHom j₂).toLinearMap) h
  exact DFunLike.congr_fun this y

private theorem op_dec_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {N : Subgroup (G F Ω)} (hNo : IsOpen (N : Set (G F Ω))) {B : ValuationSubring Ω}
    {u : HeightOneSpectrum (𝓞 F)} (hB : IsPlaceOver B u) (hI : Ine (F := F) B ≤ N) {σ : G F Ω}
    (hσ : IsFrob B (normV u) σ) (hσN : σ ∈ N) : Dec (F := F) B ≤ N := by
  intro d hd
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω B u hB ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((N.subgroupOf (Dec (F := F) B) : Subgroup (Dec (F := F) B)) : Set (Dec (F := F) B)) :=
    (N.isClosed_of_isOpen hNo).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) B) ⊔ (Ine (F := F) B).subgroupOf (Dec (F := F) B))
    (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hσN))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hI (Subgroup.mem_subgroupOf.1 hx)))) hc
  rw [h] at h2
  exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := F) B)))

private theorem op_arith {ℓ m j k t : ℕ} (hℓ : ℓ.Prime) (hm : m ∣ ℓ ^ j * t) (hm0 : m ≠ 0) (hk : ℓ ^ k ∣ t)
    (hn : ¬ ℓ ^ k ∣ m) : m ∣ t := by
  obtain ⟨a, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 ℓ hℓ.ne_one
  have hak : a < k := by
    by_contra h
    exact hn (Dvd.dvd.mul_right (pow_dvd_pow ℓ (not_lt.1 h)) _)
  have hco : Nat.Coprime ℓ m' := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hm'
  have h1 : m' ∣ t := (hco.symm.pow_right j).dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hm)
  have h2 : ℓ ^ a ∣ t := (pow_dvd_pow ℓ hak.le).trans hk
  exact (hco.pow_left a).mul_dvd_of_dvd_of_dvd h2 h1

private theorem op_val_root {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q n : ℕ} {y : Ω} (hn0 : n ≠ 0)
    (hq : ¬ A.valuation (q : Ω) < 1) (hy : y ^ n = (q : Ω)) : A.valuation y = 1 := by
  have h1 : A.valuation (q : Ω) = 1 := le_antisymm (valuation_natCast_le_one A q) (not_lt.1 hq)
  rw [← hy, map_pow] at h1
  exact (pow_eq_one_iff.1 h1).resolve_right hn0

private theorem op_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q n t : ℕ} {y w : Ω}
    (hp : A.valuation (p : Ω) < 1) (hn : ¬ A.valuation (n : Ω) < 1) (hn0 : n ≠ 0)
    (hq : ¬ A.valuation (q : Ω) < 1) (hy : y ^ n = (q : Ω)) (hw : w ^ n = (q : Ω))
    (hfrob : A.valuation (w - y ^ (n * t + 1)) < 1) (hqt : (p : ℤ) ∣ (q : ℤ) ^ t - 1) : w = y := by
  have hvy := op_val_root A hn0 hq hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hvy
  have hq0 : (q : Ω) ≠ 0 := by
    rw [← hy]
    exact pow_ne_zero _ hy0
  obtain ⟨ξ, rfl⟩ : ∃ ξ, w = ξ * y := ⟨w / y, (div_mul_cancel₀ _ hy0).symm⟩
  have hξn : ξ ^ n = 1 := by
    rw [mul_pow, hy] at hw
    exact mul_right_cancel₀ hq0 (hw.trans (one_mul _).symm)
  have e1 : ξ * y - y ^ (n * t + 1) = y * (ξ - (q : Ω) ^ t) := by
    rw [pow_succ, pow_mul, hy]
    ring
  rw [e1, map_mul, hvy, one_mul] at hfrob
  obtain ⟨c, hc⟩ := hqt
  have e2 : (q : Ω) ^ t - 1 = (p : Ω) * (c : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hc
    push_cast at this
    exact this
  have h2 : A.valuation ((q : Ω) ^ t - 1) < 1 := by
    rw [e2, map_mul]
    exact mul_lt_one_of_lt_of_le hp ((A.valuation_le_one_iff _).mpr (intCast_mem A c))
  have h3 : A.valuation (ξ - 1) < 1 := by
    have e3 : ξ - 1 = (ξ - (q : Ω) ^ t) + ((q : Ω) ^ t - 1) := by ring
    rw [e3]
    exact Valuation.map_add_lt _ hfrob h2
  rw [eq_of_pow_eq_one A hn hξn (one_pow n) h3, one_mul]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.ordPrime :
    KumMove → OrdPrime := by
  classical
  intro hKum E Ω _ _ _ _ _ ℓ k q B hℓ hq
  have hc0 : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hcl : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans ℚ E Ω⟩
  have hac : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E

  let X : Set Ω := Set.range fun i => algebraMap E Ω (Module.finBasis ℚ E i)
  have hXfin : X.Finite := Set.finite_range _
  let L := IntermediateField.adjoin ℚ X
  have hLfin : FiniteDimensional ℚ L := by
    have : Finite X := hXfin
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨U0, hU0n, hU0o, -, hU0U⟩ := GlobalTheory.OpenNormal.exists_open_normal_le Ω ℚ L.fixingSubgroup
    (IntermediateField.fixingSubgroup_isOpen L)

  obtain ⟨j, hj⟩ := hKum Ω U0 hU0o ℓ q hℓ hq
  have hℓ0 : ∀ n, 0 < ℓ ^ n := fun n => pow_pos hℓ.pos n
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (ℓ ^ (j + k)) := by
    haveI : NeZero ((ℓ ^ (j + k) : ℕ) : Ω) := ⟨by exact_mod_cast (hℓ0 (j + k)).ne'⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (ℓ ^ (j + k))
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (q : Ω) (hℓ0 j)
  obtain ⟨σ, hσU, hσζ, hσy⟩ := hj (j + k) (by omega) ζ y hζ hy
  let X2 : Set Ω := {ζ, y}
  have hX2fin : X2.Finite := by simp [X2]
  let L2 := IntermediateField.adjoin ℚ X2
  have hL2fin : FiniteDimensional ℚ L2 := by
    have : Finite X2 := hX2fin
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨N, hNn, hNo, -, hNU⟩ := GlobalTheory.OpenNormal.exists_open_normal_le Ω ℚ (L2.fixingSubgroup ⊓ U0)
    ((IntermediateField.fixingSubgroup_isOpen L2).inter hU0o)
  have hfix : ∀ n ∈ N, ∀ x ∈ X2, n x = x := fun n hn x hx =>
    (IntermediateField.mem_fixingSubgroup_iff L2 n).1 (hNU hn).1 x (IntermediateField.subset_adjoin ℚ X2 hx)

  set K := max B (max q (ℓ ^ (j + k))) with hK
  have hKne : ((K.factorial : ℕ) : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero K)
  have hspan : Ideal.span {((K.factorial : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    simpa using hKne
  obtain ⟨v, hvS, hd, -, B0, hB0, hIne, φ, hφ, hφg⟩ := GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1
    GlobalTheory.Published.chebotarevDegreeOne' ℚ Ω N hNo hNn σ (Ideal.finite_factors hspan).toFinset
  have hKv : ((K.factorial : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    apply hvS
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  have hφN : σ⁻¹ * φ ∈ N := by
    have := hNn.conj_mem _ hφg σ⁻¹
    simpa [mul_assoc] using this
  have hφX : ∀ x ∈ X2, φ x = σ x := by
    intro x hx
    have h2 := hfix _ hφN x hx
    have h3 := congrArg σ h2
    rw [AlgEquiv.mul_apply] at h3
    have h4 : σ ((σ⁻¹ : G ℚ Ω) (φ x)) = φ x := mul_inv_apply _
    rw [h4] at h3
    exact h3
  have hφU : φ ∈ U0 := by
    have := U0.mul_mem hσU (hNU hφN).2
    simpa using this
  have hDec : Dec (F := ℚ) B0 ≤ U0 := op_dec_le hU0o hB0 (hIne.trans fun n hn => (hNU hn).2) hφ hφU
  have hpr : (normV v).Prime := by
    rw [op_normV]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hd
  have hpv : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [op_normV]
    exact Ideal.absNorm_mem _
  have hdvd : ∀ m : ℕ, 0 < m → m ≤ K → ((m : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro m hm hmK h
    apply hKv
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hm hmK
    rw [hc, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ h
  have hBp : B < normV v := by
    by_contra hle
    exact hdvd _ hpr.pos ((not_lt.1 hle).trans (le_max_left _ _)) hpv
  have hnv : ∀ m : ℕ, 0 < m → m ≤ K → ¬ B0.valuation (m : Ω) < 1 := fun m hm hmK h =>
    hdvd m hm hmK ((hB0 (m : 𝓞 ℚ)).1 (by simpa using h))
  have hpval : B0.valuation ((normV v : ℕ) : Ω) < 1 := by
    simpa using (hB0 ((normV v : ℕ) : 𝓞 ℚ)).2 hpv
  have hqK : q ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hMK : ℓ ^ (j + k) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hjK : ℓ ^ j ≤ K := (Nat.pow_le_pow_right hℓ.pos (by omega)).trans hMK
  have hqv := hnv q (by omega) hqK
  refine ⟨normV v, hpr, hBp, ?_, ?_⟩
  · haveI : Fact (normV v).Prime := ⟨hpr⟩

    have hζ0 : ζ ≠ 0 := hζ.ne_zero (hℓ0 _).ne'
    have h1 : φ ζ = ζ ^ normV v := by
      refine eq_of_pow_eq_one B0 (hnv _ (hℓ0 _) hMK) ?_ ?_
        (hφ.2 ζ (valuation_eq_one_of_pow_eq_one B0 (hℓ0 _).ne' hζ.pow_eq_one).le)
      · rw [← map_pow, hζ.pow_eq_one, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hφζ : φ ζ = ζ := by
      rw [hφX ζ (Set.mem_insert _ _), hσζ]
    have hpow : ζ ^ (normV v - 1) = 1 := by
      have : ζ ^ (normV v - 1) * ζ = 1 * ζ := by
        rw [← pow_succ, Nat.sub_add_cancel hpr.one_le, one_mul, ← h1, hφζ]
      exact mul_right_cancel₀ hζ0 this
    obtain ⟨c, hc⟩ := hζ.dvd_of_pow_eq_one _ hpow
    have hpt : normV v - 1 = ℓ ^ j * (ℓ ^ k * c) := by
      rw [hc, pow_add, mul_assoc]
    have hpt' : normV v = ℓ ^ j * (ℓ ^ k * c) + 1 := by
      have := hpr.one_le
      omega
    by_contra hn
    have hpq : ¬ normV v ∣ q := by
      rintro ⟨c', hc'⟩
      apply hdvd q (by omega) hqK
      rw [hc', Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hpv
    have hq0 : (q : ZMod (normV v)) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have hm := ZMod.orderOf_dvd_card_sub_one hq0
    have hm0 : orderOf (q : ZMod (normV v)) ≠ 0 :=
      (Nat.pos_of_dvd_of_pos hm (by have := hpr.two_le; omega)).ne'
    have hmt := op_arith hℓ (hpt ▸ hm) hm0 (Dvd.intro _ rfl) hn
    have hqt : (q : ZMod (normV v)) ^ (ℓ ^ k * c) = 1 := orderOf_dvd_iff_pow_eq_one.1 hmt
    have hqt' : ((normV v : ℕ) : ℤ) ∣ (q : ℤ) ^ (ℓ ^ k * c) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hqt, sub_self]
    have hvy := op_val_root B0 (hℓ0 j).ne' hqv hy
    have hfrob : B0.valuation (σ y - y ^ (ℓ ^ j * (ℓ ^ k * c) + 1)) < 1 := by
      have := hφ.2 y hvy.le
      rw [hφX y (Set.mem_insert_of_mem _ rfl)] at this
      rwa [← hpt']
    exact hσy (op_val B0 hpval (by exact hnv _ (hℓ0 j) hjK) (hℓ0 j).ne' hqv hy
      (by rw [← map_pow, hy, map_natCast]) hfrob hqt')
  · intro A hA h hhA z
    have hAv : IsPlaceOver A v := op_isPlaceOver A v _ hpr hpv hA
    obtain ⟨s, hs⟩ := exists_smul_eq_of_isPlaceOver hB0 hAv
    let h' : G ℚ Ω := AlgEquiv.ofRingEquiv (f := h) (fun r => by simp)
    have hDecA : h' ∈ Dec (F := ℚ) A := by
      rw [mem_Dec]
      ext w
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hhA]
      show h' ((h'⁻¹ : G ℚ Ω) w) ∈ A ↔ w ∈ A
      rw [mul_inv_apply]
    have hk : s⁻¹ * h' * s ∈ Dec (F := ℚ) B0 := by
      rw [mem_Dec]
      show (s⁻¹ * h' * s) • B0 = B0
      rw [mul_smul, hs, mul_smul, (mem_Dec.1 hDecA), ← hs, inv_smul_smul]
    have h1 := hU0n.conj_mem _ (hDec hk) s
    have h2 : s * (s⁻¹ * h' * s) * s⁻¹ = h' := by group
    rw [h2] at h1
    have hfixb : ∀ i, h (algebraMap E Ω (Module.finBasis ℚ E i)) = algebraMap E Ω (Module.finBasis ℚ E i) :=
      fun i => (IntermediateField.mem_fixingSubgroup_iff L h').1 (hU0U h1) _
        (IntermediateField.subset_adjoin ℚ X ⟨i, rfl⟩)
    exact op_ringHom_eq ((h : Ω →+* Ω).comp (algebraMap E Ω)) (algebraMap E Ω) hfixb z
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharPP
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem chi_of_pow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (k : ℕ) (h : g ζ = ζ ^ k) :
    ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p) = (k : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 := IsPrimitiveRoot.autToPow_spec F hζ g
  have h2 : ζ ^ (k % p) = ζ ^ k := by
    conv_lhs => rw [hζ.eq_orderOf]
    exact pow_mod_orderOf ζ k
  rw [h, ← h2] at h1
  have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ hp) h1
  rw [← ZMod.natCast_mod k p, ← h3, ZMod.natCast_val, ZMod.cast_id', id]

private theorem chi_one {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (h : g ζ = ζ) : hζ.autToPow F g = 1 := by
  apply Units.ext
  rw [chi_of_pow hζ g 1 (by rw [pow_one, h]), Nat.cast_one, Units.val_one]

private theorem exists_prim {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] : ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω p

private theorem chi_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (j : Ω →+* ℂ) (c : G F Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    hζ.autToPow F c = -1 := by
  have hp : p.Prime := Fact.out
  have hjζ : IsPrimitiveRoot (j ζ) p := hζ.map_of_injective j.injective
  have hn : ‖j ζ‖ = 1 := hjζ.norm'_eq_one hp.ne_zero
  have hne : j ζ ≠ 0 := hjζ.ne_zero hp.ne_zero
  have h1 : c ζ = ζ ^ (p - 1) := by
    apply j.injective
    rw [hc, ← Complex.inv_eq_conj hn, map_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, hjζ.pow_eq_one]
  apply Units.ext
  rw [chi_of_pow hζ c _ h1, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, Units.val_neg, Units.val_one]

private theorem good_ker {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ}
    [Fact p.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (lam : (ZMod p)ˣ →* ℂˣ) (h1 : lam (-1) = 1) :
    Good (lam.comp (hζ.autToPow F)).ker := by
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  refine ⟨?_, Abelianization.commutator_subset_ker _, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (G F Ω) ζ) ?_
      (stabilizer_isOpen_of_isIntegral (K := F) ζ)
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_one hζ g hg, map_one]
  · intro j c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_conj hζ j c hc, h1]

private theorem normV_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    1 < normV v ∧ ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hc : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hc]; exact Ideal.absNorm_mem _
  refine ⟨?_, hmem⟩
  have hne : normV v ≠ 0 := by
    rw [hc]; exact Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : normV v ≠ 1 := by
    rw [hc]
    intro h
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

private theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ}
    (hq : (q : 𝓞 F) ∈ v.asIdeal) (h : Nat.Coprime q p) : (p : 𝓞 F) ∉ v.asIdeal := by
  intro hp
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have hb := Nat.gcd_eq_gcd_ab q p
  rw [h] at hb
  have : ((1 : ℤ) : 𝓞 F) = (q : 𝓞 F) * ((q.gcdA p : ℤ) : 𝓞 F) + (p : 𝓞 F) * ((q.gcdB p : ℤ) : 𝓞 F) := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hb
    push_cast at this ⊢
    exact this
  rw [Int.cast_one] at this
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hq) (Ideal.mul_mem_right _ _ hp)

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrCharPP :
    OrdPrime → CharOrd → DecPow → UnrCharPP := by
  intro hOrd hChar hDec ℓ k hℓ E Ω _ _ _ _ _ _ v
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨hq1, hqv⟩ := normV_mem v
  obtain ⟨p, hp, hBp, hdvd, hsplit⟩ := hOrd E Ω ℓ (k + 1) (normV v) (max (normV v) 2) hℓ hq1
  haveI : Fact p.Prime := ⟨hp⟩
  have hqp : normV v < p := lt_of_le_of_lt (le_max_left _ _) hBp
  have hcop : Nat.Coprime (normV v) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) hqp)).symm
  have hpv : ((p : ℕ) : 𝓞 (maximalRealSubfield E)) ∉ v.asIdeal := not_mem_of_coprime v hqv hcop
  set a : (ZMod p)ˣ := ZMod.unitOfCoprime (normV v) hcop with ha
  have hao : ℓ ^ (k + 1) ∣ orderOf a := by
    rw [← orderOf_units]
    simpa [ha] using hdvd
  obtain ⟨lam, hlam1, hlamo⟩ := hChar p ℓ k a hℓ hao
  obtain ⟨ζ, hζ⟩ := exists_prim (F := maximalRealSubfield E) (Ω := Ω) p
  refine ⟨lam.comp (hζ.autToPow _), good_ker hζ lam hlam1, ?_, fun A hA => ⟨?_, fun φ hφ => ?_⟩⟩
  · intro t A hA
    by_cases hpt : ((p : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ t.asIdeal
    · right
      intro g hg x
      have hval : A.valuation (p : Ω) < 1 := by
        have := (hA (p : 𝓞 (maximalRealSubfield E))).2 hpt
        simpa using this
      exact hsplit A hval g.toRingEquiv (fun z => apply_mem_iff_of_mem_Dec hg z) x
    · left
      intro τ hτ
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        chi_one hζ τ ((hDec _ Ω A t hA p hp hpt ζ hζ).2 τ hτ), map_one]
  · intro τ hτ
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      chi_one hζ τ ((hDec _ Ω A v hA p hp hpv ζ hζ).2 τ hτ), map_one]
  · have hN : ¬ A.valuation (p : Ω) < 1 := by
      simpa using not_valuation_lt_one_of_isPlaceOver hpv hA 1
    have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
    have hv : A.valuation ζ ≤ 1 := by
      have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
      exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
    have hφζ : φ ζ = ζ ^ normV v := by
      refine eq_of_pow_eq_one A hN ?_ ?_ (hφ.2 ζ hv)
      · rw [← map_pow, hz1, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
    have h1 : hζ.autToPow (maximalRealSubfield E) φ = a := by
      apply Units.ext
      rw [chi_of_pow hζ φ _ hφζ, ha, ZMod.coe_unitOfCoprime]
    rw [MonoidHom.comp_apply, h1]
    exact hlamo
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.KumMove
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.kumMove :
    MoveRoot → NormVal → KumMove := by
  intro hMR hNV Ω _ _ _ U hU ℓ q hℓ hq
  obtain ⟨b, σ0, hσ0U, hσ0⟩ := hMR Ω U hU ℓ hℓ
  obtain ⟨D, hDpos, hD⟩ := hNV Ω U hU q hq
  obtain ⟨e, D', hD'ℓ, hDe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hDpos.ne' ℓ hℓ.one_lt.ne'
  refine ⟨b + e, fun k hk ζ y hζ hy => ?_⟩
  by_contra hcon
  push_neg at hcon
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hpow : ∀ τ : G ℚ Ω, ∃ a, τ ζ = ζ ^ a := by
    intro τ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  have hact : ∀ (τ : G ℚ Ω) (a : ℕ), τ ζ = ζ ^ a → ∀ ω : Ω, ω ^ (ℓ ^ k) = 1 → τ ω = ω ^ a := by
    intro τ a ha ω hω
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hω
    rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]
  have comm : ∀ σ ∈ U, ∀ τ ∈ U, σ (τ y) = τ (σ y) := by
    intro σ hσ τ hτ
    obtain ⟨a, ha⟩ := hpow σ
    obtain ⟨c, hc⟩ := hpow τ
    have h1 : ((τ * σ)⁻¹ * (σ * τ)) ζ = ζ := by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
        AlgEquiv.mul_apply, hc, ha, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul, mul_comm]
    have h2 := hcon _ (U.mul_mem (U.inv_mem (U.mul_mem hτ hσ)) (U.mul_mem hσ hτ)) h1
    rwa [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply] at h2
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hy
    exact hq0 hy.symm
  obtain ⟨a0, ha0⟩ := hpow σ0
  obtain ⟨a, ha, ha1⟩ : ∃ a, σ0 ζ = ζ ^ a ∧ 1 ≤ a :=
    ⟨a0 + ℓ ^ k, by rw [ha0, pow_add, hζ.pow_eq_one, mul_one],
      by have := Nat.one_le_pow k ℓ hℓ.pos; omega⟩
  have hjk : ℓ ^ (b + e) ∣ ℓ ^ k := pow_dvd_pow ℓ hk
  have hzfix : ∀ τ ∈ U, τ (σ0 y / y ^ a) = σ0 y / y ^ a := by
    intro τ hτ
    have hτy : (τ y) ^ (ℓ ^ (b + e)) = y ^ (ℓ ^ (b + e)) := by
      rw [← map_pow, hy, map_natCast]
    obtain ⟨χ, hτy'⟩ : ∃ χ, τ y = y * χ := ⟨τ y / y, by field_simp⟩
    have hχj : χ ^ ℓ ^ (b + e) = 1 := by
      rw [hτy', mul_pow] at hτy
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) (hτy.trans (mul_one _).symm)
    have hχ1 : χ ^ (ℓ ^ k) = 1 := by
      obtain ⟨m, hm⟩ := hjk
      rw [hm, pow_mul, hχj, one_pow]
    have hχ0 : χ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hχ1
      exact zero_ne_one hχ1
    rw [map_div₀, map_pow, comm τ hτ σ0 hσ0U, hτy', map_mul, hact σ0 a ha χ hχ1, mul_pow]
    exact mul_div_mul_right _ _ (pow_ne_zero _ hχ0)
  have hzeq : (σ0 y / y ^ a) ^ (ℓ ^ (b + e)) * (q : Ω) ^ (a - 1) = 1 := by
    have hσy : (σ0 y) ^ (ℓ ^ (b + e)) = q := by rw [← map_pow, hy, map_natCast]
    rw [div_pow, hσy, ← pow_mul', pow_mul, hy]
    have hqa : (q : Ω) ^ a = (q : Ω) ^ (a - 1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel ha1]
    rw [hqa]
    field_simp
  have hdiv := hD _ (ℓ ^ (b + e)) (a - 1) hzfix hzeq
  have hb : ℓ ^ b ∣ a - 1 := by
    rw [pow_add, hDe] at hdiv
    have h' : ℓ ^ b * ℓ ^ e ∣ ((a - 1) * D') * ℓ ^ e := by
      have : (a - 1) * (ℓ ^ e * D') = ((a - 1) * D') * ℓ ^ e := by ring
      rwa [this] at hdiv
    have h'' := Nat.dvd_of_mul_dvd_mul_right (pow_pos hℓ.pos e) h'
    exact (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hD'ℓ)).dvd_of_dvd_mul_right h''
  obtain ⟨t, ht⟩ := hb
  have hbk : b ≤ k := by omega
  have hξ : IsPrimitiveRoot (ζ ^ ℓ ^ (k - b)) (ℓ ^ b) := by
    have := hζ.pow_of_dvd (p := ℓ ^ (k - b)) (pow_ne_zero _ hℓ.ne_zero)
      (pow_dvd_pow ℓ (Nat.sub_le k b))
    rwa [Nat.pow_div (Nat.sub_le k b) hℓ.pos, Nat.sub_sub_self hbk] at this
  apply hσ0 _ hξ
  rw [map_pow, ha, ← pow_mul]
  have h1 : a = 1 + ℓ ^ b * t := by rw [← ht]; omega
  have h2 : a * ℓ ^ (k - b) = ℓ ^ (k - b) + ℓ ^ k * t := by
    rw [h1, add_mul, one_mul, mul_comm (ℓ ^ b) t, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hbk, mul_comm t]
  rw [h2, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormVal
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normVal :
    NormVal := by
  intro Ω _ _ _ U hU q hq
  classical
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U with hK
  have hfix : K.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  have hfin : FiniteDimensional ℚ K := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hU
  have hq0 : q ≠ 0 := by omega
  have hpp : q.minFac.Prime := Nat.minFac_prime (by omega)
  haveI : Fact q.minFac.Prime := ⟨hpp⟩
  have ha : 0 < padicValNat q.minFac q := by
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd hq0 (Nat.minFac_dvd q)
  refine ⟨Module.finrank ℚ K * padicValNat q.minFac q, Nat.mul_pos Module.finrank_pos ha, ?_⟩
  intro z n c hz hzq
  rcases n with _ | k
  · have h1 : ((q ^ c : ℕ) : Ω) = ((1 : ℕ) : Ω) := by simpa using hzq
    have h2 : q ^ c = 1 := Nat.cast_injective h1
    rcases (Nat.pow_eq_one.1 h2) with h | h
    · omega
    · simp [h]
  have hzK : z ∈ K := (IntermediateField.mem_fixedField_iff U z).2 hz
  set w : K := ⟨z, hzK⟩ with hwdef
  have hw : w ^ (k + 1) * (algebraMap ℚ K (q : ℚ)) ^ c = 1 := by
    apply Subtype.ext
    simpa [hwdef] using hzq
  have hN := congrArg (Algebra.norm ℚ) hw
  rw [map_mul, map_pow, map_pow, Algebra.norm_algebraMap, map_one] at hN
  have hNw : Algebra.norm ℚ w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero k), zero_mul] at hN
    exact zero_ne_one hN
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hv := congrArg (padicValRat q.minFac) hN
  rw [padicValRat.mul (pow_ne_zero _ hNw) (pow_ne_zero _ (pow_ne_zero _ hqQ)),
    padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat.one,
    padicValRat.of_nat] at hv
  have hd : ((k + 1 : ℕ) : ℤ) ∣ ((c * (Module.finrank ℚ K * padicValNat q.minFac q) : ℕ) : ℤ) := by
    refine ⟨-padicValRat q.minFac (Algebra.norm ℚ w), ?_⟩
    rw [Nat.padicValNat_def, Nat.cast_mul, Nat.cast_mul]
    linear_combination hv
  exact Int.natCast_dvd_natCast.1 hd
end

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem unrSplit_holds : UnrSplit :=
  unrSplit_of groupStep (unrCharPP (ordPrime (kumMove moveRoot normVal)) charOrd decPow) (freshSplit freshChar_holds) exFld
    layerOf_holds degOf splitIff

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrField_holds : UpperTheory.Gal.NearKilling.UnrField := UpperTheory.Gal.UnramifiedFromSplittingCriterion.unrSplit_holds
