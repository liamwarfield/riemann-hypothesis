module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigDiag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V
open scoped Pointwise

private theorem orbit_count {G X V : Type} [Group G] [MulAction G X] [Fintype V] (U : Subgroup G) [U.Normal]
    (hU : U.index ≠ 0) (b : X) (p : V → X) (h1 : ∀ v, ∃ γ : G, p v = γ • b)
    (h2 : ∀ g : G, ∃! v, ∃ u ∈ U, g • b = u • p v) :
    ∑ v, U.relIndex (MulAction.stabilizer G (p v)) = U.index := by
  classical
  have hN : U.Normal := inferInstance
  have conj_eq : ∀ γ : G, U.map (MulAut.conj γ).toMonoidHom = U := by
    intro γ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy γ
    · intro hx
      refine ⟨γ⁻¹ * x * γ, ?_, ?_⟩
      · simpa using hN.conj_mem x hx γ⁻¹
      · simp [mul_assoc]
  have hrel : ∀ v, U.relIndex (MulAction.stabilizer G (p v)) =
      U.relIndex (U ⊔ MulAction.stabilizer G b) := by
    intro v
    obtain ⟨γ, hγ⟩ := h1 v
    rw [hγ, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have e := Subgroup.relIndex_map_map (MulAut.conj γ).toMonoidHom U (MulAction.stabilizer G b)
    rw [conj_eq γ] at e
    have hker : (MulAut.conj γ).toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (MulEquiv.injective _)
    rw [e, hker, sup_bot_eq, sup_bot_eq, Subgroup.relIndex_sup_left]
  choose γ hγ using h1
  let F : V → G ⧸ (U ⊔ MulAction.stabilizer G b) := fun v => QuotientGroup.mk (γ v)
  have inj : Function.Injective F := by
    intro v w hvw
    have hm : (γ v)⁻¹ * γ w ∈ U ⊔ MulAction.stabilizer G b := QuotientGroup.eq.mp hvw
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hm
    obtain ⟨a, ha, c, hc, hac⟩ := hm
    have hac' : a * c = (γ v)⁻¹ * γ w := hac
    have hw : γ w = γ v * a * c := by
      rw [mul_assoc, hac', mul_inv_cancel_left]
    have h₁ : γ w • b = (γ v * a * (γ v)⁻¹) • p v := by
      rw [hw, hγ v, mul_smul, MulAction.mem_stabilizer_iff.mp hc, ← mul_smul, inv_mul_cancel_right]
    have h₂ : γ w • b = (1 : G) • p w := by rw [one_smul, hγ w]
    have hu : γ v * a * (γ v)⁻¹ ∈ U := hN.conj_mem a ha (γ v)
    exact (h2 (γ w)).unique ⟨_, hu, h₁⟩ ⟨1, U.one_mem, h₂⟩
  have surj : Function.Surjective F := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨v, ⟨u, hu, e⟩, -⟩ := h2 g
      refine ⟨v, QuotientGroup.eq.mpr ?_⟩
      have hsplit : (γ v)⁻¹ * g = ((γ v)⁻¹ * u * γ v) * ((γ v)⁻¹ * u⁻¹ * g) := by group
      rw [hsplit]
      refine Subgroup.mul_mem_sup ?_ ?_
      · simpa using hN.conj_mem u hu (γ v)⁻¹
      · rw [MulAction.mem_stabilizer_iff]
        rw [hγ v] at e
        simp only [mul_smul, e, inv_smul_smul]
  have hcard : Fintype.card V = (U ⊔ MulAction.stabilizer G b).index := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_eq_of_bijective F ⟨inj, surj⟩
  rw [Finset.sum_congr rfl (fun v _ => hrel v), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    hcard, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

private theorem upl_normal (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L]
    [Algebra L Ω] [IsAbelianGalois ℚ L] : (upl Ω L).Normal := by
  unfold upl
  constructor
  intro n hn g x hx
  obtain ⟨y, hy, hy'⟩ : ∃ y ∈ maximalRealSubfield L, g⁻¹ (algebraMap L Ω x) = algebraMap L Ω y := by
    refine ⟨((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L) x, ?_, ?_⟩
    · intro φ
      exact hx (φ.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom.restrictNormal L).toRingHom)
    · exact (AlgHom.restrictNormal_commutes (g⁻¹ : Ω ≃ₐ[ℚ] Ω).toAlgHom L x).symm
  have hn' := hn y hy
  show (g * n * g⁻¹) (algebraMap L Ω x) = algebraMap L Ω x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hy', hn', ← hy', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

private theorem cycMod_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ l) {s : G ℚ Ω} (hs : s ζ = ζ) : cycMod ℚ Ω l 1 s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  unfold cycMod cycZ
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one]
  change PadicInt.toZModPow 1 ((cyclotomicCharacter Ω l) ((MulSemiringAction.toRingAut (G ℚ Ω) Ω) s)).val = 1
  rw [cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have hl1 : l ^ 1 ≠ 1 := by rw [pow_one]; exact hl.out.one_lt.ne'
  rw [ZMod.val_one'' hl1, pow_one]
  rw [pow_one] at ht
  obtain ⟨i, -, e⟩ := (hζ.isUnit_unit hl.out.ne_zero).eq_pow_of_mem_rootsOfUnity ht
  rw [← e]
  simp [hs]

private theorem val_smul {Ω : Type} [Field Ω] [CharZero Ω] (g : G ℚ Ω) (B : ValuationSubring Ω) (n : ℕ)
    (h : B.valuation (n : Ω) < 1) : (g • B).valuation (n : Ω) < 1 := by
  have key : ∀ (A : ValuationSubring Ω) (x : Ω), x ≠ 0 → (A.valuation x < 1 ↔ x⁻¹ ∉ A) := by
    intro A x hx
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]
  by_cases hn : (n : Ω) = 0
  · rw [hn]
    generalize g • B = C
    haveI : Nontrivial C.ValueGroup := ValuationRing.instNontrivialValueGroup C Ω
    rw [map_zero]
    exact zero_lt_one
  rw [key _ _ hn] at h ⊢
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast]
  exact h

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.Pr.degEq :
    UpperTheory.V.Pr.DegEq := by
  unfold UpperTheory.V.Pr.DegEq
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k a
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAbelianGalois ℚ L := k.ab
  haveI : (upl Ω L).Normal := upl_normal Ω L
  refine ⟨?_, ?_⟩
  · have hgal : galOf ℚ (W.Lp L) Ω = upl Ω L := by
      ext s
      unfold galOf upl
      constructor
      · intro h x hx
        exact h ⟨x, hx⟩
      · intro h x
        exact h x.1 x.2
    have hidx : (upl Ω L).index = Module.finrank ℚ (W.Lp L) := by
      rw [← hgal]
      exact (galEmbTop ℚ (W.Lp L) Ω).2.2
    rw [← hidx]
    unfold Fr.Frame.d
    rw [Finset.sum_congr rfl (fun v _ => k.dv v)]
    refine orbit_count (upl Ω L) (by rw [hidx]; exact Module.finrank_pos.ne') B k.pl ?_ ?_
    · intro v
      obtain ⟨γ, -, h⟩ := k.pl_conj v
      exact ⟨γ, h⟩
    · intro g
      exact k.pl_all (g • B) (val_smul g B l hL.atl)
  · rintro ⟨ζ, hζ⟩
    obtain ⟨g, hg⟩ := k.mu a
    apply hg
    have hsD : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ Dec (k.pl a) := (k.j_range a _).mp ⟨g, rfl⟩
    obtain ⟨γ, -, hγ⟩ := k.pl_conj a
    have hM : B.valuation (M : Ω) < 1 := by
      obtain ⟨t, ht⟩ := hL.dvd
      have h1 : B.valuation ((N * t : ℕ) : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (natCast_mem B _)
      rw [ht, mul_assoc, Nat.cast_mul, map_mul]
      calc B.valuation (l : Ω) * B.valuation ((N * t : ℕ) : Ω) ≤ B.valuation (l : Ω) :=
            mul_le_of_le_one_right' h1
        _ < 1 := hL.atl
    have hM' : (k.pl a).valuation (M : Ω) < 1 := by
      rw [hγ]
      exact val_smul γ B M hM
    have hker : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ η.ker :=
      k.split (k.pl a) hM' (Subgroup.mem_inf.mpr ⟨hsD, (k.j a g).2⟩)
    have hfix : ((k.j a g : upl Ω L) : G ℚ Ω) ∈ galOf ℚ L Ω := by
      rw [k.gal]
      exact Subgroup.mem_inf.mpr ⟨(k.j a g).2, hker⟩
    unfold galOf at hfix
    exact cycMod_one l (hζ.map_of_injective (algebraMap L Ω).injective) (hfix ζ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefEx
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV

private theorem ce_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)

private theorem ce_fin {l : ℕ} [Fact l.Prime] (s : Set (PadicAlgCl l)) (hs : s.Finite) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) := by
  haveI := hs.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

private theorem ce_coef {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x : c.O, x.1 ∈ E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := c.O)
  refine ⟨IntermediateField.adjoin ℚ_[l] (Subtype.val '' (s : Set c.O)), ce_fin _ (s.finite_toSet.image _), fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a b _ hb =>
    rw [SetLike.val_smul, ← algebraMap_smul ℚ_[l] a]
    exact IntermediateField.smul_mem _ hb

private theorem ce_large {l : ℕ} [Fact l.Prime] (L : Type) [Field L] [NumberField L] :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ (τ : L →+* PadicAlgCl l) (x : L), τ x ∈ E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℚ) (M := L)
  refine ⟨IntermediateField.adjoin ℚ_[l] (⋃ τ : L →+* PadicAlgCl l, τ '' (s : Set L)),
    ce_fin _ (Set.finite_iUnion fun τ => s.finite_toSet.image _), fun τ x => ?_⟩
  have hx : x ∈ Submodule.span ℚ (s : Set L) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.2 ⟨τ, y, hy, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ a) hb

theorem UpperTheory.V.Pr.coefEx :
    UpperTheory.V.Pr.CoefEx := by
  intro l _ c L Ω _ _ _ _ _ ka ka' h h'
  haveI : CompactSpace (G L Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[L] Ω))
  haveI : T2Space (G L Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[L] Ω))
  obtain ⟨E₁, f₁, m₁⟩ := ce_char (G L Ω) ka h
  obtain ⟨E₂, f₂, m₂⟩ := ce_char (G L Ω) ka' h'
  obtain ⟨E₃, f₃, m₃⟩ := ce_coef c
  obtain ⟨E₄, f₄, m₄⟩ := ce_large (l := l) L
  obtain ⟨c₁, hc⟩ := UpperTheory.V.X.So.coefOf l ((E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄))
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  haveI : Algebra.IsIntegral ℤ_[l] c₁.O := Algebra.IsIntegral.of_finite ℤ_[l] c₁.O
  have l₁ : E₁ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_left le_sup_left
  have l₂ : E₂ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_left le_sup_right
  have l₃ : E₃ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_right le_sup_left
  have l₄ : E₄ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_right le_sup_right
  have hle : c.O ≤ c₁.O := fun x hx => (hc x).2 ⟨l₃ (m₃ ⟨x, hx⟩),
    ce_norm x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)⟩
  refine ⟨c₁, hle, fun τ x => (hc _).2 ⟨l₄ (m₄ τ x), ce_norm _ ?_⟩, fun g => (hc _).2 ⟨l₁ (m₁ g).1, (m₁ g).2⟩,
    fun g => (hc _).2 ⟨l₂ (m₂ g).1, (m₂ g).2⟩, ?_⟩
  · exact (x.isIntegral_coe.map τ.toIntAlgHom).tower_top
  · let φ : c.O →+* c₁.O := (Subalgebra.inclusion hle).toRingHom
    have hint : φ.IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) φ ?_
      have e : φ.comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c₁.O := (Subalgebra.inclusion hle).comp_algebraMap
      rw [e]
      exact fun x => Algebra.IsIntegral.isIntegral x
    haveI : IsLocalHom φ := hint.isLocalHom (Subalgebra.inclusion_injective hle)
    refine ⟨ResidueField.map φ, fun a b hab => ?_⟩
    rw [ResidueField.map_residue]
    exact congrArg _ (Subtype.ext hab)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefIs
theorem UpperTheory.V.Pr.coefIs :
    UpperTheory.V.Pr.CoefIs := by
  intro l hl c
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, ?_⟩
  have h0 : (l : IsLocalRing.ResidueField c.O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  exact (CharP.charP_iff_prime_eq_zero hl.out).2 h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ValIntLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Pr

section

variable {Ω : Type} [Field Ω]

private theorem val_int_le (A : ValuationSubring Ω) (a : ℤ) : A.valuation (a : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (intCast_mem A a)

private theorem val_dvd (A : ValuationSubring Ω) {a b : ℕ} (h : a ∣ b) (ha : A.valuation (a : Ω) < 1) :
    A.valuation (b : Ω) < 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_lt_one_of_lt_of_le ha (by simpa only [Int.cast_natCast] using val_int_le A (c : ℤ))

private theorem val_prime (A : ValuationSubring Ω) (n : ℕ) (hn : n ≠ 0) (h : A.valuation (n : Ω) < 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ A.valuation (p : Ω) < 1 := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simp only [Nat.cast_one, map_one, lt_self_iff_false] at h
  | prime p hp => exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    rw [Nat.cast_mul, map_mul] at h
    by_cases ha : A.valuation (a : Ω) < 1
    · obtain ⟨p, hp, hd, hv⟩ := iha (left_ne_zero_of_mul hn) ha
      exact ⟨p, hp, hd.mul_right _, hv⟩
    · have h1 : A.valuation (a : Ω) = 1 := le_antisymm (by simpa only [Int.cast_natCast] using val_int_le A (a : ℤ)) (not_lt.1 ha)
      rw [h1, one_mul] at h
      obtain ⟨p, hp, hd, hv⟩ := ihb (right_ne_zero_of_mul hn) h
      exact ⟨p, hp, hd.mul_left _, hv⟩

private theorem val_cop (A : ValuationSubring Ω) {a b : ℕ} (h : a.Coprime b) (ha : A.valuation (a : Ω) < 1) :
    ¬ A.valuation (b : Ω) < 1 := by
  intro hb
  obtain ⟨u, v, e⟩ := Nat.isCoprime_iff_coprime.2 h
  have e' : (a : Ω) * (u : Ω) + (b : Ω) * (v : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) e
    push_cast at this
    rw [← this]; ring
  have h1 : A.valuation ((a : Ω) * (u : Ω) + (b : Ω) * (v : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_lt_of_le ha (val_int_le A u)
    · exact mul_lt_one_of_lt_of_le hb (val_int_le A v)
  rw [e', map_one] at h1
  exact lt_irrefl _ h1

variable [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem algClo (K : Type) [Field K] [NumberField K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem exists_alg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω]
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) : ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  haveI := algClo (Ω := Ω) L
  have h1 : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) _).2 fun f => h (galEmb_mem ℚ L Ω f) x
  choose f hf using h1
  have hi := (algebraMap L Ω).injective
  let g : K →+* L :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun a b => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun a b => hi (by simp [hf]) }
  letI := g.toAlgebra
  exact ⟨_, IsScalarTower.of_algebraMap_eq fun x => (hf x).symm⟩

private theorem discr_over (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois ℚ K] (M : ℕ)
    (h : ∀ B : ValuationSubring Ω, ¬ Ine (F := ℚ) B ≤ galOf ℚ K Ω → B.valuation (M : Ω) < 1)
    (A : ValuationSubring Ω) (hA : A.valuation ((discr K : ℤ) : Ω) < 1) : A.valuation (M : Ω) < 1 := by
  haveI := algClo (Ω := Ω) K
  have hA' : A.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
    rcases Int.natAbs_eq (discr K) with e | e
    · rwa [e, Int.cast_natCast] at hA
    · rwa [e, Int.cast_neg, Valuation.map_neg, Int.cast_natCast] at hA
  obtain ⟨p, hp, hd, hv⟩ := val_prime A _ (Int.natAbs_ne_zero.2 (discr_ne_zero K)) hA'
  by_cases hM : p ∣ M
  · exact val_dvd A hM hv
  exfalso
  refine (CF.unramIff.2.1 K p hp).1 ((CF.unramIff.1 K p hp).2 fun w hw => ?_) (Int.natCast_dvd.2 hd)
  obtain ⟨B, hB⟩ : ∃ B : ValuationSubring Ω, IsPlaceOver B w := exists_isPlaceOver Ω w
  have hpB : B.valuation (p : Ω) < 1 := by
    have := (hB (p : 𝓞 K)).2 hw
    simpa only [map_natCast] using this
  have hI : Ine (F := ℚ) B ≤ galOf ℚ K Ω := by
    by_contra hc
    exact val_cop B ((Nat.Prime.coprime_iff_not_dvd hp).2 hM) hpB (h B hc)
  rw [← CF.ineAbs ℚ K Ω B w hB, eq_bot_iff]
  rintro _ ⟨s, hs, rfl⟩
  refine Subgroup.mem_bot.2 (AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_)
  rw [CF.resTo_commutes]
  exact hI hs x

end

theorem UpperTheory.V.Pr.kaOf :
    UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → UpperTheory.V.Pr.KaOf := by
  intro hC hR Ω _ _ _ l hl ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k
  have hlM : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ¬ A.valuation (l : Ω) < 1 :=
    fun A h h' => h (val_dvd A ((Dvd.intro _ rfl).trans H.dvd) h')
  have hcyc : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, (cycBar L Ω l)⁻¹ s = 1 := by
    intro A hA s hs
    have h1 : cycZ L Ω l s = 1 := (places L Ω l A).2.2.2 hA hs
    simp [cycBar, h1]
  refine ⟨⟨?_, ?_, fun A hA => hcyc A (hlM A hA), 1, fun h => hl.out.one_lt.ne' (Nat.dvd_one.1 h),
    fun A hA s hs => by rw [pow_one]; exact hcyc A hA s hs⟩, fun K _ _ _ hK κ hκ => ?_⟩
  · have h := (hC L Ω l ι).1 (-1) 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    rwa [mul_one, zpow_neg_one] at h
  · intro s s' h
    have h1 : cycBar L Ω l s' = cycBar L Ω l s := by
      change cycBar ℚ Ω l (galEmb ℚ L Ω s') = cycBar ℚ Ω l (galEmb ℚ L Ω s)
      rw [h, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, h1, ← zpow_neg_one, ← zpow_add]
    norm_num
  · have hle : galOf ℚ L Ω ≤ galOf ℚ K Ω := by
      rw [k.gal, hK]
      exact inf_le_right
    obtain ⟨_, _⟩ := exists_alg K L hle
    haveI := algClo (Ω := Ω) K
    haveI := k.ab
    haveI : IsAbelianGalois ℚ K := IsAbelianGalois.tower_bot ℚ K L
    have hI : ∀ (A : ValuationSubring Ω) (s : G L Ω), s ∈ Ine (F := L) A → galEmb K L Ω s ∈ Ine (F := K) A :=
      fun A s hs => ⟨hs.1, hs.2⟩
    refine ⟨κ.comp (galEmb K L Ω), ⟨hR K L Ω l ι κ ⟨hκ.cont, ?_⟩, fun s s' h => ?_, fun A hA s hs => ?_, ?_⟩,
      fun s s' h => ?_⟩
    · obtain ⟨art, Y, a, -, h1, h2, h3, -⟩ := hκ.alg
      exact ⟨art, Y, a, h1, h2, h3⟩
    · rw [show (1 : ℤ) - ((2 : ℕ) : ℤ) = -1 by norm_num, zpow_neg_one]
      exact hκ.conj (galEmb K L Ω s) (galEmb K L Ω s') h
    · exact hκ.unr A (hlM A hA) (fun h => hA (discr_over K M (fun B' hB' => H.ram B' (hK ▸ hB')) A h)) _ (hI A s hs)
    · obtain ⟨m, -, h1, h2⟩ := hκ.ord
      exact ⟨m, h1, fun A hA s hs => h2 A hA _ (hI A s hs)⟩
    · exact congrArg κ (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutPtOf
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.DimOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Component
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component :
    ∀ (Λ T : Type) [CommRing Λ] [IsDomain Λ] [CommRing T] [Algebra Λ T] [Algebra.IsIntegral Λ T], (∀ a : Λ, a ≠ 0 → algebraMap Λ T a ∈ nonZeroDivisors T) → ∀ P ∈ minimalPrimes T, P.comap (algebraMap Λ T) = ⊥ ∧ (∀ p : Ideal Λ, p.IsPrime → ∃ Q : Ideal T, P ≤ Q ∧ Q.IsPrime ∧ Q.comap (algebraMap Λ T) = p) ∧ ringKrullDim (T ⧸ P) = ringKrullDim Λ := by
  intro Λ T _ _ _ _ _ hreg P hP
  have hP' : P.IsPrime := hP.1.1
  have hbot : P.comap (algebraMap Λ T) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
    by_contra hne
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha (hreg a hne)
  refine ⟨hbot, fun p hp => ?_, ?_⟩
  · obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p P (by
      change P.comap (algebraMap Λ T) ≤ p
      rw [hbot]
      exact bot_le)
    exact ⟨Q, hQ, hQp, hQc⟩
  · haveI : FaithfulSMul Λ (T ⧸ P) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro a b hab
      rw [IsScalarTower.algebraMap_apply Λ T (T ⧸ P), IsScalarTower.algebraMap_apply Λ T (T ⧸ P)] at hab
      have hm : Ideal.Quotient.mk P (algebraMap Λ T a) = Ideal.Quotient.mk P (algebraMap Λ T b) := hab
      have h1 : algebraMap Λ T a - algebraMap Λ T b ∈ P := Ideal.Quotient.eq.1 hm
      have h2 : a - b ∈ P.comap (algebraMap Λ T) := by
        rw [Ideal.mem_comap, map_sub]
        exact h1
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at h2
      exact h2
    exact GlobalTheory.ringKrullDim_eq_of_isIntegral Λ (T ⧸ P)
end

theorem UpperTheory.V.Pr.dimOf :
    UpperTheory.V.Pr.DimOf := by
  intro O Λ B _ _ _ _ _ _ _ φ J m ⟨e⟩ hfin htf Z hZ
  haveI : NoZeroDivisors O := IsDomain.to_noZeroDivisors O
  haveI : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  haveI : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsLocalRing O := IsDiscreteValuationRing.toIsLocalRing
  haveI : NoZeroDivisors (MvPowerSeries (Fin m) O) := inferInstance
  haveI : Nontrivial (MvPowerSeries (Fin m) O) := inferInstance
  haveI : IsDomain (MvPowerSeries (Fin m) O) := NoZeroDivisors.to_isDomain _
  haveI : IsDomain Λ := e.toMulEquiv.isDomain
  letI : Algebra Λ (B ⧸ J) := ((Ideal.Quotient.mk J).comp φ).toAlgebra
  haveI : Module.Finite Λ (B ⧸ J) := hfin
  haveI : Algebra.IsIntegral Λ (B ⧸ J) := Algebra.IsIntegral.of_finite Λ (B ⧸ J)
  have hJZ : J ≤ Z := hZ.1.2
  have hZ' := hZ
  rw [Ideal.minimalPrimes_eq_comap] at hZ'
  obtain ⟨P, hP, rfl⟩ := hZ'
  have hnz : ∀ a : Λ, a ≠ 0 → algebraMap Λ (B ⧸ J) a ∈ nonZeroDivisors (B ⧸ J) := by
    intro a ha
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine htf a ha b ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hx
  have h := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component Λ (B ⧸ J) hnz P hP).2.2
  have hq : ringKrullDim (B ⧸ P.comap (Ideal.Quotient.mk J)) = ringKrullDim ((B ⧸ J) ⧸ P) := by
    have hs : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hk : P.comap (Ideal.Quotient.mk J)
        = RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) := by
      ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
    rw [hk]
    exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs)
  show ringKrullDim _ = _
  rw [hq, h, ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameConditionAlt
open IsLocalRing Matrix Polynomial UpperTheory.V.W

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  simp only [GDet.chi, GDet.map, GDet.ofRep]
  rw [Matrix.charpoly]
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Matrix.coe_detMonoidHom]
  congr 1
  simp only [MonoidAlgebra.mapRingHom_single, map_one, GDet.repAlg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_sub, MonoidAlgebra.lift_single]
  refine Matrix.ext fun i k => ?_
  simp [Matrix.charmatrix_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [Matrix.diagonal_apply]
  rfl

private theorem aeval_mapM {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (q : A[X]) :
    f.mapMatrix (aeval M q) = aeval (f.mapMatrix M) (q.map f) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Polynomial.map_add (f := _), hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Polynomial.map_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, RingHom.mapMatrix_apply, apply_ite f]

private theorem aeval_inter {n : ℕ} {K : Type} [CommRing K] (M N Y : Matrix (Fin n) (Fin n) K)
    (h : N * Y = Y * M) (q : K[X]) : aeval N q * Y = Y * aeval M q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial]
    have hpow : N ^ k * Y = Y * M ^ k := by
      induction k with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]
    rw [mul_assoc, hpow, ← mul_assoc, ← mul_assoc, Algebra.commutes]

private theorem key {n : ℕ} {A K F : Type} [CommRing A] [Field K] [Field F] (f : A →+* K) (j : A →+* F)
    (hj : Function.Injective j) (M : Matrix (Fin n) (Fin n) A) (x : A) (c : K) (hc : c ≠ 0) (hx : f x ≠ 1)
    (hM : M.charpoly.map f = (X - C c) ^ n) (Y : Matrix (Fin n) (Fin n) F)
    (hY : j x • (j.mapMatrix M * Y) = Y * j.mapMatrix M) : Y = 0 := by
  classical
  set p := M.charpoly with hp
  set Mf := f.mapMatrix M with hMf
  set Mj := j.mapMatrix M with hMj
  have hint : aeval (j x • Mj) (p.map j) * Y = Y * aeval Mj (p.map j) :=
    aeval_inter Mj (j x • Mj) Y (by rw [smul_mul_assoc]; exact hY) _
  have hCH : aeval Mj (p.map j) = 0 := by
    rw [hp, ← Matrix.charpoly_map]
    exact Matrix.aeval_self_charpoly _
  rw [hCH, mul_zero] at hint
  have hfc : Mf.charpoly = (X - C c) ^ n := by
    rw [hMf, RingHom.mapMatrix_apply, Matrix.charpoly_map]
    exact hM
  set Nl := Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c with hNl
  have hnil : IsNilpotent Nl := by
    refine ⟨n, ?_⟩
    have h0 := Matrix.aeval_self_charpoly Mf
    rw [hfc, map_pow, map_sub, aeval_X, aeval_C] at h0
    exact h0
  set s : K := (f x - 1) * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hx) hc
  have hunitF : IsUnit (aeval (f x • Mf) (p.map f)) := by
    rw [hp, hM, map_pow, map_sub, aeval_X, aeval_C]
    apply IsUnit.pow
    have heq : f x • Mf - algebraMap K (Matrix (Fin n) (Fin n) K) c =
        algebraMap K (Matrix (Fin n) (Fin n) K) s * ((s⁻¹ * f x) • Nl + 1) := by
      rw [← Algebra.smul_def, smul_add, smul_smul, mul_inv_cancel_left₀ hs0, hNl, hs,
        Algebra.algebraMap_eq_smul_one]
      module
    rw [heq]
    exact (IsUnit.map _ (Ne.isUnit hs0)).mul (hnil.smul _).isUnit_add_one
  set D : A := (aeval (x • M) p).det with hD
  have hfD : f D ≠ 0 := by
    have hsm : f.mapMatrix (x • M) = f x • Mf := by
      ext i k
      simp [hMf]
    have h1 : f D = (aeval (f x • Mf) (p.map f)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunitF).ne_zero
  have hD0 : D ≠ 0 := fun h => hfD (by rw [h, map_zero])
  have hjD : (aeval (j x • Mj) (p.map j)).det ≠ 0 := by
    have hsm : j.mapMatrix (x • M) = j x • Mj := by
      ext i k
      simp [hMj]
    have h1 : j D = (aeval (j x • Mj) (p.map j)).det := by
      rw [hD, RingHom.map_det, aeval_mapM, hsm]
    rw [← h1]
    exact fun h => hD0 (hj (by rw [h, map_zero]))
  have hU : IsUnit (aeval (j x • Mj) (p.map j)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hjD)
  exact (hU.mul_right_eq_zero).mp hint

private theorem absolute_irreducible_rank_four {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} {r : Resid F O n} (h : r.V0ok) (y : Point r) : y.N4 := by
  intro X hX
  obtain ⟨-, hchi, g, hg, heps⟩ := h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    ext i
    exact i.elim0
  letI := y.field
  haveI := y.fin
  letI := y.algk
  letI := y.algO
  haveI := y.tower
  let i0 : Fin n := ⟨0, hn⟩
  let z : O := algebraMap ℤ_[l] O (F.ε g)
  let c : y.K := algebraMap (ResidueField O) y.K (r.chib i0 g)
  refine key (PowerSeries.constantCoeff) (algebraMap y.A y.Fr) (IsFractionRing.injective _ _) (mat y.ρ g)
    (algebraMap O y.A z) c ?_ ?_ ?_ X ?_
  · exact (_root_.map_ne_zero _).mpr (Units.ne_zero _)
  · intro h1
    apply heps
    apply Units.ext
    apply (algebraMap (ResidueField O) y.K).injective
    rw [Units.val_one, map_one, ← h1]
    show algebraMap (ResidueField O) y.K (algebraMap O (ResidueField O) z) =
      PowerSeries.constantCoeff (algebraMap O y.A z)
    rw [← IsScalarTower.algebraMap_apply]
    first
    | rfl
    | simp [PowerSeries.algebraMap_apply']
  · have hred := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red
    simp only [Resid.Dbar, chi_map_ofRep] at hred
    rw [hred]
    show Polynomial.map _ (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).charpoly = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hall : ∀ i : Fin n, (Polynomial.X - C (algebraMap (ResidueField O) y.K ↑((r.chib i) g))) =
        Polynomial.X - C c := fun i => by rw [hchi g hg i i0]
    simp only [hall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have := hX g hg
    exact this

theorem UpperTheory.V.Pr.n4Of :
    UpperTheory.V.Pr.EveryPointSatisfiesFrameCondition := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M _ L _ _ _ _ _ Φ k c₁ _ f n ka R y
  exact absolute_irreducible_rank_four R.v0 y
end
