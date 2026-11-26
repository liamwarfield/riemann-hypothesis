module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularUnitsOfRootMemKummerAdjoin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummer
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummer
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory

theorem isPGroup_coatom_normal_index_eq {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (K : Subgroup P) (hK : IsCoatom K) :
    K.Normal ∧ K.index = p := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK
  have hQ : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hidx : K.index ≠ 1 := fun h => hK.1 (Subgroup.index_eq_one.1 h)
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hidx (by rw [Subgroup.index_eq_card, hn, pow_zero])
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have htop : (Subgroup.zpowers x).comap (QuotientGroup.mk' K) = ⊤ := by
    apply hK.2
    refine lt_of_le_of_ne ?_ ?_
    · intro k hk
      have : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      rw [Subgroup.mem_comap, this]
      exact one_mem _
    · intro h
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
      have : y ∈ K := by
        rw [h, Subgroup.mem_comap]
        exact Subgroup.mem_zpowers _
      exact hx1 ((QuotientGroup.eq_one_iff y).2 this)
  have hz : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K z
    have : y ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← hx, ← Nat.card_zpowers, hz, Subgroup.card_top]
  exact ⟨hN, by rw [Subgroup.index_eq_card, hcard]⟩

theorem valuationSubring_galois_stable_of_kummer : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  intro l hl F L _ _ _ _ _ hP hζ W hW
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  let D : Subgroup (L ≃ₐ[F] L) :=
    { carrier := {σ | ∀ x, σ x ∈ W ↔ x ∈ W}
      mul_mem' := by
        intro a b ha hb x
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AlgEquiv.mul_apply, ha, hb]
      one_mem' := by intro x; simp
      inv_mem' := by
        intro a ha x
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (a⁻¹ x)]
        simp }
  suffices hD : D = ⊤ by
    intro τ x
    have hτ : τ ∈ D := hD ▸ Subgroup.mem_top τ
    exact hτ x
  by_contra hD
  obtain ⟨H, hH, hDH⟩ := (eq_top_or_exists_le_coatom D).resolve_left hD
  obtain ⟨hHn, hHi⟩ := isPGroup_coatom_normal_index_eq hP H hH
  haveI : IsGalois F (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  have hfr : Module.finrank F (IntermediateField.fixedField H) = l := by
    have h1 := (letI : Module.Free (IntermediateField.fixedField H) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank F (IntermediateField.fixedField H) L)
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F L,
      ← H.card_mul_index, hHi, mul_comm (Nat.card H)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  haveI : IsCyclic (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H) :=
    isCyclic_of_prime_card (p := l) (by rw [IsGalois.card_aut_eq_finrank, hfr])
  obtain ⟨ζ, hζ⟩ := hζ
  have hK : (primitiveRoots (Module.finrank F (IntermediateField.fixedField H)) F).Nonempty :=
    ⟨ζ, by rw [hfr, mem_primitiveRoots hl.pos]; exact hζ⟩
  obtain ⟨α, ⟨δ, hδ⟩, hα⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic F (IntermediateField.fixedField H) hK
  rw [hfr] at hδ
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h1 : (⊤ : IntermediateField F (IntermediateField.fixedField H)) = ⊥ := by
      rw [← hα]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 (zero_mem _)
    have h2 := congrArg
      (fun E : IntermediateField F (IntermediateField.fixedField H) => Module.finrank F E) h1
    simp only [IntermediateField.finrank_top', IntermediateField.finrank_bot] at h2
    exact hl.one_lt.ne' (hfr ▸ h2)
  have hθ0 : (α : L) ≠ 0 := fun h => hα0 (Subtype.ext h)
  have hθl : (α : L) ^ l ∈ (algebraMap F L).range := by
    refine ⟨δ, ?_⟩
    have := congrArg (fun y : IntermediateField.fixedField H => (y : L)) hδ
    simpa using this
  have hKθ : ∀ x ∈ IntermediateField.fixedField H, x ∈ IntermediateField.adjoin F {(α : L)} := by
    intro x hx
    have hm : x ∈ (IntermediateField.adjoin F {α}).map (IntermediateField.fixedField H).val :=
      ⟨⟨x, hx⟩, by rw [hα]; trivial, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at hm
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∉ H := by
    by_contra h
    exact hH.1 (eq_top_iff.2 fun g _ => by_contra fun hg => h ⟨g, hg⟩)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (IntermediateField.fixedField H) L W (W.comap (τ : L →+* L))
    (fun a => (hW α hθ0 hθl τ a (hKθ a a.2)).symm)
  have hη : σ.restrictScalars F ∈ H := by
    refine (IntermediateField.fixingSubgroup_fixedField H).le ?_
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have hτη : τ * σ.restrictScalars F ∈ D := fun x => hσ x
  exact hτ ((H.mul_mem_cancel_right hη).1 (hDH hτη))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummerStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_valuationSubring_galois_iff_of_kummer_stable : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  first | exact @GlobalTheory.valuationSubring_galois_stable_of_kummer | exact GlobalTheory.valuationSubring_galois_stable_of_kummer | (intros; apply GlobalTheory.valuationSubring_galois_stable_of_kummer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootFFiniteGaloisIsPGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootFFiniteGaloisIsPGroup
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES IntermediateField

noncomputable section

namespace GlobalTheory.KZ.ES.RootGal

theorem exists_adjoin_eq_of_natDegree_le {F E : Type} [Field F] [Field E] [CharZero F] [Algebra F E]
    (L : IntermediateField F E) (B : ℕ) (key : ∀ y ∈ L, IsIntegral F y ∧ (minpoly F y).natDegree ≤ B) :
    ∃ x ∈ L, L ≤ F⟮x⟯ := by
  have hbound : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ B := by
    intro y hy
    rw [adjoin.finrank (key y hy).1]
    exact (key y hy).2
  let D : Set ℕ := {d | ∃ y ∈ L, Module.finrank F F⟮y⟯ = d}
  have hDne : D.Nonempty := ⟨_, 0, L.zero_mem, rfl⟩
  have hDbdd : BddAbove D := ⟨B, by rintro d ⟨y, hy, rfl⟩; exact hbound y hy⟩
  obtain ⟨x, hxL, hxmax⟩ := Nat.sSup_mem hDne hDbdd
  have hle : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ Module.finrank F F⟮x⟯ := by
    intro y hy
    rw [hxmax]
    exact le_csSup hDbdd ⟨y, hy, rfl⟩
  refine ⟨x, hxL, ?_⟩
  intro y hy
  have hx := key x hxL
  have hy' := key y hy
  haveI : FiniteDimensional F F⟮x, y⟯ := finiteDimensional_adjoin (by
    rintro z (rfl | rfl)
    · exact hx.1
    · exact hy'.1)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F F⟮x, y⟯
  have hz : F⟮(α : E)⟯ = F⟮x, y⟯ := by
    simpa only [lift_adjoin_simple, lift_top] using congr_arg lift hα
  have hKL : F⟮x, y⟯ ≤ L := by
    rw [adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact hxL
    · exact hy
  have hxK : F⟮x⟯ ≤ F⟮x, y⟯ := adjoin_simple_le_iff.2 (subset_adjoin F _ (by simp))
  have heq : F⟮x⟯ = F⟮x, y⟯ := by
    apply eq_of_le_of_finrank_le hxK
    rw [← hz]
    exact hle _ (hKL α.2)
  rw [heq]
  exact subset_adjoin F _ (by simp)

theorem aut_eq_one_of_fix {F E : Type} [Field F] [Field E] [Algebra F E] (S : Set E)
    (ρ : adjoin F S ≃ₐ[F] adjoin F S) (h : ∀ x : adjoin F S, (x : E) ∈ S → ρ x = x) : ρ = 1 := by
  ext ⟨x, hx⟩
  congr 1
  change ρ ⟨x, hx⟩ = ⟨x, hx⟩
  induction hx using adjoin_induction with
  | mem x hx => exact h _ hx
  | algebraMap c => exact ρ.commutes c
  | add x y hx hy ihx ihy =>
    change ρ (⟨x, hx⟩ + ⟨y, hy⟩) = ⟨x, hx⟩ + ⟨y, hy⟩
    rw [map_add (f := _), ihx, ihy]
  | inv x hx ihx =>
    change ρ (⟨x, hx⟩⁻¹) = ⟨x, hx⟩⁻¹
    rw [map_inv₀, ihx]
  | mul x y hx hy ihx ihy =>
    change ρ (⟨x, hx⟩ * ⟨y, hy⟩) = ⟨x, hx⟩ * ⟨y, hy⟩
    rw [map_mul, ihx, ihy]

theorem pow_apply_eq_of_fix_pow {F E : Type} [Field F] [Field E] [Algebra F E] (m : ℕ)
    (hμ : ∀ z : E, z ^ m = 1 → z ∈ (algebraMap F E).range) (ρ : E ≃ₐ[F] E) (y : E) (hy : ρ (y ^ m) = y ^ m) :
    (ρ ^ m) y = y := by
  by_cases h0 : y = 0
  · rw [h0, map_zero]
  have h1 : (ρ y / y) ^ m = 1 := by
    rw [div_pow, ← map_pow, hy, div_self (pow_ne_zero _ h0)]
  obtain ⟨c, hc⟩ := hμ _ h1
  have h2 : ρ y = algebraMap F E c * y := by rw [hc, div_mul_cancel₀ _ h0]
  have h3 : ∀ j : ℕ, (ρ ^ j) y = algebraMap F E c ^ j * y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, ρ.commutes, h2]
      ring
  rw [h3, hc, h1, one_mul]

theorem mem_rootSet_field {F E : Type} [Field F] [Field E] [Algebra F E] {p : Polynomial F} (hp : p ≠ 0) (y : E) :
    y ∈ p.rootSet E ↔ Polynomial.aeval y p = 0 := Polynomial.mem_rootSet_of_ne hp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def levSub (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω X.K where
  carrier := {f | Lev X M f}
  mul_mem' := fun ha hb γ hγ => by rw [map_mul, ha γ hγ, hb γ hγ]
  add_mem' := fun ha hb γ hγ => by rw [map_add (f := _), ha γ hγ, hb γ hγ]
  algebraMap_mem' := fun c γ _ => AlgEquiv.commutes _ c
  inv_mem' := fun x hx γ hγ => by rw [map_inv₀, hx γ hγ]

theorem mem_levF (X : Tower Ω ε) (M : ℕ) (y : AlgebraicClosure X.K) :
    y ∈ levF X M ↔ ∃ f, Lev X M f ∧ algebraMap X.K (AlgebraicClosure X.K) f = y := by
  have : levF X M = (levSub X M).map (IsScalarTower.toAlgHom Ω X.K (AlgebraicClosure X.K)) := by
    rw [← adjoin_self Ω ((levSub X M).map _)]; rfl
  rw [this]; rfl

theorem lev_sl (X : Tower Ω ε) {M : ℕ} {f : X.K} (hf : Lev X M f) (γ : SL(2, ℤ)) :
    Lev X M (X.sl (ofSL γ) f) := by
  intro δ hδ
  have h : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← X.sl_mul, ← map_mul, h, map_mul, X.sl_mul, hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)]

theorem charZero_levF (X : Tower Ω ε) (M : ℕ) : CharZero (levF X M) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  exact charZero_of_injective_algebraMap (algebraMap Ω (levF X M)).injective

theorem sl_eq_of_map_eq (X : Tower Ω ε) {M : ℕ} {f : X.K} (hf : Lev X M f) {γ δ : SL(2, ℤ)}
    (h : SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ) :
    X.sl (ofSL γ) f = X.sl (ofSL δ) f := by
  have h1 : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    CongruenceSubgroup.Gamma_mem'.2 (by rw [map_mul, map_inv, h, mul_inv_cancel])
  have h2 : γ = γ * δ⁻¹ * δ := by group
  conv_lhs => rw [h2, map_mul, X.sl_mul, hf _ h1]

theorem exists_orbit_poly (X : Tower Ω ε) (M₀ M : ℕ) (hM : 0 < M) :
    ∃ B : ℕ, ∀ m : ℕ, 0 < m → ∀ f : X.K, Lev X M f → ∃ Q : Polynomial (levF X M₀), Q.Monic ∧ Q.natDegree ≤ B * m ∧
      ∀ y : AlgebraicClosure X.K, Polynomial.aeval y Q = 0 ↔
        ∃ γ ∈ CongruenceSubgroup.Gamma M₀, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) f) := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  let π : SL(2, ℤ) →* SL(2, ZMod M) := SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  refine ⟨Fintype.card SL(2, ZMod M), fun m hm f hf => ?_⟩
  let g : SL(2, ZMod M) → X.K := fun x => X.sl (ofSL (Function.invFun π x)) f
  let S : Finset X.K := (Finset.univ.image g).filter
    (fun c => ∃ γ ∈ CongruenceSubgroup.Gamma M₀, X.sl (ofSL γ) f = c)
  have hS : ∀ c, c ∈ S ↔ ∃ γ ∈ CongruenceSubgroup.Gamma M₀, X.sl (ofSL γ) f = c := by
    intro c
    simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨γ, -, rfl⟩ := h
    exact ⟨π γ, sl_eq_of_map_eq X hf (Function.invFun_eq (f := π) ⟨γ, rfl⟩)⟩
  have hcard : S.card ≤ Fintype.card SL(2, ZMod M) :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))
  let p : Polynomial X.K := ∏ c ∈ S, (Polynomial.X ^ m - Polynomial.C c)
  have hpmon : p.Monic := Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_pow_sub_C c hm.ne'
  have hpdeg : p.natDegree = S.card * m := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun c _ => Polynomial.monic_X_pow_sub_C c hm.ne']
    simp [Polynomial.natDegree_X_pow_sub_C _]
  have hpinv : ∀ δ ∈ CongruenceSubgroup.Gamma M₀, p.map (X.sl (ofSL δ) : X.K →+* X.K) = p := by
    intro δ hδ
    simp only [p, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    have himg : S.image (X.sl (ofSL δ)) = S := by
      ext y
      simp only [Finset.mem_image, hS]
      constructor
      · rintro ⟨z, ⟨γ, hγ, rfl⟩, rfl⟩
        exact ⟨γ * δ, mul_mem hγ hδ, by rw [map_mul, X.sl_mul]⟩
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨_, ⟨γ * δ⁻¹, mul_mem hγ (inv_mem hδ), rfl⟩, by
          rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]⟩
    conv_rhs => rw [← himg]
    rw [Finset.prod_image (fun a _ b _ h => (X.sl (ofSL δ)).injective h)]
    rfl
  have hlift : p.map (algebraMap X.K (AlgebraicClosure X.K)) ∈
      Polynomial.lifts (algebraMap (levF X M₀) (AlgebraicClosure X.K)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine ⟨⟨_, (mem_levF X M₀ _).2 ⟨p.coeff i, fun δ hδ => ?_, rfl⟩⟩, by rw [Polynomial.coeff_map]; rfl⟩
    conv_rhs => rw [← hpinv δ hδ]
    rw [Polynomial.coeff_map]
    rfl
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hpmon.map _)
  refine ⟨q, hqmon, ?_, fun y => ?_⟩
  · rw [hqdeg, Polynomial.natDegree_map, hpdeg]
    exact Nat.mul_le_mul_right _ hcard
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hqmap]
    simp only [p, Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, hS]
    constructor
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, h⟩
      exact ⟨γ, hγ, h⟩
    · rintro ⟨γ, hγ, h⟩
      exact ⟨_, ⟨γ, hγ, rfl⟩, h⟩

theorem exists_primitive (X : Tower Ω ε) (M₀ M : ℕ) (hM : 0 < M) (hd : M₀ ∣ M) :
    ∃ f₀, Lev X M f₀ ∧ ∀ f, Lev X M f → algebraMap X.K (AlgebraicClosure X.K) f ∈
      (levF X M₀)⟮algebraMap X.K (AlgebraicClosure X.K) f₀⟯ := by
  obtain ⟨B, hB⟩ := exists_orbit_poly X M₀ M hM
  have hle : levF X M₀ ≤ levF X M := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := (mem_levF X M₀ y).1 hy
    exact (mem_levF X M _).2 ⟨f, fun γ hγ => hf γ (CongruenceDescent.Gamma_le_of_dvd hd hγ), rfl⟩
  haveI := charZero_levF X M₀
  obtain ⟨θ, hθ, h⟩ := exists_adjoin_eq_of_natDegree_le (extendScalars hle) (B * 1) (by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := (mem_levF X M y).1 hy
    obtain ⟨Q, hQ, hdeg, hroot⟩ := hB 1 one_pos f hf
    have h0 := (hroot (algebraMap X.K (AlgebraicClosure X.K) f)).2
      ⟨1, Subgroup.one_mem _, by rw [pow_one, map_one, X.sl_one]⟩
    exact ⟨⟨Q, hQ, h0⟩, (Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ h0) hQ.ne_zero).trans hdeg⟩)
  obtain ⟨f₀, hf₀, rfl⟩ := (mem_levF X M θ).1 hθ
  exact ⟨f₀, hf₀, fun f hf => h ((mem_levF X M _).2 ⟨f, hf, rfl⟩)⟩

theorem apply_eq_sl (X : Tower Ω ε) (M₀ : ℕ) (E : IntermediateField (levF X M₀) (AlgebraicClosure X.K))
    (τ : E ≃ₐ[levF X M₀] E) (f₀ : X.K) (h₀ : algebraMap X.K (AlgebraicClosure X.K) f₀ ∈ E)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M₀)
    (hτ : (τ ⟨_, h₀⟩ : AlgebraicClosure X.K) = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) f₀))
    (x : AlgebraicClosure X.K) (hx : x ∈ (levF X M₀)⟮algebraMap X.K (AlgebraicClosure X.K) f₀⟯) :
    ∃ (f : X.K) (h : x ∈ E), algebraMap X.K (AlgebraicClosure X.K) f = x ∧
      (τ ⟨x, h⟩ : AlgebraicClosure X.K) = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) f) := by
  induction hx using adjoin_induction with
  | mem x hx =>
    obtain rfl := hx
    exact ⟨f₀, h₀, rfl, hτ⟩
  | algebraMap c =>
    obtain ⟨f, hf, hc⟩ := (mem_levF X M₀ c).1 c.2
    refine ⟨f, E.algebraMap_mem c, hc, ?_⟩
    rw [hf γ hγ, hc]
    exact congrArg Subtype.val (τ.commutes c)
  | add x y _ _ ihx ihy =>
    obtain ⟨f, hx, rfl, h1⟩ := ihx
    obtain ⟨g, hy, rfl, h2⟩ := ihy
    refine ⟨f + g, E.add_mem hx hy, map_add _ _ _, ?_⟩
    rw [map_add (X.sl _), map_add (algebraMap X.K (AlgebraicClosure X.K)) (X.sl _ f), ← h1, ← h2]
    exact congrArg Subtype.val (map_add τ ⟨_, hx⟩ ⟨_, hy⟩)
  | inv x _ ihx =>
    obtain ⟨f, hx, rfl, h1⟩ := ihx
    refine ⟨f⁻¹, E.inv_mem hx, map_inv₀ _ _, ?_⟩
    rw [map_inv₀ (X.sl _), map_inv₀ (algebraMap X.K (AlgebraicClosure X.K)) (X.sl _ f), ← h1]
    exact congrArg Subtype.val (map_inv₀ τ ⟨_, hx⟩)
  | mul x y _ _ ihx ihy =>
    obtain ⟨f, hx, rfl, h1⟩ := ihx
    obtain ⟨g, hy, rfl, h2⟩ := ihy
    refine ⟨f * g, E.mul_mem hx hy, map_mul _ _ _, ?_⟩
    rw [map_mul (X.sl _), map_mul (algebraMap X.K (AlgebraicClosure X.K)) (X.sl _ f), ← h1, ← h2]
    exact congrArg Subtype.val (map_mul τ ⟨_, hx⟩ ⟨_, hy⟩)

theorem algebraMap_mem_rootF (X : Tower Ω ε) (M₀ M m : ℕ) (U : X.K) {f : X.K} (hf : Lev X M f) :
    algebraMap X.K (AlgebraicClosure X.K) f ∈ rootF X M₀ M m U :=
  subset_adjoin _ _ (Or.inl ⟨f, hf, rfl⟩)

theorem exists_isSplittingField (X : Tower Ω ε) (M₀ M m : ℕ) (hM : 0 < M) (hd : M₀ ∣ M) (hm : 0 < m) (U : X.K)
    (hU : Lev X M U) : ∃ Q : Polynomial (levF X M₀), Q.IsSplittingField (levF X M₀) (rootF X M₀ M m U) := by
  obtain ⟨B, hB⟩ := exists_orbit_poly X M₀ M hM
  obtain ⟨f₀, hf₀, hgen⟩ := exists_primitive X M₀ M hM hd
  obtain ⟨Q₁, hQ₁, -, hr₁⟩ := hB 1 one_pos f₀ hf₀
  obtain ⟨Q₂, hQ₂, -, hr₂⟩ := hB m hm U hU
  have hne : Q₁ * Q₂ ≠ 0 := (hQ₁.mul hQ₂).ne_zero
  have hE : rootF X M₀ M m U = adjoin (levF X M₀) ((Q₁ * Q₂).rootSet (AlgebraicClosure X.K)) := by
    apply le_antisymm
    · refine adjoin_le_iff.2 ?_
      rintro y (⟨f, hf, rfl⟩ | hy)
      · refine (adjoin_simple_le_iff.2 (subset_adjoin _ _ ?_)) (hgen f hf)
        refine (mem_rootSet_field hne _).2 ?_
        rw [map_mul, (hr₁ _).2 ⟨1, Subgroup.one_mem _, by rw [pow_one, map_one, X.sl_one]⟩, zero_mul]
      · refine subset_adjoin _ _ ((mem_rootSet_field hne _).2 ?_)
        rw [map_mul, (hr₂ _).2 hy, mul_zero]
    · refine adjoin_le_iff.2 ?_
      intro y hy
      have h := (mem_rootSet_field hne _).1 hy
      rw [map_mul, mul_eq_zero] at h
      rcases h with h | h
      · obtain ⟨γ, -, h⟩ := (hr₁ y).1 h
        rw [pow_one] at h
        rw [h]
        exact algebraMap_mem_rootF X M₀ M m U (lev_sl X hf₀ γ)
      · exact subset_adjoin _ _ (Or.inr ((hr₂ y).1 h))
  refine ⟨Q₁ * Q₂, ?_⟩
  rw [hE]
  exact adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

theorem exists_apply_eq_sl (X : Tower Ω ε) (M₀ M m : ℕ) (hM : 0 < M) (hd : M₀ ∣ M) (U : X.K)
    (τ : rootF X M₀ M m U ≃ₐ[levF X M₀] rootF X M₀ M m U) :
    ∃ γ ∈ CongruenceSubgroup.Gamma M₀, ∀ (j : ℕ) (f : X.K) (hf : Lev X M f),
      ((τ ^ j) ⟨_, algebraMap_mem_rootF X M₀ M m U hf⟩ : AlgebraicClosure X.K) =
        algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL (γ ^ j)) f) := by
  obtain ⟨B, hB⟩ := exists_orbit_poly X M₀ M hM
  obtain ⟨f₀, hf₀, hgen⟩ := exists_primitive X M₀ M hM hd
  obtain ⟨Q₁, hQ₁, -, hr₁⟩ := hB 1 one_pos f₀ hf₀
  have h₀ := algebraMap_mem_rootF X M₀ M m U hf₀
  have h1 : Polynomial.aeval (⟨_, h₀⟩ : rootF X M₀ M m U) Q₁ = 0 := by
    apply (algebraMap (rootF X M₀ M m U) (AlgebraicClosure X.K)).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact (hr₁ _).2 ⟨1, Subgroup.one_mem _, by rw [pow_one, map_one, X.sl_one]; rfl⟩
  have h2 : Polynomial.aeval (τ ⟨_, h₀⟩ : AlgebraicClosure X.K) Q₁ = 0 := by
    have h3 : Polynomial.aeval (τ ⟨_, h₀⟩) Q₁ = 0 := by
      rw [Polynomial.aeval_algHom_apply, h1, map_zero]
    have h4 := congrArg (algebraMap (rootF X M₀ M m U) (AlgebraicClosure X.K)) h3
    rwa [← Polynomial.aeval_algebraMap_apply, map_zero] at h4
  obtain ⟨γ, hγ, h⟩ := (hr₁ _).1 h2
  rw [pow_one] at h
  have hone : ∀ (f : X.K) (hf : Lev X M f),
      τ ⟨_, algebraMap_mem_rootF X M₀ M m U hf⟩ = ⟨_, algebraMap_mem_rootF X M₀ M m U (lev_sl X hf γ)⟩ := by
    intro f hf
    obtain ⟨g, _, hg, h5⟩ := apply_eq_sl X M₀ _ τ f₀ h₀ γ hγ h _ (hgen f hf)
    obtain rfl := (algebraMap X.K (AlgebraicClosure X.K)).injective hg
    exact Subtype.ext h5
  refine ⟨γ, hγ, fun j => ?_⟩
  induction j with
  | zero => intro f hf; rw [pow_zero, pow_zero, map_one, X.sl_one]; rfl
  | succ j ih =>
    intro f hf
    rw [pow_succ, AlgEquiv.mul_apply, hone f hf, ih _ (lev_sl X hf γ), pow_succ', map_mul, X.sl_mul]

theorem rootF_finite_galois_isPGroup : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε), ∀ (l M₀ k n : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∀ U : X.K, Lev X (M₀ * l ^ k) U →
    FiniteDimensional (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧
      IsGalois (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧
      IsPGroup l (rootF X M₀ (M₀ * l ^ k) (l ^ n) U ≃ₐ[levF X M₀] rootF X M₀ (M₀ * l ^ k) (l ^ n) U) := by
  intro Ω _ _ _ ε X l M₀ k n hl hM₀ hd U hU
  have hM : 0 < M₀ * l ^ k := mul_pos hM₀ (pow_pos hl.pos k)
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨Q, hQ⟩ := exists_isSplittingField X M₀ _ _ hM (dvd_mul_right _ _) hm U hU
  haveI := charZero_levF X M₀
  haveI hfin : FiniteDimensional (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) :=
    Polynomial.IsSplittingField.finiteDimensional _ Q
  haveI : Normal (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) := Normal.of_isSplittingField Q
  refine ⟨hfin, isGalois_iff.2 ⟨inferInstance, inferInstance⟩, fun τ => ⟨k + n, ?_⟩⟩
  obtain ⟨γ, hγ, hτ⟩ := exists_apply_eq_sl X M₀ _ _ hM (dvd_mul_right _ _) U τ
  have hfix : ∀ (f : X.K) (hf : Lev X (M₀ * l ^ k) f),
      (τ ^ l ^ k) ⟨_, algebraMap_mem_rootF X M₀ _ (l ^ n) U hf⟩ = ⟨_, algebraMap_mem_rootF X M₀ _ (l ^ n) U hf⟩ := by
    intro f hf
    apply Subtype.ext
    rw [hτ _ f hf, hf _ (CongruenceDescent.pow_pow_mem_Gamma_mul hd hγ k)]
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hμ : ∀ z : rootF X M₀ (M₀ * l ^ k) (l ^ n) U, z ^ l ^ n = 1 →
      z ∈ (algebraMap (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U)).range := by
    intro z hz
    have hz' : (z : AlgebraicClosure X.K) ^ l ^ n = 1 := congrArg Subtype.val hz
    have hint : IsIntegral Ω (z : AlgebraicClosure X.K) :=
      IsIntegral.of_pow hm (by rw [hz']; exact isIntegral_one)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Ω _
      (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
    exact ⟨⟨_, (levF X M₀).algebraMap_mem c⟩, Subtype.ext hc⟩
  rw [pow_add, pow_mul]
  refine aut_eq_one_of_fix _ _ ?_
  rintro ⟨x, hx⟩ (⟨f, hf, rfl⟩ | ⟨δ, -, hδ⟩)
  · refine pow_apply_eq_of_fix_pow _ hμ (τ ^ l ^ k) _ ?_
    exact (map_pow _ _ _).trans (congrArg (· ^ l ^ n) (hfix f hf))
  · refine pow_apply_eq_of_fix_pow _ hμ (τ ^ l ^ k) _ ?_
    have h := hfix _ (lev_sl X hU δ)
    have e : (⟨x, hx⟩ ^ l ^ n : rootF X M₀ (M₀ * l ^ k) (l ^ n) U) =
        ⟨_, algebraMap_mem_rootF X M₀ _ (l ^ n) U (lev_sl X hU δ)⟩ := Subtype.ext hδ
    exact (congrArg _ e).trans (h.trans e.symm)

end GlobalTheory.KZ.ES.RootGal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootFFiniteGaloisIsPGroupStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootF_finiteDimensional_isGalois_isPGroup : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l M₀ k n : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∀ U : X.K, Lev X (M₀ * l ^ k) U → FiniteDimensional (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧ IsGalois (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧ IsPGroup l (rootF X M₀ (M₀ * l ^ k) (l ^ n) U ≃ₐ[levF X M₀] rootF X M₀ (M₀ * l ^ k) (l ^ n) U) := by
  first | exact @GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup | exact GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup | (intros; apply GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPowOfGaussValuationCongrOneAlmostAllPrimes
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.Exact

theorem exists_ext {K L : Type} [Field K] [Field L] (φ : K →+* L) (W : ValuationSubring K) :
    ∃ W' : ValuationSubring L, ∀ x, φ x ∈ W' ↔ x ∈ W := by
  obtain ⟨A, h, hl⟩ := IsLocalRing.exists_factor_valuationRing (φ.comp W.subtype)
  refine ⟨A, fun x => ⟨fun hx => ?_, fun hx => h ⟨x, hx⟩⟩⟩
  by_contra hW
  have hx0 : x ≠ 0 := by rintro rfl; exact hW W.zero_mem
  have hi : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hW
  have hu : IsUnit (((φ.comp W.subtype).codRestrict A.toSubring h) ⟨x⁻¹, hi⟩) :=
    isUnit_iff_exists_inv.2 ⟨⟨φ x, hx⟩, Subtype.ext (by simp [hx0])⟩
  obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.1 (hl.1 _ hu)
  have : (z : K) = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hz
  exact hW (this ▸ z.2)

theorem lt_one_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) {W : ValuationSubring K} {W' : ValuationSubring L}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (x : K) : W'.valuation (φ x) < 1 ↔ W.valuation x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, h, map_eq_zero]

theorem eq_one_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) {W : ValuationSubring K} {W' : ValuationSubring L}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (x : K) : W'.valuation (φ x) = 1 ↔ W.valuation x = 1 := by
  have h1 := lt_one_iff φ h x
  have h2 := h x
  rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff] at h2
  rw [← not_le, ← not_le, not_iff_not] at h1
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

theorem gauss_map {F K L : Type} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] (φ : K →ₐ[F] L)
    {W : ValuationSubring K} {W' : ValuationSubring L} (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (t : K) (V : ValuationSubring F) :
    Gauss (φ t) V W' ↔ Gauss t V W := by
  unfold Gauss
  refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun P => ?_)
  · rw [← φ.commutes, h]
  · rw [Polynomial.aeval_algHom_apply]
    exact imp_congr Iff.rfl (imp_congr Iff.rfl (eq_one_iff (φ : K →+* L) h _))

theorem fix_root {F L : Type} [Field F] [Field L] [Algebra F L] (W : ValuationSubring L) (τ : L ≃ₐ[F] L)
    (hst : ∀ x, τ x ∈ W ↔ x ∈ W) {m : ℕ} (hm : 0 < m) {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (hv : ¬ W.valuation (m : L) < 1) {y : L} (hy : W.valuation (y ^ m - 1) < 1) (hτ : τ (y ^ m) = y ^ m) :
    τ y = y := by
  have hζ' : IsPrimitiveRoot (algebraMap F L ζ) m := hζ.map_of_injective (algebraMap F L).injective
  have hp := congrArg (Polynomial.eval y) (X_pow_sub_C_eq_prod hζ' hm (one_pow m))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod,
    mul_one] at hp
  obtain ⟨i, hi⟩ : ∃ i : ℕ, W.valuation (y - algebraMap F L ζ ^ i) < 1 := by
    by_contra hc
    push Not at hc
    rw [hp, map_prod] at hy
    exact absurd hy (not_lt.2 (Finset.one_le_prod' fun i _ => hc i))
  have hi' := (lt_one_iff (τ : L →+* L) hst _).2 hi
  simp only [RingHom.coe_coe, map_sub, map_pow, AlgEquiv.commutes] at hi'
  have hd : W.valuation (τ y - y) < 1 := by
    have := W.valuation.map_sub_lt hi' hi
    simpa using this
  have hvy : W.valuation y = 1 := by
    have := W.valuation.map_one_add_of_lt hy
    rw [add_sub_cancel, map_pow] at this
    exact (pow_eq_one_iff_of_nonneg zero_le' hm.ne').1 this
  have hy0 : y ≠ 0 := by rintro rfl; simp at hvy
  set z := τ y / y with hz
  have hzm : z ^ m = 1 := by
    rw [hz, div_pow, ← map_pow, hτ, div_self (pow_ne_zero _ hy0)]
  have hz1 : W.valuation (z - 1) < 1 := by
    rw [hz, div_sub_one hy0, map_div₀, hvy, div_one]; exact hd
  have hvz : W.valuation z = 1 := by
    have := W.valuation.map_one_add_of_lt hz1
    rwa [add_sub_cancel] at this
  by_contra hne
  have hz1' : z - 1 ≠ 0 := by
    rw [sub_ne_zero, hz]; intro h; exact hne ((div_eq_one_iff_eq hy0).1 h)
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := geom_sum_mul z m
    rw [hzm, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hz1'
  have hpow : ∀ i : ℕ, W.valuation (1 - z ^ i) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : 1 - z ^ (i + 1) = z * (1 - z ^ i) - (z - 1) := by ring
      rw [e]
      refine W.valuation.map_sub_lt ?_ hz1
      rw [map_mul, hvz, one_mul]; exact ih
  apply hv
  have e : (m : L) = ∑ i ∈ Finset.range m, (1 - z ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact W.valuation.map_sum_lt one_ne_zero fun i _ => hpow i

theorem not_lt_of_coprime {L : Type} [Field L] (W : ValuationSubring L) {q m : ℕ} (h : Nat.Coprime m q)
    (hq : W.valuation (q : L) < 1) : ¬ W.valuation (m : L) < 1 := by
  intro hm
  obtain ⟨a, b, hab⟩ : IsCoprime (m : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : (a : L) * m + (b : L) * q = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → L) hab
  have hi : ∀ c : ℤ, W.valuation (c : L) ≤ 1 := fun c => (W.valuation_le_one_iff _).2 (intCast_mem W c)
  have h1 : W.valuation ((a : L) * m + (b : L) * q) < 1 := by
    refine W.valuation.map_add_lt ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hi a) zero_le' hm
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hi b) zero_le' hq
  rw [e, map_one] at h1
  exact lt_irrefl _ h1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def levK (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω X.K where
  carrier := {f | Lev X M f}
  mul_mem' ha hb γ hγ := by rw [map_mul, ha γ hγ, hb γ hγ]
  add_mem' ha hb γ hγ := by rw [map_add (f := _), ha γ hγ, hb γ hγ]
  algebraMap_mem' c γ _ := AlgEquiv.commutes _ c
  inv_mem' x hx γ hγ := by rw [map_inv₀, hx γ hγ]

theorem mem_levF (X : Tower Ω ε) (M : ℕ) (x : AlgebraicClosure X.K) :
    x ∈ levF X M ↔ ∃ f, Lev X M f ∧ algebraMap X.K (AlgebraicClosure X.K) f = x := by
  refine ⟨fun hx => ?_, fun hx => IntermediateField.subset_adjoin _ _ hx⟩
  have : levF X M ≤ (levK X M).map (IsScalarTower.toAlgHom Ω X.K (AlgebraicClosure X.K)) :=
    IntermediateField.adjoin_le_iff.2 fun z hz => hz
  exact this hx

theorem normal_levF (X : Tower Ω ε) (M : ℕ) : Normal (levF X M) (AlgebraicClosure X.K) := by
  let A := IntermediateField.adjoin Ω {X.jK}
  have hA : A ≤ levK X M := IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 (lev_jK X M))
  haveI : Algebra.IsAlgebraic A X.K := ⟨X.alg_j⟩
  haveI : Algebra.IsAlgebraic A (AlgebraicClosure X.K) := Algebra.IsAlgebraic.trans A X.K _
  let φ : A →+* levF X M := (algebraMap A (AlgebraicClosure X.K)).codRestrict (levF X M)
    fun a => (mem_levF X M _).2 ⟨a, hA a.2, rfl⟩
  haveI : Algebra.IsAlgebraic (levF X M) (AlgebraicClosure X.K) := ⟨fun x =>
    (IsIntegral.map_of_comp_eq φ (RingHom.id _) rfl (Algebra.IsIntegral.isIntegral (R := A) x)).isAlgebraic⟩
  haveI : IsAlgClosure (levF X M) (AlgebraicClosure X.K) := ⟨inferInstance, inferInstance⟩
  infer_instance

theorem lev_mono (X : Tower Ω ε) {M N : ℕ} (h : M ∣ N) {f : X.K} (hf : Lev X M f) : Lev X N f := by
  intro γ hγ
  refine hf γ ?_
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have c1 := congrArg (ZMod.castHom h (ZMod M)) h1
  have c2 := congrArg (ZMod.castHom h (ZMod M)) h2
  have c3 := congrArg (ZMod.castHom h (ZMod M)) h3
  have c4 := congrArg (ZMod.castHom h (ZMod M)) h4
  simp only [map_intCast, map_one, map_zero] at c1 c2 c3 c4
  exact ⟨c1, c2, c3, c4⟩

theorem rootF_le (X : Tower Ω ε) (hst : ∀ (g : GQ) (W : ValuationSubring X.K), X.OverY W →
      X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) (M₀ M m : ℕ) (U : X.Kˣ) (hU : U ∈ X.Un m)
    (x : AlgebraicClosure X.K) (hx : x ∈ rootF X M₀ M m U) :
    x ∈ IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m,
      y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)} := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨f, _, rfl⟩ | ⟨γ, _, hγ⟩
    · exact IntermediateField.algebraMap_mem _ f
    · exact IntermediateField.subset_adjoin _ _ ⟨_, KmapA.un_map X _ (hst (ofSL γ)) m U hU, hγ⟩
  | algebraMap x =>
    obtain ⟨f, _, hf⟩ := (mem_levF X M₀ _).1 x.2
    have := IntermediateField.algebraMap_mem (IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m,
      y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)}) f
    rw [hf] at this
    exact this
  | add x y _ _ hx hy => exact add_mem hx hy
  | inv x _ hx => exact inv_mem hx
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem mem_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    [FiniteDimensional F L] [IsGalois F L] (T : Subfield E) (hT : ∀ a : F, algebraMap F E a ∈ T) (y : L)
    (hy : ∀ τ : L ≃ₐ[F] L, (∀ x : L, (x : E) ∈ T → τ x = x) → τ y = y) : (y : E) ∈ T := by
  let T' : IntermediateField F L := (T.toIntermediateField hT).comap L.val
  have : y ∈ T' := by
    rw [← IsGalois.fixedField_fixingSubgroup T', IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact hy τ fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x hx
  exact this

end GlobalTheory.KZ.ES.Exact


open GlobalTheory.KZ.ES.Exact in
theorem GlobalTheory.KZ.ES.pow_of_gauss_congr_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W : ValuationSubring X.K, Gauss X.jK V W → ∀ (n k : ℕ) (U : X.Kˣ), U ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) U → W.valuation ((U : X.K) - 1) < 1 → ∃ g : X.Kˣ, U = g ^ (l ^ n) := by
  intro Ω _ _ _ ε X hhol l M₀ hl hM₀ hlM
  obtain ⟨S, hS⟩ := GlobalTheory.T.gaussValuation_unique_on_lthRoot_level_fields ε X hhol l M₀ hl hM₀
  refine ⟨insert l S, fun q hq hqS V hqV W hW n k U hU hlev hU1 => ?_⟩
  rw [Finset.mem_insert, not_or] at hqS
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hroot : ∀ m : ℕ, 0 < m → ∃ ζ : levF X M₀, IsPrimitiveRoot ζ m := fun m hm => by
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
    exact ⟨_, hζ.map_of_injective (algebraMap Ω (levF X M₀)).injective⟩
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨W', hW'⟩ := exists_ext (algebraMap X.K (AlgebraicClosure X.K)) W
  have hG : Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W' :=
    (gauss_map (IsScalarTower.toAlgHom Ω X.K (AlgebraicClosure X.K)) hW' X.jK V).2 hW
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.rootF_finiteDimensional_isGalois_isPGroup ε X l M₀ k n hl hM₀ hlM U hlev
  set L := rootF X M₀ (M₀ * l ^ k) (l ^ n) U with hL
  let WL : ValuationSubring L := W'.comap (algebraMap L (AlgebraicClosure X.K))
  have hWL : ∀ x : L, algebraMap L (AlgebraicClosure X.K) x ∈ W' ↔ x ∈ WL := fun x => Iff.rfl
  haveI := normal_levF X M₀
  have hstab : ∀ (τ : L ≃ₐ[levF X M₀] L) (x : L), τ x ∈ WL ↔ x ∈ WL := by
    refine GlobalTheory.T.mem_valuationSubring_galois_iff_of_kummer_stable l hl (levF X M₀) L h3 (hroot l hl.pos) WL ?_
    rintro θ hθ ⟨a, ha⟩ τ x hx
    obtain ⟨f, hf, hfa⟩ := (mem_levF X M₀ _).1 a.2
    have hθf : (θ : AlgebraicClosure X.K) ^ l = algebraMap X.K (AlgebraicClosure X.K) f := by
      rw [hfa]; exact (congrArg Subtype.val ha).symm
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [map_zero] at hθf
      exact hθ (Subtype.ext (pow_eq_zero_iff hl.ne_zero |>.1 hθf))
    have hfU : Units.mk0 f hf0 ∈ X.Un l := GlobalTheory.T.mem_modularUnits_of_root_mem_kummer_adjoin ε X (l ^ n) l hm hl.pos θ _
      (rootF_le X (fun g W hW => (GlobalTheory.T.overAffineJLine_comap_sl_gal ε X ε.injective hhol W hW).1 g) _ _ _ U hU θ θ.2) hθf
    let τ' := τ.liftNormal (AlgebraicClosure X.K)
    let σ : AlgebraicClosure X.K →ₐ[Ω] AlgebraicClosure X.K := (τ'.restrictScalars Ω : _ ≃ₐ[Ω] _)
    have hj : σ (algebraMap X.K (AlgebraicClosure X.K) X.jK) = algebraMap X.K (AlgebraicClosure X.K) X.jK :=
      τ'.commutes ⟨_, (mem_levF X M₀ _).2 ⟨_, lev_jK X M₀, rfl⟩⟩
    have hG2 : Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V (W'.comap σ.toRingHom) := by
      refine (gauss_map σ (W := W'.comap σ.toRingHom) (W' := W') (fun _ => ValuationSubring.mem_comap.symm) _ V).1 ?_
      rw [hj]; exact hG
    have hx' : (x : AlgebraicClosure X.K) ∈ IntermediateField.adjoin (levF X M₀) {(θ : AlgebraicClosure X.K)} := by
      have : L.val x ∈ (IntermediateField.adjoin (levF X M₀) {θ}).map L.val := ⟨x, hx, rfl⟩
      rwa [IntermediateField.adjoin_map, Set.image_singleton] at this
    have key := hS q hq hqS.2 V hqV _ _ hG2 hG θ _ hfU hf hθf x hx'
    rw [ValuationSubring.mem_comap] at key
    rw [← hWL, ← hWL, ← τ.liftNormal_commutes]
    exact key
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap X.K (AlgebraicClosure X.K) U) hm
  have hyL : y ∈ L := IntermediateField.subset_adjoin _ _
    (Or.inr ⟨1, one_mem _, by rw [map_one, X.sl_one]; exact hy⟩)
  obtain ⟨ζ, hζ⟩ := hroot _ hm
  have hqW : W'.valuation (q : AlgebraicClosure X.K) < 1 := by
    have := (lt_one_iff (algebraMap Ω (AlgebraicClosure X.K)) hG.1 q).2 (V.mem_nonunits_iff.1 hqV)
    rwa [map_natCast] at this
  have hqL : WL.valuation (q : L) < 1 := by
    rw [← lt_one_iff _ hWL, map_natCast]; exact hqW
  have hv : ¬ WL.valuation ((l ^ n : ℕ) : L) < 1 :=
    not_lt_of_coprime WL (Nat.Coprime.pow_left n ((Nat.coprime_primes hl hq).2 (Ne.symm hqS.1))) hqL
  have hy1 : WL.valuation ((⟨y, hyL⟩ : L) ^ (l ^ n) - 1) < 1 := by
    rw [← lt_one_iff _ hWL, map_sub, map_pow, map_one]
    have := (lt_one_iff _ hW' _).2 hU1
    rw [map_sub, map_one, ← hy] at this
    exact this
  have hyT : y ∈ (levF X (M₀ * l ^ k)).toSubfield := by
    refine mem_of_fixed L _ (fun a => ?_) ⟨y, hyL⟩ fun τ hτ => ?_
    · obtain ⟨f, hf, hfa⟩ := (mem_levF X M₀ _).1 a.2
      exact (mem_levF X _ _).2 ⟨f, lev_mono X (Dvd.intro _ rfl) hf, hfa⟩
    · refine fix_root WL τ (hstab τ) hm hζ hv hy1 (hτ _ ?_)
      exact (mem_levF X _ _).2 ⟨U, hlev, hy.symm⟩
  obtain ⟨g, -, hg⟩ := (mem_levF X _ _).1 hyT
  have hgU : g ^ (l ^ n) = U := (algebraMap X.K (AlgebraicClosure X.K)).injective (by rw [map_pow, hg, hy])
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hgU
    exact U.ne_zero hgU.symm
  exact ⟨Units.mk0 g hg0, Units.ext (by simp [hgU])⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPowOfGaussValuationCongrOneAlmostAllPrimesStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPow_of_gauss_valuation_congr_one_almost_all_primes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W : ValuationSubring X.K, Gauss X.jK V W → ∀ (n k : ℕ) (U : X.Kˣ), U ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) U → W.valuation ((U : X.K) - 1) < 1 → ∃ g : X.Kˣ, U = g ^ (l ^ n) := by
  first | exact @GlobalTheory.KZ.ES.pow_of_gauss_congr_one | exact GlobalTheory.KZ.ES.pow_of_gauss_congr_one | (intros; apply GlobalTheory.KZ.ES.pow_of_gauss_congr_one <;> assumption)
end
