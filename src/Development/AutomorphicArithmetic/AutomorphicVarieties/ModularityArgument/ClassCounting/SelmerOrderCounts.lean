module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardEQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInvLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.DatEx
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem intValuation_equivOfRingEquiv_apply {F : Type} [Field F] [NumberField F] (e : 𝓞 F ≃+* 𝓞 F)
    (P : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e r) = P.intValuation r := by
  set Q := HeightOneSpectrum.equivOfRingEquiv e P with hQdef
  have hQ : Q.asIdeal = P.asIdeal.map e := by
    rw [hQdef, ← Ideal.comap_symm]
    rfl
  have key : ∀ n : ℕ, Q.intValuation (e r) ≤ WithZero.exp (-(n : ℤ)) ↔
      P.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      hQ, ← Ideal.map_pow, Ideal.apply_mem_of_equiv_iff]
  by_cases hr : r = 0
  · simp [hr]
  have hr' : e r ≠ 0 := by simpa using hr
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Q.intValuation (e r) = WithZero.exp (-(m : ℤ)) :=
    ⟨_, HeightOneSpectrum.intValuation_if_neg _ hr'⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, P.intValuation r = WithZero.exp (-(k : ℤ)) :=
    ⟨_, HeightOneSpectrum.intValuation_if_neg _ hr⟩
  rw [hm, hk] at key ⊢
  have h1 := (key k).2 le_rfl
  have h2 := (key m).1 le_rfl
  rw [WithZero.exp_le_exp] at h1 h2
  have hmk : m = k := by omega
  rw [hmk]

private theorem valuation_equivOfRingEquiv_mapRingEquiv_apply {F : Type} [Field F] [NumberField F] (σ : F ≃+* F)
    (P : HeightOneSpectrum (𝓞 F)) (x : F) :
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ) P).valuation F (σ x) =
      P.valuation F x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have ha : σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ a) := rfl
  have hb : σ (algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv σ b) := rfl
  rw [map_div₀, ha, hb, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_equivOfRingEquiv_apply, intValuation_equivOfRingEquiv_apply]

private theorem ordP_actU_inv_eq_ordP_actP {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (γ : Gal(F/L)) (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)) :
    ordP P (actU γ⁻¹ α) = ordP (actP γ P) α := by
  have h := valuation_equivOfRingEquiv_mapRingEquiv_apply γ.toRingEquiv P ((γ⁻¹ : Gal(F/L)) (α : F))
  have e1 : γ.toRingEquiv ((γ⁻¹ : Gal(F/L)) (α : F)) = α := by
    simp [AlgEquiv.aut_inv]
  rw [e1] at h
  simp only [ordP, actP, actU, Units.coe_map]
  rw [h]
  rfl

private theorem actP_mul_selmer_order_counts {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (σ τ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) : actP (σ * τ) P = actP σ (actP τ P) := by
  apply HeightOneSpectrum.ext
  ext x
  change (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x ∈ P.asIdeal ↔
    (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
      ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) ∈ P.asIdeal
  have : (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm x =
      (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
        ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) := by
    apply RingOfIntegers.ext
    simp
    rw [← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, ← AlgEquiv.aut_inv, mul_inv_rev, AlgEquiv.mul_apply]
  rw [this]

private theorem actP_one_selmer_order_counts {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F]
    (P : HeightOneSpectrum (𝓞 F)) : actP (1 : Gal(F/L)) P = P := by
  apply HeightOneSpectrum.ext
  ext x
  change (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x ∈ P.asIdeal ↔ x ∈ P.asIdeal
  have : (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm x = x := by
    apply RingOfIntegers.ext
    simp
    rw [← AlgEquiv.aut_inv, inv_one, AlgEquiv.one_apply]
  rw [this]

private theorem actU_mul' {L F : Type} [Field L] [Field F] [Algebra L F]
    (σ τ : Gal(F/L)) (α : Fˣ) : actU (σ * τ) α = actU σ (actU τ α) := by
  ext
  simp [actU]

private theorem actU_one' {L F : Type} [Field L] [Field F] [Algebra L F] (α : Fˣ) :
    actU (1 : Gal(F/L)) α = α := by
  ext
  simp [actU]

private theorem ordP_mul' {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (α β : Fˣ) : ordP P (α * β) = ordP P α + ordP P β := by
  have hα : P.valuation F (α : F) ≠ 0 := by simp
  have hβ : P.valuation F (β : F) ≠ 0 := by simp
  simp only [ordP, Units.val_mul, map_mul]
  rw [WithZero.log_mul hα hβ]
  ring

private theorem one_lt_valuation_iff_ordP_neg {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (α : Fˣ) : 1 < P.valuation F (α : F) ↔ ordP P α < 0 := by
  have hw : P.valuation F (α : F) ≠ 0 := by simp
  conv_lhs => rw [← WithZero.exp_log hw]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  simp only [ordP]
  omega

private theorem finite_setOf_ordP_ne_zero {F : Type} [Field F] [NumberField F] (α : Fˣ) :
    {P : HeightOneSpectrum (𝓞 F) | ordP P α ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (α : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((α⁻¹ : Fˣ) : F))).subset ?_
  intro P hP
  have hinv : ordP P α⁻¹ = -ordP P α := by
    have h := ordP_mul' P α α⁻¹
    have h1 : ordP P (1 : Fˣ) = 0 := by simp [ordP]
    rw [mul_inv_cancel, h1] at h
    omega
  simp only [Set.mem_setOf_eq] at hP
  rcases lt_or_gt_of_ne hP with h | h
  · left
    exact (one_lt_valuation_iff_ordP_neg P α).2 h
  · right
    exact (one_lt_valuation_iff_ordP_neg P α⁻¹).2 (by omega)

theorem UpperTheory.V.ZK.Ct.datEx :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ), 2 ≤ a → ∃ D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ), IsDat γ a D := by
  intro L F _ _ _ _ _ γ a ha
  let E := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv γ.toRingEquiv)
  let g : Module.End ℤ (Additive Fˣ) := (MonoidHom.toAdditive (actU γ⁻¹)).toIntLinearMap
  let gI : Module.End ℤ (HeightOneSpectrum (𝓞 F) →₀ ℤ) :=
    (Finsupp.domLCongr E.symm : (HeightOneSpectrum (𝓞 F) →₀ ℤ) ≃ₗ[ℤ] _).toLinearMap
  let dA : Additive Fˣ →+ (HeightOneSpectrum (𝓞 F) →₀ ℤ) :=
    { toFun := fun y => Finsupp.ofSupportFinite (fun P => ordP P (Additive.toMul y))
        (finite_setOf_ordP_ne_zero (Additive.toMul y))
      map_zero' := by
        ext P
        simp [Finsupp.ofSupportFinite_coe, ordP]
      map_add' := by
        intro y z
        ext P
        simp [Finsupp.ofSupportFinite_coe, ordP_mul']
        rfl }
  have hg1 : ∀ α : Fˣ, g (Additive.ofMul α) = Additive.ofMul (actU γ⁻¹ α) := fun α => rfl
  have hgI1 : ∀ (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)),
      (gI 𝔡) P = 𝔡 (actP γ P) := by
    intro 𝔡 P
    simp [gI, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]
    rfl
  have hd1 : ∀ (α : Fˣ) (P : HeightOneSpectrum (𝓞 F)),
      (dA.toIntLinearMap (Additive.ofMul α)) P = ordP P α := by
    intro α P
    rfl
  have hgk : ∀ (k : ℕ) (α : Fˣ), (g ^ k) (Additive.ofMul α) = Additive.ofMul (actU (γ⁻¹ ^ k) α) := by
    intro k
    induction k with
    | zero =>
      intro α
      rw [pow_zero, pow_zero, Module.End.one_apply, actU_one']
    | succ k ih =>
      intro α
      rw [pow_succ, Module.End.mul_apply, hg1, ih, pow_succ, actU_mul']
  have hgIk : ∀ (k : ℕ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (P : HeightOneSpectrum (𝓞 F)),
      ((gI ^ k) 𝔡) P = 𝔡 (actP (γ ^ k) P) := by
    intro k
    induction k with
    | zero =>
      intro 𝔡 P
      rw [pow_zero, pow_zero, Module.End.one_apply, actP_one_selmer_order_counts]
    | succ k ih =>
      intro 𝔡 P
      rw [pow_succ', Module.End.mul_apply, hgI1, ih, pow_succ, actP_mul_selmer_order_counts]
  have hn1 : γ⁻¹ ^ orderOf γ = 1 := by rw [inv_pow, pow_orderOf_eq_one, inv_one]
  have hn2 : γ ^ orderOf γ = 1 := pow_orderOf_eq_one γ
  refine ⟨⟨g, gI, dA.toIntLinearMap, orderOf γ, a, ?_, ?_, ?_, orderOf_pos γ, ha, ?_⟩,
    ⟨rfl, rfl, hg1, hgI1, hd1⟩⟩
  · intro y
    ext P
    rw [hgI1]
    change ordP P (actU γ⁻¹ (Additive.toMul y)) = ordP (actP γ P) (Additive.toMul y)
    exact ordP_actU_inv_eq_ordP_actP γ (Additive.toMul y) P
  · apply LinearMap.ext
    intro y
    rw [Module.End.one_apply]
    have h := hgk (orderOf γ) (Additive.toMul y)
    rw [hn1, actU_one'] at h
    exact h
  · apply LinearMap.ext
    intro 𝔡
    rw [Module.End.one_apply]
    ext P
    rw [hgIk, hn2, actP_one_selmer_order_counts]
  · intro m x hm hx
    ext P
    have h := congrArg (fun f => f P) hx
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h hm
    · simpa using h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInj
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem selInj_delI_inj {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)
    (v : I) (hv : D.delI v = 0) : v = 0 := by
  have h1 : D.gI v = (D.a : ℤ) • v := by
    have h := hv
    simp only [Dat.delI, LinearMap.sub_apply, sub_eq_zero] at h
    rw [h]
    simp
  have hp : ∀ k : ℕ, (D.gI ^ k) v = ((D.a : ℤ) ^ k) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_zsmul, ih, smul_smul, pow_succ, mul_comm]
  have hn := hp D.n
  rw [D.gI_pow] at hn
  change v = _ at hn
  apply D.tf ((D.a : ℤ) ^ D.n - 1) v
  · have h2 : (1 : ℤ) < (D.a : ℤ) ^ D.n := one_lt_pow₀ (by have := D.two_le; omega) D.n_pos.ne'
    omega
  · rw [sub_smul, one_smul, ← hn, sub_self]

private theorem selInj_tors_iff {Y : Type} [AddCommGroup Y] (t : Y) :
    t ∈ Submodule.torsion ℤ Y ↔ ∃ m : ℤ, m ≠ 0 ∧ m • t = 0 := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, h⟩
    exact ⟨m, nonZeroDivisors.ne_zero hm, h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, h⟩

private theorem selInj_mem_mt {Y : Type} [AddCommGroup Y] (l : ℕ) (x : Y) :
    x ∈ mt Y l ↔ ∃ z : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • z + t = x := by
  simp only [Ct.mt, Submodule.mem_sup, LinearMap.mem_range]
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, t, ht, h⟩
    exact ⟨z, t, ht, by simpa using h⟩
  · rintro ⟨z, t, ht, h⟩
    exact ⟨_, ⟨z, rfl⟩, t, ht, by simpa using h⟩

theorem UpperTheory.V.ZK.Ct.selInj :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), ∀ l : ℕ, (l : ℤ) ∣ (D.a : ℤ) - 1 → 0 < l → Finite (D.SelInv l) → Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ Nat.card (D.SelInv l) := by
  intro Y I _ _ D l hl hl0 hfin
  have hdel_apply : ∀ y, D.del y = D.g y - (D.a : ℤ) • y := by
    intro y
    simp [Dat.del]
  have hdelI_apply : ∀ v, D.delI v = D.gI v - (D.a : ℤ) • v := by
    intro v
    simp [Dat.delI]
  have htor : ∀ {y : Y} (m : ℤ), m ≠ 0 → m • y ∈ Submodule.torsion ℤ Y → y ∈ Submodule.torsion ℤ Y := by
    intro y m hm h
    obtain ⟨m', hm', h'⟩ := (selInj_tors_iff _).1 h
    exact (selInj_tors_iff y).2 ⟨m' * m, mul_ne_zero hm' hm, by rw [mul_smul, h']⟩
  have hdt : ∀ t ∈ Submodule.torsion ℤ Y, D.d t = 0 := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact D.tf m _ hm (by rw [← map_zsmul, h, map_zero])
  have hdd : ∀ y, D.d (D.del y) = D.delI (D.d y) := by
    intro y
    rw [hdel_apply, hdelI_apply, map_sub, map_zsmul, D.comm]
  have hdelt : ∀ t ∈ Submodule.torsion ℤ Y, D.del t ∈ Submodule.torsion ℤ Y := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact (selInj_tors_iff _).2 ⟨m, hm, by rw [← map_zsmul, h, map_zero]⟩
  have key : ∀ w : {w : D.W // (l : ℤ) • w = 0}, ∃ u : D.U, Submodule.Quotient.mk u = w.1 ∧
      ∃ y : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • (u : Y) = D.del y + t := by
    rintro ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    refine ⟨u, rfl, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hw
    have hw' : (l : ℤ) • (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y := hw
    obtain ⟨a', ⟨y, rfl⟩, t, ht, h⟩ := Submodule.mem_sup.1 hw'
    exact ⟨y, t, ht, h.symm⟩
  choose u hu y t ht hyt using key
  have hsel : ∀ w, (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) ∈ D.SelInv l := by
    intro w
    obtain ⟨c, hc⟩ := hl
    refine ⟨y w, rfl, ?_, ?_⟩
    · rw [selInj_mem_mt]
      refine ⟨(u w : Y) + c • y w, -t w, neg_mem (ht w), ?_⟩
      rw [smul_add, hyt w, hdel_apply, smul_smul, ← hc, sub_smul, one_smul]
      abel
    · obtain ⟨i, hi⟩ := (u w).2
      refine ⟨i, ?_⟩
      have e := congrArg D.d (hyt w)
      rw [map_zsmul, map_add (f := _), hdt _ (ht w), add_zero, hdd, ← hi] at e
      rw [← sub_eq_zero]
      apply selInj_delI_inj D
      rw [map_sub, map_zsmul, ← e, sub_self]
  let f : {w : D.W // (l : ℤ) • w = 0} → D.SelInv l := fun w => ⟨_, hsel w⟩
  apply Nat.card_le_card_of_injective f
  intro w w' hww
  have hq : (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) = Submodule.Quotient.mk (y w') :=
    congrArg Subtype.val hww
  rw [Submodule.Quotient.eq, selInj_mem_mt] at hq
  obtain ⟨z, t0, ht0, hz⟩ := hq
  apply Subtype.ext
  rw [← hu w, ← hu w', Submodule.Quotient.eq]
  show ((u w : Y) - (u w' : Y)) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
  have e2 : D.del (y w) - D.del (y w') = (l : ℤ) • D.del z + D.del t0 := by
    rw [← map_sub, ← hz, map_add (f := _), map_zsmul]
  have hs : (u w : Y) - u w' - D.del z ∈ Submodule.torsion ℤ Y := by
    refine htor (l : ℤ) (by exact_mod_cast hl0.ne') ?_
    have e : (l : ℤ) • ((u w : Y) - u w' - D.del z) = D.del t0 + (t w - t w') := by
      rw [smul_sub, smul_sub, hyt w, hyt w',
        show D.del (y w) = (l : ℤ) • D.del z + D.del t0 + D.del (y w') by rw [← e2]; abel]
      abel
    rw [e]
    exact add_mem (hdelt t0 ht0) (sub_mem (ht w) (ht w'))
  rw [show (u w : Y) - u w' = D.del z + ((u w : Y) - u w' - D.del z) by abel]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hs
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.EqHomLe
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem actP_actP_inv' {L F : Type} [Field L] [Field F] [Algebra L F] (γ : Gal(F/L))
    (Q : HeightOneSpectrum (𝓞 F)) : actP γ (actP γ⁻¹ Q) = Q := by
  ext x
  change ((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm
    ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) ∈ Q.asIdeal ↔ x ∈ Q.asIdeal
  have : ((RingOfIntegers.mapRingEquiv γ⁻¹.toRingEquiv).symm
      ((RingOfIntegers.mapRingEquiv γ.toRingEquiv).symm x)) = x := by
    apply RingOfIntegers.ext
    simp [RingOfIntegers.mapRingEquiv]
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  rw [this]

private theorem card_addMonoidHom_zmod_le_card (H : Type) [AddCommGroup H] [Finite H] (q : ℕ) [NeZero q] :
    Nat.card (H →+ ZMod q) ≤ Nat.card H := by
  have : Fintype H := Fintype.ofFinite H
  have hinj : Function.Injective (fun ψ : H →+ ZMod q => ZMod.stdAddChar.compAddMonoidHom ψ) := by
    intro ψ₁ ψ₂ h
    ext x
    have := DFunLike.congr_fun h x
    simp only [AddChar.compAddMonoidHom_apply] at this
    exact ZMod.injective_stdAddChar this
  calc Nat.card (H →+ ZMod q) ≤ Nat.card (AddChar H ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card H := by rw [Nat.card_eq_fintype_card, AddChar.card_eq, Nat.card_eq_fintype_card]

private theorem card_addMonoidHom_zmod_prime_pow_le_pow_factorization (G : Type) [AddCommGroup G] [Finite G] (l ν : ℕ) (hl : l.Prime) :
    Nat.card (G →+ ZMod (l ^ ν)) ≤ l ^ (Nat.card G).factorization l := by
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hcop : l.Coprime (Nat.card G / l ^ (Nat.card G).factorization l) := Nat.coprime_ordCompl hl hn0
  have hnm := Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) l
  set e := (Nat.card G).factorization l
  set m := Nat.card G / l ^ e
  let H := (nsmulAddMonoidHom (α := G) m).range
  haveI : Finite (H →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective
  have hres : Function.Injective (fun ψ : G →+ ZMod (l ^ ν) => ψ.comp H.subtype) := by
    intro ψ₁ ψ₂ h
    ext x
    have hx : ψ₁ (m • x) = ψ₂ (m • x) := by
      have := DFunLike.congr_fun h ⟨m • x, x, rfl⟩
      simpa using this
    rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hx
    have hu : IsUnit ((m : ZMod (l ^ ν))) :=
      (ZMod.unitOfCoprime m (Nat.Coprime.pow_left ν hcop).symm).isUnit
    exact hu.mul_left_cancel hx
  have h1 : Nat.card (G →+ ZMod (l ^ ν)) ≤ Nat.card (H →+ ZMod (l ^ ν)) :=
    Nat.card_le_card_of_injective _ hres
  have h2 := card_addMonoidHom_zmod_le_card H (l ^ ν)
  have hkill : ∀ h : H, (l ^ e) • h = 0 := by
    rintro ⟨_, x, rfl⟩
    apply Subtype.ext
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, nsmulAddMonoidHom_apply]
    rw [smul_smul, hnm]
    exact card_nsmul_eq_zero'
  have hcopH : (Nat.card H).Coprime m := by
    apply Nat.coprime_of_dvd
    intro k hk hkH hkm
    haveI := Fact.mk hk
    obtain ⟨h, hh⟩ := exists_prime_addOrderOf_dvd_card' k hkH
    have hk' : k ∣ l ^ e := hh ▸ addOrderOf_dvd_of_nsmul_eq_zero (hkill h)
    have : k = l := (Nat.prime_dvd_prime_iff_eq hk hl).1 (hk.dvd_of_dvd_pow hk')
    subst this
    exact (Nat.Prime.coprime_iff_not_dvd hk).1 hcop hkm
  have hdvd : Nat.card H ∣ l ^ e := by
    have := AddSubgroup.card_addSubgroup_dvd_card H
    rw [← hnm] at this
    exact hcopH.dvd_of_dvd_mul_right this
  exact h1.trans (h2.trans (Nat.le_of_dvd (pow_pos hl.pos _) hdvd))

theorem UpperTheory.V.ZK.Ct.eqHomLe :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a l ν : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), l.Prime → IsDat γ a D → Finite D.ClQ → Finite (EqHom γ a (l ^ ν)) ∧ Nat.card (EqHom γ a (l ^ ν)) ≤ l ^ (Nat.card D.ClQ).factorization l := by
  classical
  intro L F _ _ _ _ _ γ a l ν D hl hD hfin
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hinv : ∀ Q, actP γ⁻¹ (actP γ Q) = Q := fun Q => by
    simpa using actP_actP_inv' γ⁻¹ Q
  have hsingle : ∀ (P : HeightOneSpectrum (𝓞 F)) (n : ℤ),
      D.gI (Finsupp.single P n) = Finsupp.single (actP γ⁻¹ P) n := by
    intro P n
    ext Q
    rw [hD.gI_eq, Finsupp.single_apply, Finsupp.single_apply]
    have hiff : (P = actP γ Q) ↔ (actP γ⁻¹ P = Q) :=
      ⟨fun h => h ▸ hinv Q, fun h => h ▸ (actP_actP_inv' γ P).symm⟩
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  let ψ0 : (HeightOneSpectrum (𝓞 F) → ZMod (l ^ ν)) → ((HeightOneSpectrum (𝓞 F) →₀ ℤ) →+ ZMod (l ^ ν)) :=
    fun φ => Finsupp.liftAddHom fun P => (AddMonoidHom.mulRight (φ P)).comp (Int.castAddHom (ZMod (l ^ ν)))
  have hψs : ∀ φ P (n : ℤ), ψ0 φ (Finsupp.single P n) = (n : ZMod (l ^ ν)) * φ P := by
    intro φ P n
    simp [ψ0]
  have hle : ∀ φ ∈ EqHom γ a (l ^ ν),
      LinearMap.range D.d ⊔ LinearMap.range D.delI ≤ LinearMap.ker (ψ0 φ).toIntLinearMap := by
    intro φ hφ
    apply sup_le
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]
      have h1 := hφ.1 (Additive.toMul y)
      rw [← h1]
      simp only [ψ0, Finsupp.liftAddHom_apply, Finsupp.sum]
      rw [finsum_eq_sum_of_support_subset]
      · apply Finset.sum_congr rfl
        intro P _
        simp [← hD.d_eq]
      · intro P hP
        rw [Function.mem_support] at hP
        rw [Finset.mem_coe, Finsupp.mem_support_iff]
        intro h0
        apply hP
        rw [← hD.d_eq]
        simp [h0]
    · have key : ∀ 𝔡, ψ0 φ (D.gI 𝔡) = (a : ZMod (l ^ ν)) * ψ0 φ 𝔡 := by
        intro 𝔡
        induction 𝔡 using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add (f := _), map_add (f := _), map_add (f := _), hf, hg, mul_add]
        | single P n =>
          rw [hsingle, hψs, hψs, hφ.2 P]
          ring
      rintro _ ⟨𝔡, rfl⟩
      rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap]
      simp only [Dat.delI, LinearMap.sub_apply, map_sub, key, hD.a_eq]
      simp
  let f : EqHom γ a (l ^ ν) → (D.ClQ →+ ZMod (l ^ ν)) := fun φ =>
    ((LinearMap.range D.d ⊔ LinearMap.range D.delI).liftQ (ψ0 φ.1).toIntLinearMap (hle φ.1 φ.2)).toAddMonoidHom
  have hf : Function.Injective f := by
    intro φ₁ φ₂ h
    apply Subtype.ext
    funext P
    have := DFunLike.congr_fun h (Submodule.Quotient.mk (Finsupp.single P 1))
    simpa [f, hψs] using this
  haveI : Finite (D.ClQ →+ ZMod (l ^ ν)) := Finite.of_injective _ DFunLike.coe_injective
  refine ⟨Finite.of_injective f hf, ?_⟩
  exact (Nat.card_le_card_of_injective f hf).trans (card_addMonoidHom_zmod_prime_pow_le_pow_factorization D.ClQ l ν hl)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CountOrdP
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct
open scoped nonZeroDivisors

private theorem fractionalIdeal_count_spanSingleton_eq_ordP {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    FractionalIdeal.count F P (FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F)) = ordP P x := by
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (𝓞 F) (x : F)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hrs
    exact x.ne_zero hrs.symm
  have hI : FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) s)⁻¹ * ↑(Ideal.span {r}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hrs, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined F P (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact x.ne_zero) hI]
  unfold ordP
  rw [← hrs, map_div₀]
  erw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.intValuation_if_neg _ hr0, HeightOneSpectrum.intValuation_if_neg _ hs0,
    ← WithZero.exp_sub, WithZero.log_exp]
  ring

theorem UpperTheory.V.ZK.Ct.clFin :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsDat γ a D → Finite ((HeightOneSpectrum (𝓞 F) →₀ ℤ) ⧸ LinearMap.range D.d) := by
  intro L F _ _ _ _ _ γ a D hD
  classical
  obtain ⟨I, hI⟩ : ∃ I : (HeightOneSpectrum (𝓞 F) →₀ ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      ∀ e P, FractionalIdeal.count F P (I e : FractionalIdeal (𝓞 F)⁰ F) = e P :=
    ⟨fun e => Units.mk0 (e.prod fun P n => ((P.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ^ n)
      (Finset.prod_ne_zero_iff.mpr fun P _ =>
        zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)),
      fun e P => FractionalIdeal.count_finsuppProd F P e⟩
  have key : ∀ e e', ClassGroup.mk F (I e) = ClassGroup.mk F (I e') → e - e' ∈ LinearMap.range D.d := by
    intro e e' h
    have h' : ClassGroup.mk F (I e * (I e')⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.1 h').principal
    have hJ : ((I e * (I e')⁻¹ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [FractionalIdeal.spanSingleton_zero] at hJ
      exact Units.ne_zero _ hJ
    refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
    ext P
    rw [hD.d_eq, Finsupp.coe_sub, Pi.sub_apply, ← hI e P, ← hI e' P, ← fractionalIdeal_count_spanSingleton_eq_ordP, Units.val_mk0, ← hJ,
      Units.val_mul, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_mul F P (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)),
      FractionalIdeal.count_inv]
    ring
  refine Finite.of_injective (fun q => ClassGroup.mk F (I (Quotient.out q))) ?_
  intro q1 q2 h
  rw [← Submodule.Quotient.mk_out q1, ← Submodule.Quotient.mk_out q2]
  exact (Submodule.Quotient.eq _).2 (key _ _ h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardKerEqCoker
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section SlopeTestRemainingChoices

variable {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)

private theorem delI_inj : Function.Injective D.delI := by
  refine (injective_iff_map_eq_zero D.delI).2 fun z hz => ?_
  have hg : D.gI z = D.a • z := by
    simp [Dat.delI, sub_eq_zero] at hz
    exact hz
  have hk : ∀ k : ℕ, (D.gI ^ k) z = (D.a ^ k) • z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_nsmul, hg, smul_smul, ← pow_succ]
  have h1 := hk D.n
  rw [D.gI_pow, Module.End.one_apply] at h1
  have ha : (2 : ℤ) ≤ D.a := by exact_mod_cast D.two_le
  have hp : (2 : ℤ) ^ 1 ≤ (D.a : ℤ) ^ D.n :=
    le_trans (pow_le_pow_right₀ (by norm_num) D.n_pos) (pow_le_pow_left₀ (by norm_num) ha _)
  have hne : (D.a : ℤ) ^ D.n - 1 ≠ 0 := by
    norm_num at hp
    omega
  have hc : ((D.a : ℤ) ^ D.n) • z = (D.a ^ D.n) • z := by
    rw [← Nat.cast_pow, natCast_zsmul]
  refine D.tf _ z hne ?_
  rw [sub_smul, one_smul, hc, ← h1, sub_self]

private theorem d_del (y : Y) : D.d (D.del y) = D.delI (D.d y) := by
  simp [Dat.del, Dat.delI, D.comm]

private theorem d_tors {t : Y} (ht : t ∈ Submodule.torsion ℤ Y) : D.d t = 0 := by
  obtain ⟨m, hm⟩ := (Submodule.mem_torsion_iff t).1 ht
  have hm' : (m : ℤ) • t = 0 := hm
  refine D.tf m _ (nonZeroDivisors.coe_ne_zero m) ?_
  rw [← map_zsmul, hm', map_zero]

private theorem card_ker_eq_coker {C : Type} [AddCommGroup C] [Finite C] (f : C →ₗ[ℤ] C) :
    Nat.card (LinearMap.ker f) = Nat.card (C ⧸ LinearMap.range f) := by
  have h1 : Nat.card C = Nat.card (C ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
  have h2 : Nat.card C = Nat.card (C ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range f).toAddSubgroup
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (h2.trans (mul_comm _ _)))

private theorem exists_psi : ∃ ψ : D.U →ₗ[ℤ] I, ∀ u : D.U, D.delI (ψ u) = D.d u := by
  let e := LinearEquiv.ofInjective D.delI (delI_inj D)
  let c : D.U →ₗ[ℤ] LinearMap.range D.delI :=
    (D.d ∘ₗ D.U.subtype).codRestrict (LinearMap.range D.delI) (fun u => u.2)
  refine ⟨e.symm.toLinearMap ∘ₗ c, fun u => ?_⟩
  have h := LinearEquiv.ofInjective_apply D.delI (h := delI_inj D) (e.symm (c u))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end SlopeTestRemainingChoices

theorem UpperTheory.V.ZK.Ct.cardW :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), Finite (I ⧸ LinearMap.range D.d) → Finite D.EQ → Finite D.ClQ ∧ Finite D.W ∧ Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
  intro Y I _ _ D hC hE
  obtain ⟨ψ, hψ⟩ := exists_psi D
  have hψ0 : ∀ u : D.U, D.d u = 0 → ψ u = 0 := fun u hu =>
    delI_inj D (by rw [hψ, hu, map_zero])
  let S := (LinearMap.range D.del ⊔ Submodule.torsion ℤ Y).submoduleOf D.U
  let p := LinearMap.range D.d
  have hpf : p ≤ p.comap D.delI := by
    rintro _ ⟨y, rfl⟩
    exact ⟨D.del y, d_del D y⟩
  let f : (I ⧸ p) →ₗ[ℤ] (I ⧸ p) := p.mapQ p D.delI hpf
  let φ : D.U →ₗ[ℤ] I ⧸ p := p.mkQ ∘ₗ ψ
  have hSφ : S ≤ LinearMap.ker φ := by
    intro u hu
    change (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y at hu
    obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 hu
    have hy : ψ u = D.d y :=
      delI_inj D (by rw [hψ, ← hat, map_add (f := _), d_tors D ht, add_zero, d_del])
    change p.mkQ (ψ u) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hy]
    exact LinearMap.mem_range_self _ _
  let φb : D.W →ₗ[ℤ] I ⧸ p := S.liftQ φ hSφ
  have hkU : LinearMap.ker D.d ≤ D.U := fun y hy => by
    change D.d y ∈ LinearMap.range D.delI
    rw [LinearMap.mem_ker.1 hy]
    exact zero_mem _
  let ι : LinearMap.ker D.d →ₗ[ℤ] D.W := S.mkQ ∘ₗ Submodule.inclusion hkU
  have hrange : LinearMap.range φb = LinearMap.ker f := by
    show LinearMap.range (S.liftQ φ hSφ) = LinearMap.ker f
    rw [Submodule.range_liftQ]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      change (Submodule.Quotient.mk (D.delI (ψ u)) : I ⧸ p) = 0
      rw [hψ, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self _ _
    · intro hx
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p x
      rw [LinearMap.mem_ker] at hx
      change (Submodule.Quotient.mk (D.delI x) : I ⧸ p) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy⟩ := hx
      have hyU : y ∈ D.U := ⟨x, hy.symm⟩
      have hψy : ψ ⟨y, hyU⟩ = x := delI_inj D (by rw [hψ]; exact hy)
      refine ⟨⟨y, hyU⟩, ?_⟩
      show p.mkQ (ψ ⟨y, hyU⟩) = p.mkQ x
      rw [hψy]
  have hker : LinearMap.ker φb = LinearMap.range ι := by
    ext w
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective S w
    constructor
    · intro hu
      rw [LinearMap.mem_ker] at hu
      change p.mkQ (ψ u) = 0 at hu
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
      obtain ⟨y, hy⟩ := hu
      have hk : (u : Y) - D.del y ∈ LinearMap.ker D.d := by
        rw [LinearMap.mem_ker, map_sub, d_del, hy, ← hψ, sub_self]
      refine ⟨⟨_, hk⟩, ?_⟩
      change S.mkQ (Submodule.inclusion hkU ⟨_, hk⟩) = S.mkQ u
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      change ((u : Y) - D.del y - u) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
      rw [sub_sub_cancel_left]
      exact Submodule.mem_sup_left (Submodule.neg_mem _ (LinearMap.mem_range_self _ _))
    · rintro ⟨k, hk⟩
      rw [LinearMap.mem_ker, ← hk]
      have hk0 : ψ (Submodule.inclusion hkU k) = 0 := hψ0 _ k.2
      change p.mkQ (ψ (Submodule.inclusion hkU k)) = 0
      rw [hk0, map_zero]
  have hkerι : LinearMap.ker ι = (Submodule.map D.del (LinearMap.ker D.d) ⊔
      Submodule.torsion ℤ Y).submoduleOf (LinearMap.ker D.d) := by
    ext k
    rw [LinearMap.mem_ker]
    change S.mkQ (Submodule.inclusion hkU k) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (k : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y ↔
      (k : Y) ∈ Submodule.map D.del (LinearMap.ker D.d) ⊔ Submodule.torsion ℤ Y
    constructor
    · intro h
      obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      have hy : D.d y = 0 := by
        apply delI_inj D
        rw [map_zero, ← d_del]
        have hk := k.2
        rw [LinearMap.mem_ker, ← hat, map_add (f := _), d_tors D ht, add_zero] at hk
        exact hk
      exact Submodule.mem_sup.2 ⟨D.del y, ⟨y, hy, rfl⟩, t, ht, hat⟩
    · intro h
      obtain ⟨a, ⟨y, -, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      exact Submodule.mem_sup.2 ⟨D.del y, LinearMap.mem_range_self _ _, t, ht, hat⟩
  haveI : Finite (I ⧸ p) := hC
  haveI : Finite D.EQ := hE
  have hr : LinearMap.range f = Submodule.map p.mkQ (LinearMap.range D.delI) :=
    calc LinearMap.range f = LinearMap.range (f ∘ₗ p.mkQ) :=
          (LinearMap.range_comp_of_range_eq_top f (Submodule.range_mkQ p)).symm
      _ = LinearMap.range (p.mkQ ∘ₗ D.delI) := by rw [Submodule.mapQ_mkQ]
      _ = Submodule.map p.mkQ (LinearMap.range D.delI) := LinearMap.range_comp _ _
  have hQ : Finite ((I ⧸ p) ⧸ Submodule.map p.mkQ (LinearMap.range D.delI)) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hClQ : Finite D.ClQ :=
    Finite.of_equiv _ (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv
  have hcoker : Nat.card D.ClQ = Nat.card ((I ⧸ p) ⧸ LinearMap.range f) := by
    rw [hr]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv.symm
  have hkf := card_ker_eq_coker f
  have hEQ : Nat.card D.EQ = Nat.card (LinearMap.range ι) :=
    Nat.card_congr ((Submodule.quotEquivOfEq _ _ hkerι.symm).trans ι.quotKerEquivRange).toEquiv
  have hW : Nat.card D.W = Nat.card (D.W ⧸ LinearMap.ker φb) * Nat.card (LinearMap.ker φb) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φb).toAddSubgroup
  have hmain : Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
    rw [hW, Nat.card_congr φb.quotKerEquivRange.toEquiv, hrange, hkf, ← hcoker, hker, ← hEQ]
    exact mul_comm _ _
  have hne : Nat.card D.W ≠ 0 := by
    rw [hmain]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  exact ⟨hClQ, Nat.finite_of_card_ne_zero hne, hmain⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.ActUPow
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem dat_g_pow_apply_ofMul_eq_actU_inv_pow {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hD : IsDat γ a D)
    (k : ℕ) (α : Fˣ) :
    (D.g ^ k) (Additive.ofMul α) = Additive.ofMul (actU (γ⁻¹ ^ k) α) := by
  induction k generalizing α with
  | zero => simp [actU]; rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, hD.g_eq, ih]
    congr 1

private theorem dat_nm_apply_ofMul_eq_ofMul_nrm {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)) (hD : IsDat γ a D)
    (α : Fˣ) :
    D.nm (Additive.ofMul α) = Additive.ofMul (nrm γ a α) := by
  simp only [Dat.nm, LinearMap.sum_apply, LinearMap.smul_apply, nrm, ofMul_prod, ofMul_pow, hD.n_eq,
    hD.a_eq, dat_g_pow_apply_ofMul_eq_actU_inv_pow γ a D hD]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ orderOf γ := (Finset.mem_range.mp hj).le
  have hinv : (γ⁻¹) ^ (orderOf γ - j) = γ ^ j := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.sub_add_cancel hj', pow_orderOf_eq_one]
  rw [hinv]
  push_cast
  exact natCast_zsmul _ _

theorem UpperTheory.V.ZK.Ct.fewLe :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a s q B : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsDat γ a D → Few γ a s q B → ∀ f : D.W →ₗ[ℤ] Additive Fˣ ⧸ mt (Additive Fˣ) q, (∀ y : D.U, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((s : ℤ) • D.nm y)) → Finite D.W → Nat.card (LinearMap.range f) ≤ B := by
  intro L F _ _ _ _ _ γ a s q B D hD hF f hf hW
  classical
  haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict
  haveI := Fintype.ofFinite (LinearMap.range f)
  choose w hw using fun z : LinearMap.range f => LinearMap.mem_range.mp z.2
  choose u hu using fun z : LinearMap.range f => Submodule.Quotient.mk_surjective _ (w z)
  have hφ : ∀ z, f (Submodule.Quotient.mk (u z)) = z := by
    intro z
    rw [hu, hw]
  let φ : LinearMap.range f → Fˣ := fun z => Additive.toMul ((u z : D.U) : Additive Fˣ)
  have hinj : Function.Injective φ := by
    intro z z' h
    have h' : u z = u z' := Subtype.ext (Additive.toMul.injective h)
    apply Subtype.ext
    rw [← hφ z, ← hφ z', h']
  have key := hF (Finset.univ.image φ) ?_ ?_
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card] at key
    exact key
  · intro α hα
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨𝔡, h𝔡⟩ := LinearMap.mem_range.mp (u z).2
    refine ⟨𝔡, fun P => ?_⟩
    have hP := congrArg (fun x => x P) h𝔡
    have hd : ordP P (φ z) = D.d ((u z : D.U) : Additive Fˣ) P := (hD.d_eq _ P).symm
    rw [hd, ← hP]
    simp [Dat.delI, hD.gI_eq, hD.a_eq]
  · intro α hα α' hα' ⟨δ, hδ⟩
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp hα'
    congr 1
    apply Subtype.ext
    rw [← hφ z, ← hφ z', hf, hf, Submodule.Quotient.eq]
    apply Submodule.mem_sup_left
    refine LinearMap.mem_range.mpr ⟨Additive.ofMul δ, ?_⟩
    have e := congrArg Additive.ofMul hδ
    rw [ofMul_mul, ofMul_pow, ofMul_pow, ofMul_pow] at e
    have e1 := dat_nm_apply_ofMul_eq_ofMul_nrm γ a D hD (φ z)
    have e2 := dat_nm_apply_ofMul_eq_ofMul_nrm γ a D hD (φ z')
    change D.nm (u z : Additive Fˣ) = _ at e1
    change D.nm (u z' : Additive Fˣ) = _ at e2
    rw [e1, e2, natCast_zsmul, natCast_zsmul, e]
    simp
end

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

theorem UpperTheory.V.ZK.sCount :
    UpperTheory.V.ZK.SCount := by
  intro L F _ _ _ _ _ hTC l c ν E b B _ ζ γ hL hE hF
  have hl : l.Prime := Fact.out
  obtain ⟨ha2, hfa, hfN⟩ := Ct.lte l c ν E hl hL.c_pos hL.c_two hL.c_le hE
  generalize (1 + l ^ c) ^ E = a at *
  obtain ⟨D, hD⟩ := Ct.datEx L F γ a ha2
  have hDa := hD.a_eq
  have hDn := hD.n_eq
  have hI := Ct.clFin L F γ a D hD
  obtain ⟨hEQf, hEQc⟩ := Ct.cardEQ L F γ a D hTC hL.gal hL.gen hD
  obtain ⟨hClf, hWf, hWc⟩ := Ct.cardW _ _ D hI hEQf
  obtain ⟨hEHf, hEHc⟩ := Ct.eqHomLe L F γ a l ν D hl hD hClf
  refine ⟨hEHf, ?_⟩
  have hlpow : l ^ (ν - c) ≠ 0 := (pow_pos hl.pos _).ne'
  have hbig : 2 ≤ a ^ l ^ (ν - c) := le_trans ha2 (Nat.le_self_pow hlpow a)
  have hN0 : a ^ l ^ (ν - c) - 1 ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = ordCompl[l] (a ^ l ^ (ν - c) - 1) := ⟨_, rfl⟩
  have hNm : a ^ l ^ (ν - c) - 1 = l ^ (ν + E.factorization l) * m := by
    have h0 := Nat.ordProj_mul_ordCompl_eq_self (a ^ l ^ (ν - c) - 1) l
    rw [← hm, hfN] at h0
    exact h0.symm
  have hmd : ¬ l ∣ m := by
    rw [hm]
    exact Nat.not_dvd_ordCompl hl hN0
  have hker : ((D.a : ℤ)) ^ D.n - 1 = ((l ^ ν : ℕ) : ℤ) * ((l ^ E.factorization l * m : ℕ) : ℤ) := by
    rw [hDa, hDn, hL.ord]
    have h1 : 1 ≤ a ^ l ^ (ν - c) := by omega
    have key : ((a ^ l ^ (ν - c) - 1 : ℕ) : ℤ) = (a : ℤ) ^ l ^ (ν - c) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [← key, hNm]
    push_cast
    ring
  obtain ⟨f, hfnm, hfk⟩ := Ct.kerF _ _ D (l ^ ν) (l ^ b) _ hker
  haveI := hWf
  haveI := hEQf
  haveI := hClf
  have hrange := Ct.fewLe L F γ a (l ^ b) (l ^ ν) B D hD hF f hfnm hWf
  obtain ⟨hSLf, hSLc⟩ := Ct.selLCard L l hl
  obtain ⟨hSIf, hSIc⟩ := Ct.selInvLe L F l c ν a ζ γ D hl hL hD hSLf
  have hdvd : (l : ℤ) ∣ (D.a : ℤ) - 1 := by
    rw [hDa]
    have hc1 := hL.c_pos
    have hd : l ∣ a - 1 := Nat.dvd_of_factorization_pos (by rw [hfa]; omega)
    have h1 : 1 ≤ a := by omega
    have hd' := Int.natCast_dvd_natCast.mpr hd
    rw [Nat.cast_sub h1] at hd'
    simpa using hd'
  have htor := Ct.selInj _ _ D l hdvd hl.pos hSIf
  have hg : Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ l ^ gens L := by
    refine htor.trans (hSIc.trans ((Nat.mul_le_mul_right _ hSLc).trans (le_of_eq ?_)))
    unfold gens
    rw [← pow_add]
  have hp := Ct.pCount D.W _ f l (b + E.factorization l) (gens L) (m : ℤ) hl
    (by exact_mod_cast hmd)
    (by
      intro w hw
      have h0 := hfk w hw
      convert h0 using 2
      push_cast
      ring) hg
  have hEQ0 : Nat.card D.EQ ≠ 0 := Nat.card_pos.ne'
  have hCl0 : Nat.card D.ClQ ≠ 0 := Nat.card_pos.ne'
  have hfW : (Nat.card D.W).factorization l =
      (Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l := by
    rw [hWc, Nat.factorization_mul hEQ0 hCl0, Finsupp.add_apply]
  have hfEQ : (Nat.card D.EQ).factorization l + (c + E.factorization l) =
      InfinitePlace.nrComplexPlaces L * (ν + E.factorization l) := by
    have h0 := congrArg (fun n => n.factorization l) hEQc
    have ha1 : a - 1 ≠ 0 := by omega
    rw [Nat.factorization_mul hEQ0 ha1, Finsupp.add_apply, hfa, hL.ord, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul, hfN] at h0
    exact h0
  calc Nat.card ↑(EqHom γ a (l ^ ν)) * (l ^ ν) ^ InfinitePlace.nrComplexPlaces L
      ≤ l ^ (Nat.card D.ClQ).factorization l *
          l ^ ((Nat.card D.EQ).factorization l + (c + E.factorization l)) := by
        refine Nat.mul_le_mul hEHc ?_
        rw [← pow_mul]
        refine Nat.pow_le_pow_right hl.pos ?_
        rw [hfEQ, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    _ = l ^ ((Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l) *
          l ^ (c + E.factorization l) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
    _ ≤ (Nat.card ↥f.range * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [← hfW]
        exact hp
    _ ≤ (B * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hrange)
    _ = B * l ^ ((b + E.factorization l) * gens L + c + E.factorization l) := by
        rw [mul_assoc, ← pow_add, add_assoc]
