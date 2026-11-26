module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orb_gen {G O : Type} [CommGroup G] [Finite G] [CommRing O] [IsDomain O] (f : G →* Oˣ) :
    IsCyclic (G ⧸ f.ker) ∧ ∃ g : G, (∀ x, ∃ a : ℕ, f x = f g ^ a) ∧ f.ker.index = orderOf (f g) := by
  have hfin : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hc : IsCyclic f.range := isCyclic_subgroup_units f.range
  refine ⟨isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange f).symm
    (QuotientGroup.quotientKerEquivRange f).symm.surjective, ?_⟩
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := hc.exists_monoid_generator
  refine ⟨g, fun x => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hg ⟨f x, x, rfl⟩
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  · rw [Subgroup.index_ker, ← orderOf_eq_card_of_forall_mem_powers hg, ← Subgroup.orderOf_coe]

theorem UpperTheory.V.HV.orbFacts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.toUnitHom.ker.index = orderOf ψ ∧ IsCyclic ((ZMod N)ˣ ⧸ ψ.toUnitHom.ker) ∧
      (∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker ↔ ∃ j : ℕ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j) ∧
      {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker}.ncard = Nat.totient (orderOf ψ) := by
  intro O _ _ N _ ψ
  obtain ⟨hc, g, hg, hidx⟩ := orb_gen ψ.toUnitHom
  have hpow : ∀ (χ : DirichletCharacter O N) (k : ℕ) (x : (ZMod N)ˣ),
      (χ ^ k).toUnitHom x = χ.toUnitHom x ^ k := by
    intro χ k x
    ext
    simp [MulChar.pow_apply_coe]
  have hext : ∀ χ χ' : DirichletCharacter O N, (∀ x, χ.toUnitHom x = χ'.toUnitHom x) → χ = χ' := by
    intro χ χ' h
    ext x
    simpa using congrArg Units.val (h x)
  have hone : ∀ x, (1 : DirichletCharacter O N).toUnitHom x = 1 := by
    intro x
    ext
    simp
  have hord : orderOf ψ = orderOf (ψ.toUnitHom g) := by
    rw [orderOf_eq_orderOf_iff]
    intro k
    constructor
    · intro h
      rw [← hpow, h, hone]
    · intro h
      apply hext
      intro x
      obtain ⟨a, ha⟩ := hg x
      rw [hpow, hone, ha, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  have hpos : 0 < orderOf (ψ.toUnitHom g) :=
    (ψ.toUnitHom.isOfFinOrder (isOfFinOrder_of_finite g)).orderOf_pos
  have hfwd : ∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker →
      ∃ j < orderOf ψ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j := by
    intro ψ' h
    have hm : ∀ x, ψ'.toUnitHom x = 1 ↔ ψ.toUnitHom x = 1 := fun x => by
      rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, h]
    have ho : orderOf (ψ'.toUnitHom g) = orderOf (ψ.toUnitHom g) := by
      rw [orderOf_eq_orderOf_iff]
      intro k
      rw [← map_pow, ← map_pow, hm]
    have h1 := IsPrimitiveRoot.orderOf (ψ.toUnitHom g)
    have h2 := IsPrimitiveRoot.orderOf (ψ'.toUnitHom g)
    rw [ho] at h2
    haveI : NeZero (orderOf (ψ.toUnitHom g)) := ⟨hpos.ne'⟩
    obtain ⟨j, hj, hcop, hjj⟩ := (h1.isPrimitiveRoot_iff').1 h2
    refine ⟨j, hord ▸ hj, hord ▸ hcop, hext _ _ fun x => ?_⟩
    obtain ⟨a, ha⟩ := hg x
    have h3 : ψ.toUnitHom (x / g ^ a) = 1 := by rw [map_div, map_pow, ha, div_self']
    have h4 := (hm _).2 h3
    rw [map_div, map_pow, div_eq_one] at h4
    rw [hpow, h4, ha, ← hjj, ← pow_mul, ← pow_mul, mul_comm]
  have hbwd : ∀ j : ℕ, j.Coprime (orderOf ψ) → (ψ ^ j).toUnitHom.ker = ψ.toUnitHom.ker := by
    intro j hj
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hpow]
    constructor
    · intro h
      have h2 : ψ.toUnitHom x ^ orderOf ψ = 1 := by rw [← hpow, pow_orderOf_eq_one, hone]
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one h2)
      rw [hj.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    · intro h
      rw [h, one_pow]
  refine ⟨hidx.trans hord.symm, hc, fun ψ' => ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨j, -, hj⟩ := hfwd ψ' h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact hbwd j hj
  · have hset : {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker} =
        (fun j : ℕ => ψ ^ j) ''
          ((Finset.range (orderOf ψ)).filter (fun a => (orderOf ψ).Coprime a) : Finset ℕ) := by
      ext ψ'
      constructor
      · intro h
        obtain ⟨j, hj, hcop, rfl⟩ := hfwd ψ' h
        exact ⟨j, by simpa using ⟨hj, hcop.symm⟩, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
        exact hbwd j hj'.2.symm
    rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset, Nat.totient_eq_card_coprime]
    refine pow_injOn_Iio_orderOf.mono fun j hj => ?_
    have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
    exact hj'.1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CardLeLevel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem card_le_level (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N]
    (T : Finset (DirichletCharacter O N)) : T.card ≤ N := by
  classical
  have hli := linearIndependent_monoidHom (ZMod N) O
  let g : T → (ZMod N →* O) := fun χ => (χ.1 : MulChar (ZMod N) O).toMonoidHom
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply MulChar.ext'
    intro y
    have := DFunLike.congr_fun h y
    simpa [g] using this
  have hT := (hli.comp g hg).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card, Fintype.card_coe] at hT
  exact hT

theorem UpperTheory.V.HV.xCard :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N], (∀ T : Finset (DirichletCharacter O N), T.card ≤ N) ∧
      ∀ (M : ℕ), 0 < M → ∀ T : Finset (DirichletCharacter O N), (∀ ψ ∈ T, ψ.conductor ∣ M) → T.card ≤ M := by
  intro O _ _ N _
  refine ⟨card_le_level O N, ?_⟩
  intro M hM T hT
  classical
  set g := Nat.gcd M N with hgdef
  have hgN : g ∣ N := Nat.gcd_dvd_right M N
  have hgM : g ≤ M := Nat.le_of_dvd hM (Nat.gcd_dvd_left M N)
  haveI : NeZero g := ⟨(Nat.gcd_pos_of_pos_left N hM).ne'⟩
  have hex : ∀ ψ ∈ T, ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ := by
    intro ψ hψ
    obtain ⟨hc, χ₀, hχ₀⟩ := ψ.factorsThrough_conductor
    have hcg : ψ.conductor ∣ g := Nat.dvd_gcd (hT ψ hψ) hc
    refine ⟨DirichletCharacter.changeLevel hcg χ₀, ?_⟩
    rw [← DirichletCharacter.changeLevel_trans]
    exact hχ₀
  let f : DirichletCharacter O N → DirichletCharacter O g := fun ψ =>
    if h : ∃ ψ₀ : DirichletCharacter O g, ψ = DirichletCharacter.changeLevel hgN ψ₀ then h.choose else 1
  have hf : ∀ ψ ∈ T, ψ = DirichletCharacter.changeLevel hgN (f ψ) := by
    intro ψ hψ
    have h := hex ψ hψ
    simp only [f, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn f T := by
    intro a ha b hb hab
    rw [hf a ha, hf b hb, hab]
  calc T.card = (T.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ g := card_le_level O g _
    _ ≤ M := hgM
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LossLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.lossLe :
    ∀ l N n e : ℕ, l.Prime → l ≠ 2 → 2 ≤ N → n ≤ N → 1 ≤ e → lossAll l N n e ≤ (N * e) ^ 6 ∧ LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
  intro l N n e hl hl2 hN hn he
  have hfac : ∀ (p m : ℕ), m.factorization p ≤ m := by
    intro p m
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · exact (Nat.factorization_lt p h0.ne').le
  have hnu : LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
    unfold LDataCardLeFinrank.nuBound
    have a1 := hfac l N
    have a2 := hfac l e
    split_ifs
    · have : max (N.factorization l) 1 ≤ N.factorization l + 1 := max_le (by omega) (by omega)
      nlinarith
    · exact Nat.zero_le _
  have hk : N.primeFactors.card ≤ N := by
    calc N.primeFactors.card ≤ (Finset.Icc 1 N).card := by
          apply Finset.card_le_card
          intro p hp
          have hp' := Nat.mem_primeFactors.mp hp
          simp only [Finset.mem_Icc]
          exact ⟨hp'.1.one_lt.le, Nat.le_of_dvd (by omega) hp'.2.1⟩
      _ = N := by simp
  have hv : n.factorization l ≤ N := (hfac l n).trans hn
  refine ⟨?_, hnu⟩
  set M := N * e with hM
  have hNM : N ≤ M := Nat.le_mul_of_pos_right N he
  have hM2 : 2 ≤ M := hN.trans hNM
  have hnuM : LDataCardLeFinrank.nuBound l N e ≤ 2 * M := by rw [hM, ← mul_assoc]; exact hnu
  unfold lossAll Chr.loss
  have b1 : (n + n ^ 2) * LDataCardLeFinrank.nuBound l N e ≤ (M + M ^ 2) * (2 * M) := by
    apply Nat.mul_le_mul _ hnuM
    have : n ≤ M := hn.trans hNM
    have : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have b2 : N.primeFactors.card * (n * n.factorization l) ≤ M * (M * M) :=
    Nat.mul_le_mul (hk.trans hNM) (Nat.mul_le_mul (hn.trans hNM) (hv.trans hNM))
  have b3 : N.primeFactors.card * n.factorization l ≤ M * M :=
    Nat.mul_le_mul (hk.trans hNM) (hv.trans hNM)
  have hM3 : 8 ≤ M ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ M ^ 3 := Nat.pow_le_pow_left hM2 3
  have b4 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M ≤ M ^ 6 := by
    have e6 : M ^ 6 = M ^ 3 * M ^ 3 := by ring
    have : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : (M + M ^ 2) * (2 * M) + M * (M * M) + M * M = 2 * M ^ 2 + 3 * M ^ 3 + M ^ 2 := by ring
    rw [h1, e6]
    nlinarith
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbSum
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem ker_eq_bot_of_orderOf {Q : Type} [CommGroup Q] [Finite Q] (χ : Q →* ℂˣ)
    (h : orderOf χ = Nat.card Q) : χ.ker = ⊥ := by
  have h1 : χ ^ χ.ker.index = 1 := by
    ext x
    have : x ^ χ.ker.index ∈ χ.ker := Subgroup.pow_index_mem _ _
    rw [MonoidHom.mem_ker, map_pow] at this
    simp [MonoidHom.pow_apply, this]
  have h2 : Nat.card Q ∣ χ.ker.index := h ▸ orderOf_dvd_of_pow_eq_one h1
  have h3 : χ.ker.index = Nat.card Q := Nat.dvd_antisymm (Subgroup.index_dvd_card _) h2
  have h4 := Subgroup.card_mul_index χ.ker
  rw [h3] at h4
  have h5 : Nat.card χ.ker = 1 := by
    have hp : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hp (by rw [h4, one_mul])
  exact Subgroup.card_eq_one.1 h5

open Classical in
private theorem totient_le_card_ker {Γ : Type} [CommGroup Γ] [Finite Γ] [Fintype (Γ →* ℂˣ)] (H : Subgroup Γ)
    (hH : IsCyclic (Γ ⧸ H)) :
    Nat.totient H.index ≤ (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card := by
  haveI : NeZero (Monoid.exponent (Γ ⧸ H)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Γ ⧸ H) ℂ
  haveI : Finite ((Γ ⧸ H) →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype ((Γ ⧸ H) →* ℂˣ) := Fintype.ofFinite _
  haveI : IsCyclic ((Γ ⧸ H) →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  have hc : Fintype.card ((Γ ⧸ H) →* ℂˣ) = H.index := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]; rfl
  rw [← IsCyclic.card_orderOf_eq_totient (α := (Γ ⧸ H) →* ℂˣ) (d := H.index) (hc ▸ dvd_rfl)]
  refine Finset.card_le_card_of_injOn (fun χ => χ.comp (QuotientGroup.mk' H)) ?_ ?_
  · intro χ hχ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hχ ⊢
    have := ker_eq_bot_of_orderOf χ hχ
    rw [← MonoidHom.comap_ker, this, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  · intro a _ b _ hab
    exact QuotientGroup.monoidHom_ext _ hab

theorem UpperTheory.V.HV.orbSum :
    ∀ (Γ : Type) [CommGroup Γ] [Finite Γ] (T : Finset (Subgroup Γ)), (∀ H ∈ T, IsCyclic (Γ ⧸ H)) → ∑ H ∈ T, Nat.totient H.index ≤ Nat.card Γ := by
  intro Γ _ _ T hT
  classical
  haveI : NeZero (Monoid.exponent Γ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Γ ℂ
  haveI : Finite (Γ →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  letI : Fintype (Γ →* ℂˣ) := Fintype.ofFinite _
  calc ∑ H ∈ T, Nat.totient H.index
      ≤ ∑ H ∈ T, (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker = H).card :=
        Finset.sum_le_sum fun H hH => by convert totient_le_card_ker H (hT H hH)
    _ = (Finset.univ.filter fun χ : Γ →* ℂˣ => χ.ker ∈ T).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ Fintype.card (Γ →* ℂˣ) := Finset.card_le_univ _
    _ = Nat.card Γ := by rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv]
end
