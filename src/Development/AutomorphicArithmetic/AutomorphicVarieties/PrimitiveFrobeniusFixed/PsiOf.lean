module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimRam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.FrobFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzany

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primeq
open Finset UpperTheory.V.Bern

private theorem key_primeq {R : Type} [CommRing R] [Algebra ℚ R] {M c c' : ℕ} [NeZero M] (k : ℕ)
    (ψ : DirichletCharacter R c) (ψ' : DirichletCharacter R c') (e : c = c') (h : c ∣ M) (h' : c' ∣ M)
    (hψ : DirichletCharacter.changeLevel h ψ = DirichletCharacter.changeLevel h' ψ') :
    genB k (ψ : ZMod c → R) = genB k (ψ' : ZMod c' → R) ∧ ∀ a : ℕ, ψ (a : ZMod c) = ψ' (a : ZMod c') := by
  subst e
  have hψψ : ψ = ψ' := DirichletCharacter.changeLevel_injective h hψ
  subst hψψ
  exact ⟨rfl, fun _ => rfl⟩

theorem UpperTheory.V.Bern.b_primeq :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (χ.IsPrimitive → Bprim k χ = genB k χ ∧ ∀ a : ℕ, primVal χ a = χ (a : ZMod N)) ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), Bprim k (DirichletCharacter.changeLevel h χ) = Bprim k χ ∧ ∀ a : ℕ, primVal (DirichletCharacter.changeLevel h χ) a = primVal χ a := by
  intro R _ _ N _ k χ
  refine ⟨fun hp => ?_, fun M _ h => ?_⟩
  · exact key_primeq k χ.primitiveCharacter χ hp χ.conductor_dvd_level (dvd_refl N)
      (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_self])
  · refine key_primeq k (DirichletCharacter.changeLevel h χ).primitiveCharacter χ.primitiveCharacter
      (DirichletCharacter.conductor_changeLevel χ h) (DirichletCharacter.conductor_dvd_level _)
      (χ.conductor_dvd_level.trans h) ?_
    rw [DirichletCharacter.changeLevel_primitiveCharacter,
      DirichletCharacter.changeLevel_trans _ χ.conductor_dvd_level h,
      DirichletCharacter.changeLevel_primitiveCharacter]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimCase
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.RatPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem rat_pow {l : ℕ} (hl : Odd l) (a : ℚˣ) (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), (l : ℤ) ∣ Kum.ordv v a) :
    ∃ y : ℚ, (a : ℚ) = y ^ l := by
  have hl0 : l ≠ 0 := hl.pos.ne'
  have h1 := (Kum.radClKer ℚ ∅ l hl0 a fun v _ => h v).1 (by
    haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
    haveI : Subsingleton (ClassGroup (𝓞 ℚ)) :=
      (@Fintype.card_le_one_iff_subsingleton _ (_)).1 (card_classGroup_eq_one (R := 𝓞 ℚ)).le
    rw [Subsingleton.elim (Kum.radCl l a) 1]; exact one_mem _)
  obtain ⟨u, hu, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h1
  have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (u : ℚ) = 1 := fun v => hu v (by simp)
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ (u : ℚ) fun v => (hv v).le
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ (u : ℚ)⁻¹ fun v => by
    rw [map_inv₀, hv v, inv_one]
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, hx, hy, map_one, mul_inv_cancel₀ u.ne_zero]
  have h2 : Rat.ringOfIntegersEquiv x * Rat.ringOfIntegersEquiv y = 1 := by rw [← map_mul, hxy, map_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with e | e
  · have : x = 1 := Rat.ringOfIntegersEquiv.injective (by rw [e, map_one])
    exact ⟨b, by simp [← hx, this]⟩
  · have : x = -1 := Rat.ringOfIntegersEquiv.injective (by rw [e, map_neg, map_one])
    exact ⟨-b, by simp [← hx, this, hl.neg_pow]⟩

private theorem rat_place (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ q : ℕ, q.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ w.asIdeal → w = v := by
  refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, fun w hw => ?_⟩
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  apply Subtype.ext
  refine (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w)
    (Rat.HeightOneSpectrum.prime_natGenerator v)).1 ?_
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hw
  simpa using this

private theorem kum {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (hl : Odd l)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ l) (η z : G ℚ Ω → ZMod l) (hη : ∀ g : G ℚ Ω, g ζ = ζ ^ (η g).val)
    (hz : IsLocallyConstant z) (hc : ∀ g h, z (g * h) = z g + η g * z h)
    (hi : ∀ q : ℕ, q.Prime → ∃ A : ValuationSubring Ω, Over A q ∧ ∀ g ∈ Ine (F := ℚ) A, z g = 0)
    (t : G ℚ Ω) (ht : η t ≠ 1) (h0 : z t = 0) (g : G ℚ Ω) : z g = 0 := by
  obtain ⟨β, a, ha, hβ⟩ := Kum.radExists ℚ Ω l ζ η z hζ hη hz hc
  obtain ⟨y, hy⟩ := rat_pow hl a fun v => by
    obtain ⟨q, hq, hv⟩ := rat_place v
    obtain ⟨A, hA, hA'⟩ := hi q hq
    obtain ⟨w, hw, -, hw'⟩ := (placeBasic Ω).2.2.2.2.2.2.2.2.1 A q hq hA
    obtain rfl := hv w hw'
    exact Kum.dvdOfIne ℚ Ω l A w β a hw ha fun g hg => by rw [hβ, hA' g hg, ZMod.val_zero, pow_zero, one_mul]
  have hl0 : l ≠ 0 := hl.pos.ne'
  have hy0 : algebraMap ℚ Ω y ≠ 0 := by
    rw [map_ne_zero]; rintro rfl
    exact a.ne_zero (by rw [hy, zero_pow hl0])
  have h1 : (β / algebraMap ℚ Ω y) ^ l = 1 := by
    rw [div_pow, ha, hy, map_pow, div_self (pow_ne_zero _ hy0)]
  obtain ⟨j, hj, hj'⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hb : β = ζ ^ j * algebraMap ℚ Ω y := by rw [hj', div_mul_cancel₀ _ hy0]
  have key : ∀ g : G ℚ Ω, η g * j = z g + j := fun g => by
    have h2 := hβ g
    rw [hb, map_mul, map_pow, hη, AlgEquiv.commutes, ← mul_assoc, ← pow_mul, ← pow_add] at h2
    have h3 := mul_right_cancel₀ hy0 h2
    rw [pow_eq_pow_mod _ hζ.pow_eq_one, pow_eq_pow_mod (_ + _) hζ.pow_eq_one] at h3
    have h4 := hζ.pow_inj (Nat.mod_lt _ hl.pos) (Nat.mod_lt _ hl.pos) h3
    have h5 := (ZMod.natCast_eq_natCast_iff' _ _ l).2 h4
    simpa using h5
  have hj0 : (j : ZMod l) = 0 := by
    have h2 := key t
    rw [h0, zero_add] at h2
    by_contra hne
    exact ht (mul_right_cancel₀ hne (by rw [h2, one_mul]))
  simpa [hj0] using (key g).symm

private theorem cyc_nat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (g : G ℚ Ω) :
    ∃ n : ℕ, (∀ x : Ω, x ^ l = 1 → g x = x ^ n) ∧ (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  refine ⟨(PadicInt.toZModPow 1 (cycZ ℚ Ω l g : ℤ_[l])).val, fun x hx =>
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) x (by rwa [pow_one]), ?_⟩
  rw [← Ideal.mem_span_singleton, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_natCast, ZMod.natCast_zmod_val, sub_self]

private theorem l_mem (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : (l : ℤ_[l]) ∈ (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) := by
    change (l : ℤ_[l]) ∈ (IsLocalRing.maximalIdeal O).under ℤ_[l]
    rw [IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l])
      (IsLocalRing.maximalIdeal O)), PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  simpa using h

private theorem sep' (l : ℕ) [Fact l.Prime] {V : Type} [AddCommGroup V] [Module (ZMod l) V] (v : V)
    (hv : ∀ f : V →+ ZMod l, f v = 0) : v = 0 :=
  (Module.forall_dual_apply_eq_zero_iff (ZMod l) v).1 fun f => hv f.toAddMonoidHom

private theorem sep (l : ℕ) [Fact l.Prime] {V : Type} [AddCommGroup V] (h : ∀ v : V, l • v = 0) (v : V)
    (hv : ∀ f : V →+ ZMod l, f v = 0) : v = 0 :=
  @sep' l _ V _ (AddCommGroup.zmodModule h) v hv

private theorem sht_pi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (hl : Odd l)
    {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (α : G ℚ Ω →* Oˣ) (π : O) (hπ : π ∣ (l : O))
    (n : G ℚ Ω → ℕ) (hn : ∀ (g : G ℚ Ω) (x : Ω), x ^ l = 1 → g x = x ^ n g) (hα : ∀ g, π ∣ (α g : O) - n g)
    (A₀ : ValuationSubring Ω) (hA₀ : Over A₀ l) (t : G ℚ Ω) (ht : t ∈ Ine (F := ℚ) A₀) (ht1 : (n t : ZMod l) ≠ 1)
    (hu : IsUnit ((α t : O) - 1)) (a : O) (c : G ℚ Ω → W) (hc : c ∈ ShT W α t l a) (h0 : π • c = 0) : c = 0 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨⟨h1, h2⟩, h3, -, h4, h5⟩ := hc
  obtain ⟨m, -, hm⟩ := h5 A₀ hA₀
  have hm0 : m = 0 := by
    have := hm t ht.1
    rw [h3] at this
    exact hu.smul_left_cancel.1 (by rw [sub_smul, one_smul, ← this, smul_zero])
  let V := Submodule.torsionBy O W π
  have kill : ∀ y : O, π ∣ y → ∀ v : V, y • v = 0 := by
    rintro _ ⟨y, rfl⟩ v
    rw [mul_comm, mul_smul, Submodule.smul_torsionBy, smul_zero]
  let c' : G ℚ Ω → V := fun g => ⟨c g, congrFun h0 g⟩
  have hlc : IsLocallyConstant c' := IsLocallyConstant.desc c' Subtype.val h1 Subtype.val_injective
  have hcc : ∀ g h, c' (g * h) = c' g + n g • c' h := fun g h => by
    have e := kill _ (hα g) (c' h)
    rw [sub_smul, sub_eq_zero, Nat.cast_smul_eq_nsmul] at e
    rw [← e]
    exact Subtype.ext (h2 g h)
  funext g
  refine congrArg Subtype.val (sep l (fun v => by rw [← Nat.cast_smul_eq_nsmul O, kill _ hπ]) (c' g) fun f => ?_)
  have z0 : ∀ g, c g = 0 → f (c' g) = 0 := fun g hg => by rw [show c' g = 0 from Subtype.ext hg, map_zero]
  refine kum hl hζ (fun g => (n g : ZMod l)) (fun g => f (c' g)) (fun g => ?_) (hlc.comp f) (fun g h => ?_)
    (fun q hq => ?_) t ht1 (z0 t h3) g
  · rw [hn g ζ hζ.pow_eq_one, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ.pow_eq_one]
  · rw [hcc, map_add (f := _), map_nsmul, nsmul_eq_mul]
  · by_cases e : q = l
    · exact ⟨A₀, e ▸ hA₀, fun g hg => z0 g (by rw [hm g hg.1, hm0, smul_zero, sub_zero])⟩
    · obtain ⟨A, hA⟩ := (placeBasic Ω).1 q hq
      exact ⟨A, hA, fun g hg => z0 g (h4 A ((placeBasic Ω).2.2.2.1 A q l ((Nat.coprime_primes hq hp).2 e) hA) g hg)⟩

theorem UpperTheory.V.ML.exc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], l ≠ 2 → ∀ α : G ℚ Ω →* Oˣ, (∀ g, ¬ IsUnit ((α g : O) - (chiO ℚ Ω l O g : O))) →
    (∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine (F := ℚ) A, α g = 1) → ShaU (twist₂ l α) l (⊤ : Subgroup (G ℚ Ω)) = ⊥ := by
  intro Ω _ _ _ l _ O _ _ _ _ _ hl2 α hα hun
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : l.Prime := Fact.out
  have hl : Odd l := hp.odd_of_ne_two hl2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ π ∣ y := fun y => by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hπl : π ∣ (l : O) := (hmax _).1 (l_mem l O)
  choose n hn hn' using cyc_nat (Ω := Ω) l
  have hαn : ∀ g, π ∣ (α g : O) - n g := fun g => by
    have e1 : π ∣ (α g : O) - (chiO ℚ Ω l O g : O) := (hmax _).1 (hα g)
    have e2 := map_dvd (algebraMap ℤ_[l] O) (hn' g)
    rw [map_natCast, map_sub, map_natCast] at e2
    have := dvd_add e1 (hπl.trans e2)
    rwa [show (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O (cycZ ℚ Ω l g : ℤ_[l]) from rfl, sub_add_sub_cancel] at this
  obtain ⟨A₀, hA₀⟩ := (placeBasic Ω).1 l hp
  obtain ⟨t, ht, htl⟩ := (ineTau Ω l hp).1 A₀ hA₀ (-1)
  have ht1 : (n t : ZMod l) ≠ 1 := fun e => by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
    have h3 := (hn t ζ hζ.pow_eq_one).symm.trans (htl ζ hζ.pow_eq_one)
    rw [pow_eq_pow_mod _ hζ.pow_eq_one] at h3
    have h4 := hζ.pow_inj (Nat.mod_lt _ hl.pos) (ZMod.val_lt _) h3
    rw [← ZMod.val_natCast, e] at h4
    have h5 := ZMod.val_injective l h4
    haveI : Fact (2 < l) := ⟨lt_of_le_of_ne hp.two_le hl2.symm⟩
    exact ZMod.neg_one_ne_one (by simpa using h5.symm)
  have hu : IsUnit ((α t : O) - 1) := by
    by_contra hnu
    have e1 : π ∣ (α t : O) - 1 := (hmax _).1 hnu
    have e2 : π ∣ (n t : O) - 1 := by simpa using dvd_sub e1 (hαn t)
    have e3 : IsUnit ((n t : ℤ_[l]) - 1) := by
      by_contra h
      have h' : (n t : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
        rw [PadicInt.ker_toZMod]; exact h
      exact ht1 (by simpa [sub_eq_zero] using h')
    have e4 := e3.map (algebraMap ℤ_[l] O)
    rw [map_sub, map_natCast, map_one] at e4
    exact hπ.not_isUnit (isUnit_of_dvd_unit e2 e4)
  have key := shaToShT Ω l O α t hu l hp.ne_zero hun (fun A h h' => absurd h h') 0 fun a ha => by
    have hb : ShT (QO l O) α t l a = ⊥ := by
      have ind : ∀ (k : ℕ), ∀ c ∈ ShT (QO l O) α t l a, π ^ k • c = 0 → c = 0 := fun k => by
        induction k with
        | zero => intro c _ h; simpa using h
        | succ k ih =>
          intro c hc h
          exact ih c hc (sht_pi hl α π hπl n hn hαn A₀ hA₀ t ht ht1 hu a _ (Submodule.smul_mem _ _ hc)
            (by rw [← mul_smul, ← pow_succ', h]))
      obtain ⟨k, u, e⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      refine (Submodule.eq_bot_iff _).2 fun c hc => ind k c hc ?_
      have h1 : a • c = 0 := funext hc.2.2.1
      rw [e, mul_smul] at h1
      exact u.isUnit.smul_left_cancel.1 (by rw [h1, smul_zero])
    rw [hb, Module.length_bot]
  exact Submodule.subsingleton_iff_eq_bot.1 (Module.length_eq_zero_iff.1 (nonpos_iff_eq_zero.1 key))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ZeNorm
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GenBUnits
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem th_eq (F b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    (b : ℤ) * (t.val : ℤ) = (((b : ZMod F) * t).val : ℤ) + F * ((t.val * b / F : ℕ) : ℤ) ∧
    th F b t = 2 * ((t.val * b / F : ℕ) : ℤ) - ((b : ℤ) - 1) := by
  have hF : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have h1 : ((b : ZMod F) * t).val = t.val * b % F := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, mul_comm]
  have h0 : 0 < ((b : ZMod F) * t).val := Nat.pos_of_ne_zero fun h => hy ((ZMod.val_eq_zero _).1 h)
  have hlt := ZMod.val_lt ((b : ZMod F) * t)
  have h2 : F * (t.val * b / F) + t.val * b % F = t.val * b := Nat.div_add_mod _ _
  have h3 : F * ((-t).val * b / F) + (-t).val * b % F = (-t).val * b := Nat.div_add_mod _ _
  have h4 : (-t).val * b % F < F := Nat.mod_lt _ hF
  have h5 : (-t).val + t.val = F := by
    rw [ZMod.neg_val, if_neg ht]
    have := ZMod.val_lt t
    omega
  rw [← h1] at h2
  rw [th]
  generalize ((b : ZMod F) * t).val = y at *
  generalize (-t).val * b % F = r at *
  generalize (-t).val * b / F = j' at *
  generalize t.val * b / F = j at *
  generalize (-t).val = s at *
  generalize t.val = u at *
  zify at h0 hlt h2 h3 h4 h5 hF
  have hr : (0 : ℤ) ≤ r := by positivity
  have h6 : (F : ℤ) * (b - j - j') = y + r := by linear_combination -h2 - h3 - b * h5
  have h7 : (0 : ℤ) < b - j - j' := by
    by_contra h
    nlinarith
  have h8 : (b : ℤ) - j - j' < 2 := by
    by_contra h
    nlinarith
  exact ⟨by linear_combination -h2, by omega⟩

private theorem pointwise (F e b : ℕ) [NeZero F] (t : ZMod F) (ht : t ≠ 0) (hy : (b : ZMod F) * t ≠ 0) :
    ∃ z : ℤ, (Stk.dk (e + 1) : ℚ) * ((b : ℚ) ^ e * (th F b t * (t.val : ℚ) ^ e) +
      2 * (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val / (e + 1) -
        (b : ℚ) ^ (e + 1) * (Bern.bcoef F (e + 1) t.val / (e + 1)))) = F * z := by
  have hM0 : 0 < F := Nat.pos_of_ne_zero (NeZero.ne F)
  have hM : (F : ℚ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  obtain ⟨h1, h2⟩ := th_eq F b t ht hy
  obtain ⟨z1, hz1⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e ((b : ZMod F) * t).val hM0
  obtain ⟨z2, hz2⟩ := Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator F e t.val hM0
  rw [h2]
  generalize ((b : ZMod F) * t).val = y at *
  generalize t.val * b / F = j at *
  generalize t.val = u at *
  obtain ⟨⟨z3, hz3⟩, ⟨w, hw⟩⟩ := Stk.exists_binomial_expansion_mod_sq ((b : ℤ) * u) (-(j : ℤ)) F e
  have h3 : (b : ℤ) * u + F * (-(j : ℤ)) = y := by linear_combination h1
  rw [h3] at hz3 hw
  have q3 : (y : ℚ) ^ (e + 1) =
      ((b : ℚ) * u) ^ (e + 1) + ((e : ℚ) + 1) * ((b : ℚ) * u) ^ e * ((F : ℚ) * (-(j : ℚ))) + (F : ℚ) ^ 2 * z3 := by
    exact_mod_cast hz3
  have qw : (y : ℚ) ^ e = ((b : ℚ) * u) ^ e + (F : ℚ) * w := by
    exact_mod_cast hw
  have hdk : (Stk.dk (e + 1) : ℚ) = 2 * ((e : ℚ) + 1) * (primorial (e + 1 + 1) : ℚ) := by
    rw [Stk.dk]; push_cast; ring
  refine ⟨4 * z1 - 4 * (b : ℤ) ^ (e + 1) * z2 + 4 * (primorial (e + 1 + 1) : ℤ) * z3
    - 2 * ((e : ℤ) + 1) * (primorial (e + 1 + 1) : ℤ) * w, ?_⟩
  rw [Nat.cast_add, Nat.cast_one] at hz1 hz2
  rw [hz1, hz2, q3, qw, hdk]
  push_cast
  field_simp
  ring

private theorem genB_units {R : Type} [CommRing R] [Algebra ℚ R] {F : ℕ} [NeZero F] (hF : 1 < F) (k : ℕ)
    (χ : DirichletCharacter R F) :
    Bern.genB k (χ : ZMod F → R) = ∑ t : (ZMod F)ˣ, χ t * algebraMap ℚ R (Bern.bcoef F k (t : ZMod F).val) := by
  haveI : Fact (1 < F) := ⟨hF⟩
  have h1 : Bern.genB k (χ : ZMod F → R) = ∑ t : ZMod F, χ t * algebraMap ℚ R (Bern.bcoef F k t.val) := by
    rw [← Bern.b_sumicc (fun x : ZMod F => χ x * algebraMap ℚ R (Bern.bcoef F k x.val)), Bern.genB]
    refine Finset.sum_congr rfl fun a ha => ?_
    rcases (Finset.mem_Icc.1 ha).2.lt_or_eq with h | h
    · rw [ZMod.val_cast_of_lt h]
    · rw [h, ZMod.natCast_self, χ.map_nonunit not_isUnit_zero, zero_mul, zero_mul]
  rw [h1]
  symm
  refine Finset.sum_of_injOn (fun t : (ZMod F)ˣ => (t : ZMod F)) (fun a _ b _ h => Units.ext h)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro x _ hx
  rw [χ.map_nonunit, zero_mul]
  rintro ⟨u, rfl⟩
  exact hx ⟨u, by simp, rfl⟩

private theorem norm_chi {R : Type} [NormedField R] {F : ℕ} [NeZero F] (χ : DirichletCharacter R F) (t : (ZMod F)ˣ) :
    ‖χ t‖ = 1 := by
  have h : χ t ^ Fintype.card (ZMod F)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖χ t‖ ^ Fintype.card (ZMod F)ˣ = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

theorem UpperTheory.V.ML.zCong :
    ∀ (l : ℕ) [Fact l.Prime] (F m e b : ℕ) [NeZero F], l ^ m ∣ F → 1 ≤ m → 1 ≤ e → b.Coprime F → ∀ χ : DirichletCharacter (PadicAlgCl l) F, χ (-1) = (-1) ^ (e + 1) →
    ‖(UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)))‖ ≤ ‖(l : PadicAlgCl l) ^ m‖ := by
  intro l hl F m e b _ hm h1m _ hb χ _
  have hF : 1 < F := lt_of_lt_of_le (Nat.one_lt_pow (by omega) hl.out.one_lt)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne F)) hm)
  haveI : Fact (1 < F) := ⟨hF⟩
  set u : (ZMod F)ˣ := ZMod.unitOfCoprime b hb with hu
  have hub : (u : ZMod F) = b := ZMod.coe_unitOfCoprime b hb
  have g1 := genB_units hF (e + 1) χ
  have g2 : Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) = ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) ((b : ZMod F) * t).val) := by
    rw [g1, ← hub]
    exact (Equiv.sum_comp (Equiv.mulLeft u) (fun t : (ZMod F)ˣ => χ t *
      algebraMap ℚ (PadicAlgCl l) (Bern.bcoef F (e + 1) (t : ZMod F).val))).symm
  have hp : ∀ t : (ZMod F)ˣ, _ := fun t => pointwise F e b (t : ZMod F) t.ne_zero (by
    rw [← hub]; exact (u * t).ne_zero)
  choose z hz using hp
  have key : (UpperTheory.V.Stk.dk (e + 1) : PadicAlgCl l) * ((b : PadicAlgCl l) ^ e * χ b * ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) * (((t : ZMod F).val : PadicAlgCl l) ^ e * χ t) -
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1))) =
      ∑ t : (ZMod F)ˣ, χ ((b : ZMod F) * t) * ((F : PadicAlgCl l) * z t) := by
    have e1 : 2 * (χ b * (b : PadicAlgCl l) ^ (e + 1) - 1) * (UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) / (e + 1)) =
      2 * (χ b * (b : PadicAlgCl l) ^ (e + 1)) / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l)
        - 2 / (e + 1) * UpperTheory.V.Bern.genB (e + 1) (χ : ZMod F → PadicAlgCl l) := by ring
    rw [e1]
    nth_rewrite 2 [g2]
    rw [g1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := congrArg (algebraMap ℚ (PadicAlgCl l)) (hz t)
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_natCast, map_intCast, map_div₀, map_one, map_ofNat] at h
    rw [← h, map_mul]
    ring
  rw [key]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun t _ => ?_
  obtain ⟨c, hc⟩ := hm
  have hn : ‖χ ((b : ZMod F) * t)‖ = 1 := by
    rw [← hub]; exact norm_chi χ (u * t)
  have hFc : (F : PadicAlgCl l) * z t = (l : PadicAlgCl l) ^ m * (((c : ℤ) * z t : ℤ) : PadicAlgCl l) := by
    have : (F : PadicAlgCl l) = (l : PadicAlgCl l) ^ m * c := by exact_mod_cast congrArg (Nat.cast : ℕ → PadicAlgCl l) hc
    rw [this]; push_cast; ring
  rw [norm_mul, hn, one_mul, hFc, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem ze_norm {l : ℕ} [Fact l.Prime] (c : HV.Coef l) :
    (∀ x : c.O, ‖(x : PadicAlgCl l)‖ ≤ 1) ∧ ∀ x y : c.O, ‖(y : PadicAlgCl l)‖ ≤ ‖(x : PadicAlgCl l)‖ → x ∣ y := by
  obtain ⟨hinj, -, -, -, -, h0, hfin, -, -⟩ := dvrFacts l c.O
  have hE : (eO l c.O).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, not_or]
    exact ⟨h0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hfin⟩
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine ⟨fun x => ?_, fun x y h => ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have := normO l c.O x hx
      rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) hE, this]
      exact pow_le_one₀ hl0.le hl1.le
  · rcases eq_or_ne y 0 with rfl | hy
    · exact dvd_zero _
    have hx : x ≠ 0 := by
      rintro rfl
      apply hy
      have : (y : PadicAlgCl l) = 0 := by simpa using h
      exact Subtype.ext this
    have h1 := pow_le_pow_left₀ (norm_nonneg _) h (eO l c.O).toNat
    rw [normO l c.O x hx, normO l c.O y hy, pow_le_pow_iff_right_of_lt_one₀ hl0 hl1] at h1
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd]
    have a1 : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hx
    have a2 : IsDiscreteValuationRing.addVal c.O y ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hy
    rw [← ENat.coe_toNat a1, ← ENat.coe_toNat a2]
    exact_mod_cast h1

private theorem ze_chi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] {F m k : ℕ} (h : l ^ m ∣ F) {g : G ℚ Ω} (hg : Pows F k g) :
    (l : O) ^ m ∣ (chiO ℚ Ω l O g : O) - k := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have h1 : g ζ = ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec l g.toRingEquiv ζ hζ.pow_eq_one
  have h2 : g ζ = ζ ^ k := hg ζ (by obtain ⟨d, rfl⟩ := h; rw [pow_mul, hζ.pow_eq_one, one_pow])
  have h3 : (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val ≡ k [MOD l ^ m] := by
    have ho : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, NeZero.pos _, hζ.pow_eq_one⟩
    have := h1.symm.trans h2
    rwa [ho.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at this
  have h4 : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - k ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ← (ZMod.natCast_eq_natCast_iff _ _ _).2 h3,
      ZMod.natCast_zmod_val, sub_self]
  have h5 := map_dvd (algebraMap ℤ_[l] O) (Ideal.mem_span_singleton.1 h4)
  simpa [chiO] using h5

private theorem ze_dir {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O]
    {f F k : ℕ} [NeZero f] (ψ : DirichletCharacter O f) (h : f ∣ F) (hk : k.Coprime F) {g : G ℚ Ω} (hg : Pows F k g) :
    (Chr.dirG ℚ Ω ψ g : O) = ψ k := by
  have h1 : Chr.cls ℚ Ω f g = ZMod.unitOfCoprime k (hk.of_dvd_right h) := by
    refine (Chr.clsFacts ℚ Ω f).2.2.1 g _ fun ζ hζ => ?_
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod k hζ]
    exact hg ζ (by obtain ⟨d, rfl⟩ := h; rw [pow_mul, hζ, one_pow])
  rw [Chr.dirG, MonoidHom.comp_apply, h1, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

private theorem ze_psi {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {f F m k : ℕ} [NeZero f] (ψ : DirichletCharacter O f) (e : ℕ) (hl : l ^ m ∣ F) (h : f ∣ F)
    (hk : k.Coprime F) {g : G ℚ Ω} (hg : Pows F k g) :
    (l : O) ^ m ∣ (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : O) - (k : O) ^ e * ψ k := by
  have h1 := (ze_chi l O hl hg).trans (sub_dvd_pow_sub_pow _ _ e)
  have h2 : (Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : O) = (chiO ℚ Ω l O g : O) ^ e * ψ k := by
    rw [← ze_dir ψ h hk hg]
    simp [Chr.Psi]
  rw [h2, ← sub_mul]
  exact h1.mul_right _

private theorem ze_dat {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {f F m : ℕ} [NeZero f] [NeZero F] (ψ : DirichletCharacter O f) (e : ℕ) (hl : l ^ m ∣ F) (h : f ∣ F)
    (hψ : ψ (-1) = (-1) ^ (e + 1)) :
    (∀ g ∈ fixMu ℚ Ω F, (l : O) ^ m ∣ (((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : Oˣ) : O) - 1) ∧
    ∀ g : G ℚ Ω, Lifts F (-1) g → (l : O) ^ m ∣ (((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : Oˣ) : O) + 1 := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have h1 := ze_psi l ψ e hl h (Nat.coprime_one_left F) (g := g) (fun x hx => by rw [pow_one]; exact hg x hx)
    rw [MonoidHom.inv_apply]
    set u := Chr.Psi l e (Chr.dirG ℚ Ω ψ) g
    have e1 : ((u⁻¹ : Oˣ) : O) - 1 = (u - ((1 : ℕ) : O) ^ e * ψ (1 : ℕ)) * (-(u⁻¹ : Oˣ)) := by
      simp [sub_mul]
    rw [e1]; exact h1.mul_right _
  · have h1 := ze_psi l ψ e hl h (ZMod.val_coe_unit_coprime _) hg
    set k := (((-1 : (ZMod F)ˣ) : ZMod F)).val with hk
    have h2 : F ∣ k + 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hk, ZMod.natCast_zmod_val]; simp
    have h3 : (k : ZMod f) = -1 := by
      have := (ZMod.natCast_eq_zero_iff _ _).2 (h.trans h2)
      rw [Nat.cast_add, Nat.cast_one] at this
      exact eq_neg_of_add_eq_zero_left this
    have h4 : (l : O) ^ m ∣ (k : O) - (-1) := by
      have := Nat.cast_dvd_cast (α := O) (hl.trans h2)
      simpa using this
    have h5 := h1.add ((h4.trans (sub_dvd_pow_sub_pow _ _ e)).mul_right (ψ k))
    rw [h3, hψ] at h5
    rw [MonoidHom.inv_apply]
    set u := Chr.Psi l e (Chr.dirG ℚ Ω ψ) g
    have e0 : (-1 : O) ^ e * (-1) ^ (e + 1) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨e, by ring⟩
    have e1 : ((u⁻¹ : Oˣ) : O) + 1 = (u - (k : O) ^ e * (-1) ^ (e + 1) + ((k : O) ^ e - (-1) ^ e) * (-1) ^ (e + 1)) *
        ((u⁻¹ : Oˣ) : O) := by
      linear_combination ((u⁻¹ : Oˣ) : O) * e0 - u.mul_inv
    rw [e1]; exact h5.mul_right _

private theorem ze_gen {l : ℕ} [Fact l.Prime] {f F e : ℕ} [NeZero F] (h : f ∣ F) (he : 1 ≤ e)
    (hF : ∀ p : ℕ, p.Prime → p ∣ F → p = l ∨ p ∣ f) (χ : DirichletCharacter (PadicAlgCl l) f)
    (hχ : ∀ x, ‖χ x‖ ≤ 1) :
    ‖Bern.genB (e + 1) (DirichletCharacter.changeLevel h χ : ZMod F → PadicAlgCl l)‖ =
      ‖Bern.genB (e + 1) (χ : ZMod f → PadicAlgCl l)‖ := by
  rw [Bern.b_level h (e + 1) χ (NeZero.pos F) (by omega), norm_mul, norm_prod, Finset.prod_eq_one, mul_one]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rcases hF p hpp (Nat.dvd_of_mem_primeFactors hp) with rfl | hd
  · have h1 : ‖(p : PadicAlgCl p)‖ < 1 := by
      have : (p : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
      rw [this, norm_algebraMap']; exact Padic.norm_p_lt_one
    have h2 : ‖-(χ p * (p : PadicAlgCl p) ^ (e + 1 - 1))‖ < ‖(1 : PadicAlgCl p)‖ := by
      rw [norm_neg, norm_mul, norm_pow, norm_one]
      exact mul_lt_one_of_nonneg_of_lt_one_right (hχ _) (by positivity) (pow_lt_one₀ (norm_nonneg _) h1 (by omega))
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le, norm_one]
  · rw [MulChar.map_nonunit χ (a := (p : ZMod f)) (by
      rw [ZMod.isUnit_iff_coprime]
      exact fun hc => hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hd))]
    simp

private theorem ze_eq {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have : x = (x - y) + y := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]

private theorem ze_an {K : Type} [NormedField K] [IsUltrametricDist K] {z S v u T d : K} {ε : ℝ} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (h2 : ‖(2 : K)‖ = 1) (hd : ‖d‖ ≤ 1) (h : ‖d * (v * S - 2 * u * T)‖ ≤ ε) (hz : ‖z - S‖ ≤ ε) (hε : ε < ‖d‖ * ‖T‖) :
    ‖z‖ = ‖T‖ := by
  have hw : ‖2 * u * T‖ = ‖T‖ := by rw [norm_mul, norm_mul, h2, hu, one_mul, one_mul]
  have h3 : ‖v * S‖ = ‖2 * u * T‖ := by
    apply ze_eq
    rw [hw]
    rw [norm_mul] at h
    exact lt_of_mul_lt_mul_left (h.trans_lt hε) (norm_nonneg d)
  rw [hw, norm_mul, hv, one_mul] at h3
  rw [← h3]
  apply ze_eq
  rw [h3]
  exact (hz.trans_lt hε).trans_le (mul_le_of_le_one_left (norm_nonneg _) hd)

theorem UpperTheory.V.ML.zEval :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l), l ≠ 2 → ∀ (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f) (e : ℕ), 1 ≤ e → ψ.IsPrimitive → ψ (-1) = (-1) ^ (e + 1) →
    (∃ g : G ℚ Ω, IsUnit ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : c.Oˣ) : c.O) - (chiO ℚ Ω l c.O g : c.O))) →
    ∀ a : c.O, (a : PadicAlgCl l) = alN (e + 1) (ψ.ringHomComp c.O.val.toRingHom) → ∀ a₀ : c.O, a₀ ≠ 0 →
    ∃ (m b : ℕ) (_ : NeZero (ordCompl[l] f * l ^ m)) (σ : (ZMod (ordCompl[l] f * l ^ m))ˣ → G ℚ Ω), Dat l (ordCompl[l] f) m (ordCompl[l] f * l ^ m) (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ ∧
      b < ordCompl[l] f * l ^ m ∧ (∀ t, Lifts (ordCompl[l] f * l ^ m) t (σ t)) ∧ a₀ * zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b ∣ (l : c.O) ^ m ∧ zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b ∣ a := by
  intro Ω _ _ _ l hlp c hl2 f _ ψ e he hprim hpar hg a ha a₀ ha₀
  have hp : l.Prime := hlp.out
  obtain ⟨hle, hdvd⟩ := ze_norm c
  have hunit : ∀ x : c.O, IsUnit x → ‖(x : PadicAlgCl l)‖ = 1 := by
    rintro _ ⟨u, rfl⟩
    have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : c.Oˣ)
    have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
    nlinarith
  have hdn : ∀ x y : c.O, x ∣ y → ‖(y : PadicAlgCl l)‖ ≤ ‖(x : PadicAlgCl l)‖ := by
    rintro x _ ⟨y, rfl⟩
    rw [Subalgebra.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hle y)
  have hnat : ∀ n : ℕ, ‖(n : PadicAlgCl l)‖ ≤ 1 := fun n => by simpa using hle n
  have hnu : ∀ n : ℕ, ¬ l ∣ n → ‖(n : PadicAlgCl l)‖ = 1 := fun n hn => by
    simpa using hunit n ((dvrFacts l c.O).2.2.2.2.2.2.2.2 n hn)
  have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']; exact Padic.norm_p_lt_one
  set ψ' : DirichletCharacter (PadicAlgCl l) f := ψ.ringHomComp c.O.val.toRingHom with hψ'
  have hv : ∀ x, ψ' x = ((ψ x : c.O) : PadicAlgCl l) := fun x => rfl
  have hpar' : ψ' (-1) = (-1) ^ (e + 1) := by rw [hv, hpar]; simp
  have hprim' : ψ'.IsPrimitive := ((Bern.b_condmap c.O.val.toRingHom Subtype.val_injective ψ).1).trans hprim
  have hB : Bern.Bprim (e + 1) ψ' = Bern.genB (e + 1) (ψ' : ZMod f → PadicAlgCl l) :=
    ((Bern.b_primeq (e + 1) ψ').1 hprim').1
  have hB0 := (Bern.b_nzany ψ' (e + 1) (by omega) hpar').1
  have he0 : ((e : PadicAlgCl l) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  have hd0 : (Stk.dk (e + 1) : PadicAlgCl l) ≠ 0 := by exact_mod_cast (Stk.dk_pos (Nat.succ_pos e)).ne'
  have ha0 : (a₀ : PadicAlgCl l) ≠ 0 := fun h => ha₀ (Subtype.ext h)
  set T : ℝ := ‖Bern.Bprim (e + 1) ψ' / (e + 1)‖ with hT
  have hTpos : 0 < T := norm_pos_iff.2 (div_ne_zero hB0 he0)
  have hpos : 0 < ‖(a₀ : PadicAlgCl l)‖ * (‖(Stk.dk (e + 1) : PadicAlgCl l)‖ * T) :=
    mul_pos (norm_pos_iff.2 ha0) (mul_pos (norm_pos_iff.2 hd0) hTpos)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hl1
  obtain ⟨m, hm1, hmf, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ f.factorization l ≤ m ∧
      ‖(l : PadicAlgCl l) ^ m‖ < ‖(a₀ : PadicAlgCl l)‖ * (‖(Stk.dk (e + 1) : PadicAlgCl l)‖ * T) :=
    ⟨n + f.factorization l + 1, by omega, by omega, by
      rw [norm_pow]
      exact (pow_le_pow_of_le_one (norm_nonneg _) hl1.le (by omega)).trans_lt hn⟩
  have hF0 : NeZero (ordCompl[l] f * l ^ m) :=
    ⟨mul_ne_zero (Nat.ordCompl_pos l (NeZero.ne f)).ne' (pow_ne_zero _ hp.ne_zero)⟩
  have hfF : f ∣ ordCompl[l] f * l ^ m := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self f l, mul_comm]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow l hmf)
  have hlF : l ^ m ∣ ordCompl[l] f * l ^ m := dvd_mul_left _ _
  have hFp : ∀ p : ℕ, p.Prime → p ∣ ordCompl[l] f * l ^ m → p = l ∨ p ∣ f := fun p hpp hd =>
    (hpp.dvd_mul.1 hd).elim (fun h => Or.inr (h.trans (Nat.ordCompl_dvd f l)))
      fun h => Or.inl ((Nat.prime_dvd_prime_iff_eq hpp hp).1 (hpp.dvd_of_dvd_pow h))
  have hcop : (ordCompl[l] f).Coprime l := (Nat.coprime_ordCompl hp (NeZero.ne f)).symm
  refine ⟨m, ?_⟩
  generalize hF : ordCompl[l] f * l ^ m = F at hF0 hfF hlF hFp ⊢
  obtain ⟨hd1, hd2⟩ := ze_dat (Ω := Ω) l ψ e hlF hfF hpar
  choose σ hσ' using (galBasic Ω F (NeZero.ne F)).2.2.2.1
  obtain ⟨g, hg'⟩ := id hg
  set b := ((Chr.cls ℚ Ω F g : (ZMod F)ˣ) : ZMod F).val with hb
  have hbc : b.Coprime F := ZMod.val_coe_unit_coprime _
  have hgb : Pows F b g := fun x hx => Chr.cls_spec F g x hx
  have hχ : ∀ k : ℕ, k.Coprime F → DirichletCharacter.changeLevel hfF ψ' (k : ZMod F) = ψ' (k : ZMod f) := fun k hk => by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ' hfF (ZMod.unitOfCoprime k hk)
    rwa [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hfF] at this
  have hχ1 : DirichletCharacter.changeLevel hfF ψ' (-1) = (-1) ^ (e + 1) := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ' hfF (-1)
    rw [Units.val_neg, Units.val_one, ZMod.cast_neg hfF, ZMod.cast_one hfF] at this
    rw [this, hpar']
  have hc := zCong l F m e b hlF hm1 he hbc _ hχ1
  have hlb : ¬ l ∣ b := fun h =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hbc h ((dvd_pow_self l (by omega)).trans hlF))
  have hψb : ‖ψ' (b : ZMod f)‖ = 1 := by
    rw [hv, ← ze_dir ψ hfF hbc hgb]; exact hunit _ (Units.isUnit _)
  have hlm : ‖(l : PadicAlgCl l) ^ m‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  have hu : ‖ψ' (b : ZMod f) * (b : PadicAlgCl l) ^ (e + 1) - 1‖ = 1 := by
    have h1 := ze_psi l ψ e hlF hfF hbc hgb
    have h2 := ze_chi l c.O hlF hgb
    rw [MonoidHom.inv_apply] at hg'
    set u := Chr.Psi l e (Chr.dirG ℚ Ω ψ) g
    set w := (chiO ℚ Ω l c.O g : c.O)
    have h3 := hunit _ (hg'.mul u.isUnit).neg
    have h4 : (l : c.O) ^ m ∣ (ψ (b : ZMod f) * (b : c.O) ^ (e + 1) - 1) - -((((u⁻¹ : c.Oˣ) : c.O) - w) * u) := by
      have := ((h1.mul_right (b : c.O)).add (h2.mul_right (u : c.O))).neg_right
      convert this using 1
      linear_combination u.inv_mul
    have h5 := hdn _ _ h4
    rw [← h3]
    apply ze_eq
    rw [h3]
    refine lt_of_le_of_lt ?_ hlm
    simpa [hv] using h5
  have hz : ‖((zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b : c.O) : PadicAlgCl l) - ∑ t : (ZMod F)ˣ, (th F b t : PadicAlgCl l) *
      (((t : ZMod F).val : PadicAlgCl l) ^ e * DirichletCharacter.changeLevel hfF ψ' t)‖ ≤ ‖(l : PadicAlgCl l) ^ m‖ := by
    have h1 : (l : c.O) ^ m ∣ zVal (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ σ b - ∑ t : (ZMod F)ˣ, (th F b t : c.O) *
        (((t : ZMod F).val : c.O) ^ e * ψ (t : ZMod F).val) := by
      rw [zVal, zSum, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun t _ => ?_
      rw [← mul_sub, MonoidHom.inv_apply, inv_inv]
      exact (ze_psi l ψ e hlF hfF (ZMod.val_coe_unit_coprime t) (hσ' t)).mul_left _
    have h2 : ∀ t : (ZMod F)ˣ, DirichletCharacter.changeLevel hfF ψ' t = ((ψ (t : ZMod F).val : c.O) : PadicAlgCl l) := fun t => by
      rw [← hv, ← hχ _ (ZMod.val_coe_unit_coprime t), ZMod.natCast_zmod_val]
    have h3 := hdn _ _ h1
    simp only [h2]
    push_cast at h3
    exact h3
  have hT' : ‖Bern.genB (e + 1) (DirichletCharacter.changeLevel hfF ψ' : ZMod F → PadicAlgCl l) / (e + 1)‖ = T := by
    rw [hT, norm_div, norm_div, ze_gen hfF he hFp ψ' (fun x => hle _), hB]
  have hzT := ze_an (by rw [hχ b hbc, norm_mul, norm_pow, hnu b hlb, hψb, one_pow, one_mul]) (by rw [hχ b hbc]; exact hu)
    (by simpa using hnu 2 fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)) (hnat _) hc hz
    (by rw [hT']; exact hm.trans_le (mul_le_of_le_one_left (by positivity) (hle _)))
  rw [hT'] at hzT
  refine ⟨b, hF0, σ, ⟨hl2, hcop, hm1, hF.symm, hd1, hd2, hg⟩, ZMod.val_lt _, hσ', hdvd _ _ ?_, hdvd _ _ ?_⟩
  · rw [Subalgebra.coe_mul, norm_mul, hzT]
    push_cast
    exact hm.le.trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hTpos.le (hnat _)) (norm_nonneg _))
  · rw [hzT, ha, alN, hT, norm_mul, norm_div, le_div_iff₀ (norm_pos_iff.2 he0)]
    have h1 := hnat (Bern.den f (e + 1))
    have h2 := hnat (e + 1)
    push_cast at h2
    exact (mul_le_of_le_one_right (by positivity) h2).trans (mul_le_of_le_one_left (norm_nonneg _) h1)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem valuation_natCast_le_one_primitive_frobenius_fixed {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) :
    A.valuation (n : Ω) ≤ 1 := by
  have h := A.valuation_le_one (n : A)
  simpa using h

private theorem over_mul {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (m n : ℕ) :
    Over A (m * n) ↔ Over A m ∨ Over A n := by
  have hm := valuation_natCast_le_one_primitive_frobenius_fixed A m
  have hn := valuation_natCast_le_one_primitive_frobenius_fixed A n
  simp only [Over, Nat.cast_mul, map_mul]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : A.valuation (m : Ω) = 1 := le_antisymm hm hc.1
    have h2 : A.valuation (n : Ω) = 1 := le_antisymm hn hc.2
    rw [h1, h2, one_mul] at h
    exact lt_irrefl _ h
  · rintro (h | h)
    · calc A.valuation (m : Ω) * A.valuation (n : Ω) ≤ A.valuation (m : Ω) * 1 := mul_le_mul' le_rfl hn
        _ = A.valuation (m : Ω) := mul_one _
        _ < 1 := h
    · calc A.valuation (m : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) := mul_le_mul' hm le_rfl
        _ = A.valuation (n : Ω) := one_mul _
        _ < 1 := h

private theorem over_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l k : ℕ) (h : Over A (l ^ k)) : Over A l := by
  by_contra hc
  have h1 : A.valuation (l : Ω) = 1 := le_antisymm (valuation_natCast_le_one_primitive_frobenius_fixed A l) (not_lt.mp hc)
  simp only [Over, Nat.cast_pow, map_pow, h1, one_pow] at h
  exact lt_irrefl _ h

private theorem over_pow_iff_over_of_one_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l m : ℕ) (hm : 1 ≤ m) :
    Over A (l ^ m) ↔ Over A l := by
  constructor
  · exact over_pow A l m
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, over_mul]
    exact Or.inl h

private theorem over_lev {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l f m : ℕ) (hm : 1 ≤ m) :
    Over A (ordCompl[l] f * l ^ m) ↔ Over A (f * l) := by
  have hf : f * l = ordCompl[l] f * l ^ f.factorization l * l := by
    rw [mul_comm (ordCompl[l] f), Nat.ordProj_mul_ordCompl_eq_self]
  rw [hf, over_mul A (ordCompl[l] f * l ^ f.factorization l) l, over_mul A (ordCompl[l] f) (l ^ f.factorization l),
    over_mul A (ordCompl[l] f) (l ^ m), over_pow_iff_over_of_one_le A l m hm]
  constructor
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (over_pow A l _ h)
    · exact Or.inr h

private theorem shT_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]
    (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) {F F' : ℕ} (h : ∀ A : ValuationSubring Ω, Over A F ↔ Over A F') (a : O) :
    ShT W α δ F a = ShT W α δ F' a := by
  ext c
  show (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [h]

private theorem isUnit_inv_sub_one_iff_isUnit_sub_one {R : Type} [CommRing R] (u : Rˣ) :
    IsUnit ((↑u⁻¹ : R) - 1) ↔ IsUnit ((u : R) - 1) := by
  have hx : ((↑u⁻¹ : R) - 1) = -(↑u⁻¹ : R) * ((u : R) - 1) := by
    rw [neg_mul, mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [hx, IsUnit.mul_iff]
  exact ⟨fun h => h.2, fun h => ⟨(Units.isUnit _).neg, h⟩⟩

private theorem prim_case (hR : Rec) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (c : HV.Coef l) (h2 : l ≠ 2) (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f) (e : ℕ) (he : 1 ≤ e)
    (hp : ψ.IsPrimitive) (ho : ¬ l ∣ orderOf ψ) (hs : ψ (-1) = (-1) ^ (e + 1)) (a : c.O)
    (ha : (a : PadicAlgCl l) = alN (e + 1) (ψ.ringHomComp c.O.val.toRingHom)) :
    Chr.V l e (Chr.dirG ℚ Ω ψ) ≤ IsDiscreteValuationRing.addVal c.O a := by
  haveI := c.dvr
  haveI := c.fin
  have hl2 : ¬ l ∣ 2 := by
    intro h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).mp h)
  obtain ⟨hram, hunr, hunit⟩ := primRam Ω l c f ψ hp ho
  have hχ : ∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine A, chiO ℚ Ω l c.O g = 1 := by
    intro A hA g hg
    have hk := (places ℚ Ω l A).2.2.2 hA hg
    rw [MonoidHom.mem_ker] at hk
    simp [chiO, hk]
  have hαg : ∀ g, chiO ℚ Ω l c.O g = 1 →
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g = (Chr.dirG ℚ Ω ψ g)⁻¹ := by
    intro g hg
    simp [Chr.Psi, hg]
  unfold Chr.V Chr.VS
  rw [Chr.rho_eq]
  by_cases hex : ∃ g, IsUnit ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : c.Oˣ) : c.O) - ((chiO ℚ Ω l c.O g : c.Oˣ) : c.O))
  · have hfacts := dvrFacts l c.O
    have hlnu : ¬ IsUnit (l : c.O) := by
      rintro ⟨u, hu⟩
      have h0 := IsDiscreteValuationRing.addVal_eq_zero_of_unit u
      rw [hu, ← hfacts.2.2.2.2.2.2.2.1] at h0
      exact hfacts.2.2.2.2.2.1 h0
    obtain ⟨m₁, b₁, hNZ₁, σ₁, hD₁, -, -, -, -⟩ := zEval Ω l c h2 f ψ e he hp hs hex a ha 1 one_ne_zero
    obtain ⟨δ, hδ⟩ := (galBasic Ω (f / l ^ f.factorization l * l ^ m₁) (NeZero.ne _)).2.2.2.1 (-1)
    have hodd := hD₁.odd δ hδ
    have hδu : IsUnit ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) - 1) := by
      have hmax : ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) + 1) ∈ IsLocalRing.maximalIdeal c.O := by
        obtain ⟨k, hk⟩ := hodd
        rw [hk, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply hlnu
        have hpow : IsUnit ((l : c.O) ^ m₁) := isUnit_of_mul_isUnit_left hu
        exact (isUnit_pow_iff (by have := hD₁.pos; omega)).mp hpow
      by_contra hnu
      have h2m : ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) - 1) ∈ IsLocalRing.maximalIdeal c.O :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hsub := Ideal.sub_mem _ hmax h2m
      rw [show ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) + 1) -
          ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) - 1) = ((2 : ℕ) : c.O) by push_cast; ring] at hsub
      exact (IsLocalRing.mem_maximalIdeal _).mp hsub (hfacts.2.2.2.2.2.2.2.2 2 hl2)
    refine shaToShT Ω l c.O _ δ hδu (f * l) (Nat.mul_ne_zero (NeZero.ne f) hl.out.ne_zero) ?_ ?_ _ ?_
    · intro A hA g hg
      rw [over_mul, not_or] at hA
      rw [hαg g (hχ A hA.2 g hg), hunr A hA.1 g hg, inv_one]
    · intro A hA hAl
      have hf : Over A f := by
        rcases (over_mul A f l).mp hA with h | h
        · exact h
        · exact absurd h hAl
      obtain ⟨g, hg, hu⟩ := hram A hf
      refine ⟨g, hg, ?_⟩
      rw [hαg g (hχ A hAl g hg), isUnit_inv_sub_one_iff_isUnit_sub_one]
      exact hu
    · intro a₀ ha₀
      obtain ⟨m, b, hNZ, σ, hD, hb, hσ, hdiv, hza⟩ := zEval Ω l c h2 f ψ e he hp hs hex a ha a₀ ha₀
      have hc := count hR Ω l c.O (f / l ^ f.factorization l) m _ b _ hD hb δ hδu σ hσ a₀ hdiv
      rw [shT_congr _ δ (F' := f * l) (fun A => over_lev A l f m hD.pos)] at hc
      exact hc.trans (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hza)
  · push_neg at hex
    set_option synthInstance.maxHeartbeats 200000 in
      rw [exc Ω l c.O h2 _ hex ?_, Module.length_bot]
    · exact zero_le
    · intro A hA g hg
      rw [hαg g (hχ A hA g hg)]
      by_contra hne
      have h1 : Chr.dirG ℚ Ω ψ g ≠ 1 := fun h => hne (by rw [h, inv_one])
      have hx := hex g
      rw [hαg g (hχ A hA g hg), hχ A hA g hg, Units.val_one, isUnit_inv_sub_one_iff_isUnit_sub_one] at hx
      exact hx (hunit g h1)

private theorem lev_case (hR : Rec) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (c : HV.Coef l) (h2 : l ≠ 2) (f N : ℕ) [NeZero f] [NeZero N] (h : f ∣ N) (φ : DirichletCharacter c.O f) (e : ℕ)
    (he : 1 ≤ e) (hp : φ.IsPrimitive) (ho : ¬ l ∣ orderOf (DirichletCharacter.changeLevel h φ))
    (hs : DirichletCharacter.changeLevel h φ (-1) = (-1) ^ (e + 1)) (a : c.O)
    (ha : (a : PadicAlgCl l) = alN (e + 1) ((DirichletCharacter.changeLevel h φ).ringHomComp c.O.val.toRingHom)) :
    Chr.V l e (Chr.dirG ℚ Ω (DirichletCharacter.changeLevel h φ)) ≤ IsDiscreteValuationRing.addVal c.O a := by
  haveI := c.dvr
  haveI := c.fin
  have hG : Chr.dirG ℚ Ω (DirichletCharacter.changeLevel h φ) = Chr.dirG ℚ Ω φ := by
    unfold Chr.dirG
    rw [DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_assoc, (Chr.clsFacts ℚ Ω N).2.1 f h]
  have ho' : ¬ l ∣ orderOf φ := by
    rwa [orderOf_injective _ (DirichletCharacter.changeLevel_injective h) φ] at ho
  have hs' : φ (-1) = (-1) ^ (e + 1) := by
    have hc := DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := φ) h (a := -1) isCoprime_one_left.neg_left
    push_cast at hc
    rw [← hc]
    exact hs
  have hrc : (DirichletCharacter.changeLevel h φ).ringHomComp c.O.val.toRingHom =
      DirichletCharacter.changeLevel h (φ.ringHomComp c.O.val.toRingHom) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hmem : alN (e + 1) (φ.ringHomComp c.O.val.toRingHom) ∈ c.O :=
    (Bern.b_primmem (e + 1) (φ.ringHomComp c.O.val.toRingHom)).2.1 c.O.toSubring
      (fun u => by simp [MulChar.ringHomComp_apply])
  obtain ⟨k, hk⟩ := Bern.den_dvd h (e + 1)
  have hdvd : (⟨_, hmem⟩ : c.O) ∣ a := by
    refine ⟨(k : c.O), Subtype.ext ?_⟩
    rw [ha, hrc]
    simp only [alN, ((Bern.b_primeq (e + 1) (φ.ringHomComp c.O.val.toRingHom)).2 N h).1, hk]
    push_cast
    ring
  have hP := prim_case hR Ω l c h2 f φ e he hp ho' hs' ⟨_, hmem⟩ rfl
  rw [hG]
  exact hP.trans (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hdvd)

theorem UpperTheory.V.ML.vChar :
    Rec → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l), l ≠ 2 → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N) (e : ℕ), 1 ≤ e → ¬ l ∣ orderOf ψ → ψ (-1) = (-1) ^ (e + 1) →
    ∀ a : c.O, (a : PadicAlgCl l) = alN (e + 1) (ψ.ringHomComp c.O.val.toRingHom) → Chr.V l e (Chr.dirG ℚ Ω ψ) ≤ IsDiscreteValuationRing.addVal c.O a := by
  intro hR Ω _ _ _ l _ c h2 N _ ψ e he ho hs a ha
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have key := lev_case hR Ω l c h2 ψ.conductor N ψ.conductor_dvd_level ψ.primitiveCharacter e he
    ψ.primitiveCharacter_isPrimitive
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at key
  exact key ho hs a ha
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.psiOf :
    Rec → PsiBound := by
  intro hR E Ω _ _ _ _ _ _ _ _ _ _ N _ ρ hρ l _ hl2 hlE O _ _ e he ψ hodd a ha
  haveI : IsGalois ℚ E := inferInstance
  let c : HV.Coef l := ⟨O, inferInstance, inferInstance⟩
  let ψ' : DirichletCharacter (↥c.O) N := MulChar.ofUnitHom (ψ.comp ρ)
  have hcomp : MulChar.ringHomComp ψ' c.O.val.toRingHom = chiOf ρ ψ := by
    ext b
    simp [ψ', chiOf, MulChar.ringHomComp_apply]
  have hord : ¬ l ∣ orderOf ψ' := by
    intro hdiv
    apply hlE
    refine hdiv.trans ?_
    rw [← IsGalois.card_aut_eq_finrank]
    apply orderOf_dvd_of_pow_eq_one
    ext b
    simp only [ψ', MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MulChar.one_apply_coe]
    have h2 : ψ (ρ b) ^ Fintype.card Gal(E/ℚ) = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    have h3 := congrArg (fun u : (↥O)ˣ => ((u : ↥O) : PadicAlgCl l)) h2
    simpa using h3
  have hodd' : ψ' (-1) = (-1) ^ (e + 1) := by
    have h1 := congrArg (fun χ => χ (-1)) hcomp
    simp only [MulChar.ringHomComp_apply] at h1
    apply Subtype.val_injective
    rw [hodd] at h1
    simpa using h1
  have key := vChar hR Ω l c hl2 N ψ' e he hord hodd' a (by rw [hcomp]; exact ha)
  obtain ⟨_, hker, hlift⟩ := galQuot ℚ E Ω
  have hρσ : ∀ σ : G ℚ Ω, ρ (Chr.cls ℚ Ω N σ) = AlgEquiv.restrictNormalHom E σ := by
    intro σ
    have h1 := hρ (Chr.cls ℚ Ω N σ) σ.toRingEquiv (fun x hx => Chr.cls_spec N σ x hx)
    have h2 := hlift σ
    ext x
    apply (algebraMap E Ω).injective
    exact (h1 x).symm.trans (h2 x)
  have hdir : Chr.dirG ℚ Ω ψ' = ψ.comp (AlgEquiv.restrictNormalHom E) := by
    ext σ
    simp [Chr.dirG, ψ', hρσ]
  obtain ⟨_, hopen, hidx⟩ := galEmbTop ℚ E Ω
  haveI : (galOf ℚ E Ω).Normal := by
    rw [← hker]
    infer_instance
  have hle : galOf ℚ E Ω ≤ (ψ.comp (AlgEquiv.restrictNormalHom E)).ker := by
    rw [← hker]
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  have heig := Chr.eigV ℚ Ω l O e (ψ.comp (AlgEquiv.restrictNormalHom E)) (galOf ℚ E Ω) hopen hle
    (by rw [hidx]; exact hlE)
  have hpsi : psiLen Ω e ψ = Chr.eigL l e (galOf ℚ E Ω) (ψ.comp (AlgEquiv.restrictNormalHom E)) := rfl
  rw [hpsi, heig, ← hdir]
  exact key
