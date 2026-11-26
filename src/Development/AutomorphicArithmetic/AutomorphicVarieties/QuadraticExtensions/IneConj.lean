module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.ineConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : G F Ω), (∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B) ∧
      (∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1) ∧ ∀ (N : ℕ), ∀ s ∈ ineOff F Ω N, v⁻¹ * s * v ∈ ineOff F Ω N := by
  intro F Ω _ _ _ _ _ v
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), y ≠ 0 → (A.valuation y < 1 ↔ y⁻¹ ∉ A) := by
    intro A y hy
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
  have hL : ∀ (w : G F Ω) (B : ValuationSubring Ω) (x : Ω), (w • B).valuation x < 1 ↔ B.valuation (w⁻¹ • x) < 1 := by
    intro w B x
    by_cases hx : x = 0
    · subst hx
      simp
    have hx' : w⁻¹ • x ≠ 0 := by simpa using hx
    rw [hlt _ _ hx, hlt _ _ hx', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'']
  have p1 : ∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B := by
    intro B g hg
    obtain ⟨hd, hi⟩ := hg
    refine ⟨?_, ?_⟩
    · have hd' : g • (v • B) = v • B := hd
      show (v⁻¹ * g * v) • B = B
      rw [mul_smul, mul_smul, hd', inv_smul_smul]
    · intro x hx
      have hvx : (v • B).valuation (v x) ≤ 1 := by
        rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ← ValuationSubring.valuation_le_one_iff]
        simpa [AlgEquiv.smul_def] using hx
      have h2 := hi (v x) hvx
      rw [hL] at h2
      convert h2 using 2
      simp [AlgEquiv.smul_def, map_sub, AlgEquiv.mul_apply]
  have p2 : ∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1 := by
    intro B N
    rw [hL]
    simp [AlgEquiv.smul_def]
  refine ⟨p1, p2, ?_⟩
  rintro N s ⟨A, hA, hs⟩
  have hA' : v • (v⁻¹ • A) = A := smul_inv_smul v A
  refine ⟨v⁻¹ • A, ?_, ?_⟩
  · rw [← p2, hA']
    exact hA
  · apply p1
    rw [hA']
    exact hs
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem mem_princ_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : G ℚ Ω) : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ g ∈ (galChar Ω (l ^ n)).ker := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have e : cycZ ℚ Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
  have h1 : cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔
      (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1 := by
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]
    rfl
  rw [h1, cyclotomicCharacter.toZModPow, MonoidHom.mem_ker, Units.ext_iff]
  rfl

theorem UpperTheory.V.Two.levChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (U : Subgroup (G ℚ Ω)), levU l U n = U ⊓ (galChar Ω (l ^ n)).ker ∧ (cycZ ℚ Ω l).ker ≤ (galChar Ω (l ^ n)).ker := by
  intro Ω _ _ _ l _ n U
  refine ⟨?_, fun g hg => ?_⟩
  · ext g
    rw [levU, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap, mem_princ_iff]
  · rw [← mem_princ_iff, MonoidHom.mem_ker.1 hg]
    exact one_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardClDual
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem cardLe_dual_zmod_card (l : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V] [Module (ZMod l) V]
    [Finite V] : CardLe (V →ₗ[ZMod l] ZMod l) (Nat.card V) := by
  refine ⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩
  show Nat.card (Module.Dual (ZMod l) V) ≤ _
  rw [Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]

private theorem cardLe_hom (A : Type) [CommGroup A] [Finite A] (l : ℕ) [Fact l.Prime] (P : Type) (θ : P → A → ZMod l)
    (hθ : Function.Injective θ) (hm : ∀ p a b, θ p (a * b) = θ p a + θ p b) :
    CardLe P (Nat.card (A ⧸ (powMonoidHom l : A →* A).range)) := by
  have hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c := by
    intro p c n
    induction n with
    | zero =>
      have h := hm p 1 1
      rw [mul_one] at h
      simpa using h
    | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
  have h1 : ∀ p, θ p 1 = 0 := fun p => by simpa using hpow p 1 0
  have hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0 := by
    intro v
    change (Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  let φ : P → A →* Multiplicative (ZMod l) := fun p =>
    { toFun := fun a => Multiplicative.ofAdd (θ p a)
      map_one' := by
        show Multiplicative.ofAdd (θ p 1) = 1
        rw [h1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (θ p (a * b)) = _
        rw [hm]
        rfl }
  let ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l) := fun p =>
    QuotientGroup.lift _ (φ p) (by
      rintro _ ⟨c, rfl⟩
      show Multiplicative.ofAdd (θ p (c ^ l)) = 1
      rw [hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl)
  let Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l) := fun p =>
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by
      show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _
      rw [map_mul]
      rfl)
  have hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a := fun p a => rfl
  have hinj : Function.Injective Φ := by
    intro p q h
    apply hθ
    funext a
    rw [← hΦ p a, ← hΦ q a, h]
  letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV
  exact CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _
    ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range))
      (M₁ := ZMod l)).comp hinj)

theorem UpperTheory.V.Two.cardClDual :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (N : ℕ), CardLe (ClDual K N (ZMod l) (ZMod l)) (Nat.card (ClassGroup (𝓞 K) ⧸ (powMonoidHom l : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range)) := by
  intro K _ _ l _ N
  exact cardLe_hom (ClassGroup (𝓞 K)) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem ker_congr (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m n : ℕ) [NeZero m] [NeZero n]
    (h : m = n) : (galChar Ω m).ker = (galChar Ω n).ker := by
  subst h
  rfl

private theorem prim_lemma (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m Ω)
    (Polynomial.degree_cyclotomic_pos m Ω (NeZero.pos m)).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

private theorem galChar_eq_of_apply_primitiveRoot_eq_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m]
    (g : G ℚ Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ m) (k : ℕ) (hk : g ζ = ζ ^ k) :
    (galChar Ω m g : ZMod m) = k := by
  have h1 := galChar_spec m g ζ hζ.pow_eq_one
  rw [hk] at h1
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, NeZero.pos m, hζ.pow_eq_one⟩
  have h2 := hfin.pow_eq_pow_iff_modEq.mp h1
  rw [← hζ.eq_orderOf] at h2
  rw [← ZMod.natCast_zmod_val (galChar Ω m g : ZMod m)]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h2).symm

private theorem galChar_val_cast_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    (((galChar Ω N g : ZMod N).val : ℕ) : ZMod m) = (galChar Ω m g : ZMod m) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω N
  obtain ⟨d, hd⟩ := h
  have hμ : IsPrimitiveRoot (ζ ^ d) m := hζ.pow (NeZero.pos N) (by rw [hd, mul_comm])
  refine (galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g (ζ ^ d) hμ _ ?_).symm
  rw [map_pow, galChar_spec N g ζ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm]

private theorem unitsMap_galChar_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    ZMod.unitsMap h (galChar Ω N g) = galChar Ω m g := by
  ext
  rw [← galChar_val_cast_eq_galChar_of_dvd Ω m N h g, ← ZMod.cast_eq_val]
  rfl

private theorem galChar_surjective (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    Function.Surjective (galChar Ω m) := by
  intro u
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  have hcop : Nat.Coprime (u : ZMod m).val m := ZMod.val_coe_unit_coprime u
  have hμ : IsPrimitiveRoot (ζ ^ (u : ZMod m).val) m := hζ.pow_of_coprime _ hcop
  have hmin : minpoly ℚ (ζ ^ (u : ZMod m).val) = minpoly ℚ ζ := by
    have e1 := Polynomial.cyclotomic_eq_minpoly_rat hμ (NeZero.pos m)
    have e2 := Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos m)
    convert e1.symm.trans e2 <;> exact Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  have hg' : g ζ = ζ ^ (u : ZMod m).val := (AlgEquiv.smul_def g ζ).symm.trans hg
  refine ⟨g, ?_⟩
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ _ hg', ZMod.natCast_zmod_val]

private theorem isOpen_galChar_ker (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    IsOpen ((galChar Ω m).ker : Set (G ℚ Ω)) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos m)).tower_top
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro g hg
  have hfix : g ζ = ζ ^ 1 := by
    rw [pow_one]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
      (IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ))
  rw [MonoidHom.mem_ker]
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ 1 hfix]
  simp

theorem UpperTheory.V.Two.abBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω], (∀ A B : AbF, abU Ω (A.sup B) = abU Ω A ⊓ abU Ω B) ∧ (∀ A : AbF, (abU Ω A).index = A.deg ∧ A.deg ≠ 0 ∧ IsOpen (abU Ω A : Set (G ℚ Ω)) ∧ (galChar Ω A.m).ker ≤ abU Ω A) ∧
      (∀ (A : AbF) (N : ℕ) [NeZero N], A.m ∣ N → ∀ g, g ∈ abU Ω A ↔ A.ker (galChar Ω N g : ZMod N).val) ∧ ∀ (m : ℕ) [NeZero m], abU Ω (AbF.cyc m) = (galChar Ω m).ker := by
  intro Ω _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B
    ext g
    rw [Subgroup.mem_inf]
    show ZMod.unitsMap (dvd_mul_right A.m B.m) (galChar Ω (A.m * B.m) g) ∈ A.H ∧
        ZMod.unitsMap (dvd_mul_left B.m A.m) (galChar Ω (A.m * B.m) g) ∈ B.H ↔
      galChar Ω A.m g ∈ A.H ∧ galChar Ω B.m g ∈ B.H
    rw [unitsMap_galChar_eq_galChar_of_dvd Ω A.m (A.m * B.m) (dvd_mul_right _ _) g,
      unitsMap_galChar_eq_galChar_of_dvd Ω B.m (A.m * B.m) (dvd_mul_left _ _) g]
  · intro A
    refine ⟨Subgroup.index_comap_of_surjective _ (galChar_surjective Ω A.m), Subgroup.index_ne_zero_of_finite, ?_, ?_⟩
    · refine Subgroup.isOpen_mono ?_ (isOpen_galChar_ker Ω A.m)
      intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
    · intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
  · intro A N _ hN g
    simp only [abU, Subgroup.mem_comap, AbF.ker]
    rw [galChar_val_cast_eq_galChar_of_dvd Ω A.m N hN g]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, hEq⟩
      rwa [← Units.ext hEq]
  · intro m _
    have hm : (AbF.cyc m).m = m := max_eq_left NeZero.one_le
    show Subgroup.comap _ ⊥ = _
    rw [MonoidHom.comap_bot]
    exact ker_congr Ω _ _ hm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DegBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem UpperTheory.V.Two.deg_sup_le (A B : AbF) : (A.sup B).deg ≤ A.deg * B.deg := by
  haveI : NeZero (A.m * B.m) := ⟨(Nat.mul_pos A.pos B.pos).ne'⟩
  have h1 := A.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_right A.m B.m))
  have h2 := B.H.index_comap_of_surjective (ZMod.unitsMap_surjective (dvd_mul_left B.m A.m))
  unfold AbF.deg
  rw [← h1, ← h2]
  exact Subgroup.index_inf_le

private theorem UpperTheory.V.Two.deg_cyc_four : (AbF.cyc 4).deg = 2 := by
  show (⊥ : Subgroup (ZMod 4)ˣ).index = 2
  rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

private theorem UpperTheory.V.Two.deg_quad_dvd (p : ℕ) (hp : p.Prime) : (AbF.quad p).deg ∣ 2 := by
  show ((powMonoidHom 2 : (ZMod (max p 1))ˣ →* _).range).index ∣ 2
  have hp' : (max p 1).Prime := by rwa [max_eq_left hp.pos]
  haveI := Fact.mk hp'
  rw [IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_dvd_right _ _

theorem UpperTheory.V.Two.degBasic :
    (∀ A B : AbF, (A.sup B).deg ≤ A.deg * B.deg) ∧ (AbF.cyc 4).deg = 2 ∧ (∀ p : ℕ, p.Prime → (AbF.quad p).deg ∣ 2) ∧ ∀ (M : AbF) (q d : ℕ), q.Prime → d.Prime → (base2 M q d).deg ≤ 8 * M.deg := by
  refine ⟨deg_sup_le, deg_cyc_four, deg_quad_dvd, fun M q d hq hd => ?_⟩
  have h1 : (withI M).deg ≤ M.deg * 2 := deg_cyc_four ▸ deg_sup_le M (AbF.cyc 4)
  have hq2 := Nat.le_of_dvd two_pos (deg_quad_dvd q hq)
  have hd2 := Nat.le_of_dvd two_pos (deg_quad_dvd d hd)
  calc (base2 M q d).deg ≤ ((withI M).sup (AbF.quad q)).deg * (AbF.quad d).deg := deg_sup_le _ _
    _ ≤ ((withI M).deg * (AbF.quad q).deg) * 2 := Nat.mul_le_mul (deg_sup_le _ _) hd2
    _ ≤ (M.deg * 2 * 2) * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 hq2)
    _ = 8 * M.deg := by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.MuIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.muIff :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] (n : ℕ) [NeZero n], (∃ ζ : L, IsPrimitiveRoot ζ n) ↔ galOf ℚ L Ω ≤ (galChar Ω n).ker := by
  intro Ω _ _ _ L _ _ _ n _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  have key : ∀ g : G ℚ Ω, ∀ z : Ω, IsPrimitiveRoot z n → (g z = z ↔ galChar Ω n g = 1) := by
    intro g z hz
    rw [galChar_spec n g z hz.pow_eq_one]
    have hiff : z ^ ((galChar Ω n g : ZMod n).val) = z ↔
        (((galChar Ω n g : ZMod n).val : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne n)
      have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp hz
      nth_rewrite 2 [← pow_one (u : Ω)]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
        pow_eq_pow_iff_modEq, ← hu.eq_orderOf, ZMod.natCast_eq_natCast_iff]
    rw [hiff, ZMod.natCast_zmod_val, Nat.cast_one, ← Units.val_one, Units.val_inj]
  constructor
  · rintro ⟨ζ, hζ⟩ g hg
    rw [MonoidHom.mem_ker, ← key g _ (hζ.map_of_injective (algebraMap L Ω).injective)]
    exact hg ζ
  · intro hle
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) L
    haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
    obtain ⟨ζ, hζ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) z).mpr (fun f => by
      have hf := hle (galEmb_mem ℚ L Ω f)
      rw [MonoidHom.mem_ker, ← key _ z hz, galEmb_apply] at hf
      exact hf)
    refine ⟨ζ, ?_⟩
    rw [← hζ] at hz
    exact (IsPrimitiveRoot.map_iff_of_injective (algebraMap L Ω).injective).mp hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SupIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem relIndex_sup_normal {Γ : Type} [Group Γ] (K D H : Subgroup Γ) [K.Normal] (hD : D ≤ H) :
    H.relIndex (K ⊔ D) = H.relIndex K := by
  classical
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ D)) fun a b h => ?_) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun a => Quotient.ind' fun b => ?_
    intro h
    simp only [Quotient.map'_mk''] at h
    rw [Quotient.eq''] at h ⊢
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · refine Quotient.ind' fun y => ?_
    obtain ⟨k, hk, d, hd, hkd⟩ := Subgroup.mem_sup_of_normal_left.mp y.2
    refine ⟨Quotient.mk'' ⟨k, hk⟩, ?_⟩
    simp only [Quotient.map'_mk'']
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hy : (y : Γ) = k * d := hkd.symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hy, inv_mul_cancel_left]
    exact hD hd

theorem UpperTheory.V.Two.supIndex :
    ∀ (Γ : Type) [Group Γ] (K W D : Subgroup Γ) [K.Normal] [W.Normal], W.index ≠ 0 → (K ⊔ D).index ≠ 0 → ((W ⊓ K) ⊔ D).index ≠ 0 ∧ ((W ⊓ K) ⊔ D).index ≤ W.index * (K ⊔ D).index := by
  intro Γ _ K W D _ _ hW hKD
  have hLKD : (W ⊓ K) ⊔ D ≤ K ⊔ D := sup_le_sup_right inf_le_right D
  have hDL : D ≤ (W ⊓ K) ⊔ D := le_sup_right
  have hWKL : W ⊓ K ≤ (W ⊓ K) ⊔ D := le_sup_left
  have h1 : ((W ⊓ K) ⊔ D).index = ((W ⊓ K) ⊔ D).relIndex K * (K ⊔ D).index := by
    rw [← relIndex_sup_normal K D _ hDL, Subgroup.relIndex_mul_index hLKD]
  have h2 : ((W ⊓ K) ⊔ D).relIndex K ∣ W.index := by
    have h := Subgroup.relIndex_dvd_of_le_left K hWKL
    rw [Subgroup.inf_relIndex_right] at h
    exact h.trans (Subgroup.relIndex_dvd_index_of_normal W K)
  have h3 : ((W ⊓ K) ⊔ D).relIndex K ≠ 0 := fun h => hW (Nat.eq_zero_of_zero_dvd (h ▸ h2))
  have h4 : ((W ⊓ K) ⊔ D).relIndex K ≤ W.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hW) h2
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact mul_ne_zero h3 hKD
  · rw [h1]
    exact Nat.mul_le_mul_right _ h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have hv := congrArg A.valuation h
  rw [map_pow, map_one] at hv
  exact (pow_eq_one_iff.mp hv).resolve_right hm

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff]
    refine Subring.sum_mem A.toSubring (fun j _ => ?_)
    have hj : η ^ j ∈ A := by
      rw [← ValuationSubring.valuation_le_one_iff, map_pow, h1, one_pow]
    exact hj
  rw [← mul_neg_geom_sum, map_mul, Valuation.map_sub_swap]
  exact mul_lt_one_of_lt_of_le h hS

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  have hS : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have hg := mul_neg_geom_sum η m
    rw [hη, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  have h1 : A.valuation η = 1 := aux_one A hm hη
  have hlt : A.valuation ((m : Ω) - ∑ i ∈ Finset.range m, η ^ i) < 1 := by
    have he : (m : Ω) - ∑ i ∈ Finset.range m, η ^ i = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
      simp [Finset.sum_sub_distrib]
    rw [he]
    exact Valuation.map_sum_lt _ one_ne_zero (fun i _ => power_bounds_of_between A h1 h i)
  rw [hS, sub_zero] at hlt
  exact hv hlt

private theorem inertia_fixes_prime_to_roots {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hA : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) {ζ : Ω} (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have hI : g ∈ Inertia (F := ℚ) A := hg
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hζ
    exact zero_ne_one hζ
  have hv1 := aux_one A hm hζ
  have key := hI.2 ζ hv1.le
  have hη : (g ζ * ζ⁻¹) ^ m = 1 := by
    rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : A.valuation (g ζ * ζ⁻¹ - 1) < 1 := by
    have he : g ζ * ζ⁻¹ - 1 = (g ζ - ζ) * ζ⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, map_mul, map_inv₀, hv1, inv_one, mul_one]
    exact key
  have hfin := root_of_unity_eq_one_of_close_residue A hm hA hη hlt
  rwa [mul_inv_eq_one₀ hζ0] at hfin

theorem UpperTheory.V.Two.ineChar :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] (A : ValuationSubring Ω), ¬ A.valuation (m : Ω) < 1 → Ine (F := ℚ) A ≤ (galChar Ω m).ker := by
  intro Ω _ _ _ m _ A hA g hg
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hfix := inertia_fixes_prime_to_roots A (NeZero.ne m) hA hg hz.pow_eq_one
  rw [galChar_spec m g z hz.pow_eq_one] at hfix
  obtain ⟨u, rfl⟩ := hz.isUnit (NeZero.ne m)
  have hu : IsPrimitiveRoot u m := IsPrimitiveRoot.coe_units_iff.mp hz
  have heq : u ^ ((galChar Ω m g : ZMod m).val) = u ^ 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_one]
    exact hfix
  have hmod := pow_eq_pow_iff_modEq.mp heq
  rw [← hu.eq_orderOf] at hmod
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val ((galChar Ω m g : ZMod m)), ← Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

namespace UpperTheory.V.Two.DyadicOrbitIndex

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [e]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show ((n : ℤ) : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  have e1 : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  have e2 : ((n : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n := by simp
  rw [e1, e2]
  exact map_dvd_iff Rat.ringOfIntegersEquiv.symm

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    have hc : IsCoprime ((l : ℕ) : ℤ) n :=
      ((Nat.prime_iff_prime_int.mp hl.out).coprime_iff_not_dvd).mpr hnd
    obtain ⟨a, b, hab⟩ := hc
    have h1 : A.valuation ((a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    have h2 : (a : Ω) * ((l : ℕ) : Ω) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    rw [h2, map_one] at h1
    exact lt_irrefl _ h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = ((n : ℤ) : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by
      have := Rat.ringOfIntegersEquiv.symm_apply_apply x
      rw [← this]; simp⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA]
  simp

private theorem smul_val_lt [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hA ⊢
  rcases hA with h | h
  · exact Or.inl h
  · refine Or.inr fun h' => h ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h'
    have e : g⁻¹ • ((n : Ω))⁻¹ = ((n : Ω))⁻¹ := by
      show (g⁻¹ : G ℚ Ω) ((n : Ω))⁻¹ = _
      rw [map_inv₀, map_natCast]
    rwa [e] at h'

end UpperTheory.V.Two.DyadicOrbitIndex

open UpperTheory.V.Two.DyadicOrbitIndex in
theorem UpperTheory.V.Two.orbIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) (V : Subgroup (G ℚ Ω)) [V.Normal] (A₀ : ValuationSubring Ω), p.Prime → A₀.valuation (p : Ω) < 1 → (V ⊔ Dec (F := ℚ) A₀).index ≠ 0 → OrbLe V p (V ⊔ Dec (F := ℚ) A₀).index := by
  intro Ω _ _ _ p V hV A₀ hp h0 hi
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)) := Nat.finite_of_card_ne_zero hi
  haveI := Fintype.ofFinite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀))
  refine ⟨Finset.univ.image fun q : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀) => q.out • A₀, ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
  · intro B hB
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hB
    exact smul_val_lt _ _ _ h0
  · intro A hA
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ A₀ h0) (isPlaceOver_vQ A hA)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V ⊔ Dec (F := ℚ) A₀) g
    have hm : (h⁻¹ : G ℚ Ω) ∈ ((V ⊔ Dec (F := ℚ) A₀ : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := inv_mem h.2
    rw [Subgroup.normal_mul] at hm
    obtain ⟨v, hv, d, hd, e⟩ := hm
    set r := (QuotientGroup.mk g : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)).out with hr
    refine ⟨r • A₀, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, r * v * r⁻¹, hV.conj_mem v hv r, ?_⟩
    have hd' : d • A₀ = A₀ := (mem_Dec (F := ℚ)).1 hd
    have eg : g = r * v * d := by
      have e' : v * d = (h : G ℚ Ω)⁻¹ := e
      rw [mul_assoc, e', hh]; group
    rw [eg, mul_smul (r * v) d, hd', smul_smul]
    congr 1; group
end
