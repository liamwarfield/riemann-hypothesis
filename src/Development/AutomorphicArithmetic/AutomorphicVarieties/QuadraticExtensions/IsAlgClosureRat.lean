module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevUAnti
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevelRk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.ExistsNumberFieldIsAbFieldFinrankEqDeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.GenOfRk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.TameGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.QuadStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ShaTwo

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CharStep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem not_valuation_lt_one_of_coprime_of_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p l : ℕ}
    (h : p.Coprime l) (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := by
  intro hl
  have hg := Nat.gcd_eq_gcd_ab p l
  rw [h.gcd_eq_one] at hg
  have hΩ : (1 : Ω) = (p : Ω) * ((p.gcdA l : ℤ) : Ω) + (l : Ω) * ((p.gcdB l : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hg
    push_cast at this
    exact this
  have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => by
    simpa using A.valuation_le_one (z : A)
  have h1 : A.valuation ((p : Ω) * ((p.gcdA l : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hp
  have h2 : A.valuation ((l : Ω) * ((p.gcdB l : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hΩ, map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.V.Two.charStep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (V : Subgroup (G F Ω)) (N p n k : ℕ), p.Coprime l → OrbLe V p k → (∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Ine (F := F) A ≤ V) →
      CardLe (CharOff V (ineOff F Ω N) l) n → CardLe (CharOff V (ineOff F Ω (N * p)) l) (n * l ^ k) := by
  intro F Ω _ _ _ _ _ l _ V N p n k hcop hT hV hN
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨T, hTc, hTp, hTcov⟩ := hT
  have hl : ∀ B ∈ T, ¬ B.valuation (l : Ω) < 1 := fun B hB => not_valuation_lt_one_of_coprime_of_lt_one B hcop (hTp B hB)
  choose γ hγ using fun B : {B // B ∈ T} => tameGen F Ω l B.1 (hl B.1 B.2)
  let L : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l) := fun φ B =>
    (φ : V → ZMod l) ⟨(γ B : G F Ω), hV B.1 (hTp B.1 B.2) (γ B).2⟩
  have key : ∀ φ ψ : CharOff V (ineOff F Ω (N * p)) l, L φ = L ψ →
      ((φ : V → ZMod l) - (ψ : V → ZMod l)) ∈ CharOff V (ineOff F Ω N) l := by
    intro φ ψ h
    let χ : V → ZMod l := (φ : V → ZMod l) - (ψ : V → ZMod l)
    have hm : IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧
        ∀ u : V, (u : G F Ω) ∈ ineOff F Ω (N * p) → χ u = 0 := (φ - ψ).2
    obtain ⟨hlc, hadd, hoff⟩ := hm
    change IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧
        ∀ u : V, (u : G F Ω) ∈ ineOff F Ω N → χ u = 0
    refine ⟨hlc, hadd, fun u hu => ?_⟩
    obtain ⟨A, hAN, huA⟩ := hu
    by_cases hAp : A.valuation (p : Ω) < 1
    · obtain ⟨B, hB, v, hv, rfl⟩ := hTcov A hAp
      have hg : v⁻¹ * (u : G F Ω) * v ∈ Ine B := (ineConj F Ω v).1 B u huA
      have hBV : Ine (F := F) B ≤ V := hV B (hTp B hB)
      let Bt : {B // B ∈ T} := ⟨B, hB⟩
      let ι : Ine (F := F) B → V := fun σ => ⟨(σ : G F Ω), hBV σ.2⟩
      have hι : ∀ a b : Ine (F := F) B, ι (a * b) = ι a * ι b := fun a b => rfl
      let χ' : Ine (F := F) B → ZMod l := fun σ => χ (ι σ)
      have hcont : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
      have hχlc : IsLocallyConstant χ' := hlc.comp_continuous hcont
      have hχadd : ∀ a b : Ine (F := F) B, χ' (a * b) = χ' a + χ' b := by
        intro a b
        show χ (ι (a * b)) = χ (ι a) + χ (ι b)
        rw [hι]
        exact hadd _ _
      have hχγ : χ' (γ Bt) = 0 := by
        have := congrFun h Bt
        exact sub_eq_zero.mpr this
      have h0 := hγ Bt χ' hχlc hχadd hχγ ⟨_, hg⟩
      let v' : V := ⟨v, hv⟩
      have e3 : χ (v'⁻¹ * u * v') = 0 := h0
      have e1 : χ (v'⁻¹ * u * v') = χ v'⁻¹ + χ u + χ v' := by
        rw [hadd, hadd]
      have h1 : χ 1 = 0 := by
        have := hadd 1 1
        rw [mul_one] at this
        linear_combination -this
      have e2 : χ v'⁻¹ + χ v' = 0 := by
        rw [← hadd, inv_mul_cancel, h1]
      linear_combination e3 - e1 - e2
    · apply hoff u
      refine ⟨A, ?_, huA⟩
      push_cast
      rw [map_mul]
      intro hlt
      exact (not_lt.mpr (one_le_mul (not_lt.mp hAN) (not_lt.mp hAp))) hlt
  haveI : Nonempty (CharOff V (ineOff F Ω (N * p)) l) := ⟨0⟩
  let s := Function.invFun L
  have hs : ∀ φ, L (s (L φ)) = L φ := fun φ => Function.invFun_eq ⟨φ, rfl⟩
  let f : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l) × CharOff V (ineOff F Ω N) l :=
    fun φ => (L φ, ⟨(φ : V → ZMod l) - (s (L φ) : V → ZMod l), key φ (s (L φ)) (hs φ).symm⟩)
  have hf : Function.Injective f := by
    intro φ ψ hfe
    have h1 : L φ = L ψ := congrArg Prod.fst hfe
    have h2 := congrArg (fun x => ((x.2 : CharOff V (ineOff F Ω N) l) : V → ZMod l)) hfe
    simp only [f] at h2
    rw [h1] at h2
    exact Subtype.ext (sub_left_inj.mp h2)
  haveI : Finite (CharOff V (ineOff F Ω N) l) := hN.1
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card (CharOff V (ineOff F Ω (N * p)) l)
      ≤ Nat.card (({B // B ∈ T} → ZMod l) × CharOff V (ineOff F Ω N) l) :=
        Nat.card_le_card_of_injective f hf
    _ = l ^ T.card * Nat.card (CharOff V (ineOff F Ω N) l) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod]
        simp
    _ ≤ l ^ k * n := Nat.mul_le_mul (Nat.pow_le_pow_right (Fact.out : l.Prime).pos hTc) hN.2
    _ = n * l ^ k := Nat.mul_comm _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneTwo
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p m : ℕ} (h : p.Coprime m)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (m : Ω) < 1 := by
  intro hm
  have hz : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one ⟨(z : Ω), intCast_mem A z⟩
  have h1 : ((p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]
    rfl
  have hcast : (p : Ω) * (Nat.gcdA p m : Ω) + (m : Ω) * (Nat.gcdB p m : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) h1
    push_cast at this
    exact this
  have ha : A.valuation ((p : Ω) * (Nat.gcdA p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hp
  have hb : A.valuation ((m : Ω) * (Nat.gcdB p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hm
  have := lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
  rw [hcast, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Two.ineTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p : ℕ) (A : ValuationSubring Ω), p.Coprime (2 * M.m) → A.valuation (p : Ω) < 1 → Ine (F := ℚ) A ≤ cycU 2 (abU Ω (withI M)) := by
  intro Ω _ _ _ M p A hcop hp
  have h2 : p.Coprime 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 M.m) hcop
  have hM : p.Coprime M.m := Nat.Coprime.coprime_dvd_right (dvd_mul_left M.m 2) hcop
  have hW : p.Coprime (withI M).m := by
    show p.Coprime (M.m * max 4 1)
    exact Nat.Coprime.mul_right hM (by simpa using Nat.Coprime.pow_right 2 h2)
  intro g hg
  refine ⟨?_, ?_⟩
  · have := ineChar Ω (withI M).m A (not_lt_one_of_coprime A hW hp) hg
    rw [MonoidHom.mem_ker] at this
    show galChar Ω (withI M).m g ∈ (withI M).H
    rw [this]
    exact Subgroup.one_mem _
  · exact (places ℚ Ω 2 A).2.2.2 (not_lt_one_of_coprime A h2 hp) hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbField
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abField :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (L : Type) [Field L] [NumberField L] [Algebra L Ω], IsAbField A L → galOf ℚ L Ω = abU Ω A := by
  intro Ω _ _ _ A L _ _ _ hL
  obtain ⟨N, hN, j, ζ, hm, hζ, hj⟩ := hL
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ (CyclotomicField N ℚ) := by
    haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
    have h := CyclotomicField.isCyclotomicExtension (n := N) (K := ℚ)
    have h2 := (@IsCyclotomicExtension.isGalois _ _ _ _ _ _ h).to_normal
    convert h2
    exact Subsingleton.elim _ _
  let k : CyclotomicField N ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (CyclotomicField N ℚ) Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have key : ∀ σ : G ℚ Ω, (∀ x : L, σ (k (j x)) = k (j x)) ↔ galChar Ω A.m σ ∈ A.H := by
    intro σ
    let τ := σ.restrictNormal (CyclotomicField N ℚ)
    have hτ : ∀ y, k (τ y) = σ (k y) := fun y => σ.restrictNormal_commutes (CyclotomicField N ℚ) y
    have hkζ : IsPrimitiveRoot (k ζ) N := hζ.map_of_injective k.injective
    have hσζ : σ (k ζ) = k ζ ^ (galChar Ω N σ : ZMod N).val :=
      galChar_spec N σ (k ζ) hkζ.pow_eq_one
    have hτζ : τ ζ = ζ ^ (galChar Ω N σ : ZMod N).val := by
      apply k.injective
      show k (τ ζ) = k (ζ ^ _)
      rw [hτ, hσζ, map_pow]
    have h1 := hj τ _ hτζ
    have hfix : (∀ x : L, τ (j x) = j x) ↔ (∀ x : L, σ (k (j x)) = k (j x)) :=
      forall_congr' fun x => by rw [← hτ]; exact k.injective.eq_iff.symm
    rw [← hfix, h1]
    obtain ⟨d, hd⟩ := hm
    have hprim : IsPrimitiveRoot (k ζ ^ d) A.m :=
      hkζ.pow (Nat.pos_of_ne_zero (NeZero.ne N)) (hd.trans (mul_comm _ _))
    have e1 := galChar_spec A.m σ (k ζ ^ d) hprim.pow_eq_one
    rw [map_pow, hσζ, ← pow_mul, mul_comm _ d, pow_mul] at e1
    have hfin : IsOfFinOrder (k ζ ^ d) := isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hprim.pow_eq_one⟩
    have hmod : (galChar Ω N σ : ZMod N).val ≡ (galChar Ω A.m σ : ZMod A.m).val [MOD A.m] := by
      have h2 := hfin.pow_eq_pow_iff_modEq.1 e1
      rwa [← hprim.eq_orderOf] at h2
    have hcast : (((galChar Ω N σ : ZMod N).val : ℕ) : ZMod A.m) = (galChar Ω A.m σ : ZMod A.m) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, ZMod.natCast_zmod_val]
    constructor
    · rintro ⟨u, hu, hua⟩
      have hu' : u = galChar Ω A.m σ := Units.ext (hua.trans hcast)
      exact hu' ▸ hu
    · intro h
      exact ⟨_, h, hcast.symm⟩
  let σ₀ : Ω →ₐ[ℚ] Ω := j.liftNormal Ω
  have hσ₀ : ∀ x : L, σ₀ (algebraMap L Ω x) = k (j x) := fun x => j.liftNormal_commutes Ω x
  let e : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  have he : ∀ x : L, e (algebraMap L Ω x) = k (j x) := hσ₀
  have hconj : ∀ σ : G ℚ Ω, galChar Ω A.m (e * σ * e⁻¹) = galChar Ω A.m σ := by
    intro σ
    rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω A.m e), mul_assoc, mul_inv_cancel, mul_one]
  ext σ
  change (∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) ↔ galChar Ω A.m σ ∈ A.H
  rw [← hconj σ, ← key]
  refine forall_congr' fun x => ?_
  rw [← he, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
    e.injective.eq_iff]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CompIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem exists_isPrimitiveRoot_of_isAlgClosure_rat (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n] :
    ∃ ω : Ω, IsPrimitiveRoot ω n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω n

private theorem coe_galChar_eq_natCast_of_apply_eq_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n]
    (σ : G ℚ Ω) (ω : Ω) (hω : IsPrimitiveRoot ω n) (c : ℕ) (hc : σ ω = ω ^ c) :
    ((galChar Ω n σ : (ZMod n)ˣ) : ZMod n) = (c : ZMod n) := by
  have hc' : σ ω = ω ^ (c % n) := by
    rw [hc]
    conv_lhs => rw [← Nat.mod_add_div c n, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have htn : (t : Ω) ^ n = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one htn
  rw [← hi, ZMod.val_natCast]
  change σ (ω ^ i) = _
  rw [map_pow, hc', ← pow_mul, ← pow_mul, mul_comm]

private theorem apply_eq_pow_val_galChar_of_isPrimitiveRoot (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n]
    (σ : G ℚ Ω) (ω : Ω) (hω : IsPrimitiveRoot ω n) :
    σ ω = ω ^ ((galChar Ω n σ : (ZMod n)ˣ) : ZMod n).val := by
  have := modularCyclotomicCharacter.spec Ω (n := n) (by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n) σ.toRingEquiv (t := (hω.toRootsOfUnity : Ωˣ)) (SetLike.coe_mem _)
  simp only [IsPrimitiveRoot.val_toRootsOfUnity_coe, Units.val_pow_eq_pow_val] at this
  exact this

private theorem coe_galChar_eq_val_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k m : ℕ) [NeZero k] [NeZero m]
    (hkm : k ∣ m) (σ : G ℚ Ω) :
    ((galChar Ω k σ : (ZMod k)ˣ) : ZMod k) = (((galChar Ω m σ : (ZMod m)ˣ) : ZMod m).val : ZMod k) := by
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_of_isAlgClosure_rat Ω m
  obtain ⟨r, hr⟩ := hkm
  have hω' : IsPrimitiveRoot (ω ^ r) k := hω.pow (Nat.pos_of_neZero m) (by rw [hr, mul_comm])
  apply coe_galChar_eq_natCast_of_apply_eq_pow Ω k σ _ hω'
  rw [map_pow, apply_eq_pow_val_galChar_of_isPrimitiveRoot Ω m σ ω hω, ← pow_mul, ← pow_mul, mul_comm]

private theorem unitsMap_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k m : ℕ) [NeZero k] [NeZero m]
    (hkm : k ∣ m) (σ : G ℚ Ω) :
    ZMod.unitsMap hkm (galChar Ω m σ) = galChar Ω k σ := by
  ext
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, coe_galChar_eq_val_galChar_of_dvd Ω k m hkm σ]

private theorem mem_comap_cycZ_princ_two_iff_galChar_eq_one (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (σ : G ℚ Ω) :
    σ ∈ Subgroup.comap (cycZ ℚ Ω 2) (KStar.TotallyRealRoots.princ 2 n) ↔ galChar Ω (2 ^ n) σ = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (2 ^ i) := fun i => inferInstance
  rw [Subgroup.mem_comap, KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow, Units.ext_iff, Units.ext_iff]
  change PadicInt.toZModPow n ((cyclotomicCharacter Ω 2 σ.toRingEquiv : ℤ_[2]ˣ) : ℤ_[2]) = 1 ↔ _
  rw [cyclotomicCharacter.toZModPow]
  rfl

private theorem mem_galOf_iff_val_galChar_of_fixes_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (E : Type) [Field E]
    [NumberField E] [Algebra E Ω] (N : ℕ) [NeZero N] (j : E →ₐ[ℚ] CyclotomicField N ℚ)
    (ζ : CyclotomicField N ℚ) (hζ : IsPrimitiveRoot ζ N) (Q : ℕ → Prop)
    (hQ : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (a : ℕ), τ ζ = ζ ^ a → ((∀ x, τ (j x) = j x) ↔ Q a))
    (σ : G ℚ Ω) : σ ∈ galOf ℚ E Ω ↔ Q ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hce0 := CyclotomicField.isCyclotomicExtension N ℚ
  have hce : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := by exact hce0
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := by
    exact IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  let ι : CyclotomicField N ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (CyclotomicField N ℚ) Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_ratCast, eq_ratCast, map_ratCast])
  let φ := (ι.comp j).liftNormal Ω
  let ρ : G ℚ Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  have hρ : ∀ x : E, ρ (algebraMap E Ω x) = ι (j x) := fun x => (ι.comp j).liftNormal_commutes Ω x
  let σ' : G ℚ Ω := ρ * σ * ρ⁻¹
  have hgal : galChar Ω N σ' = galChar Ω N σ := by
    simp only [σ', map_mul, map_inv]
    rw [mul_comm (galChar Ω N ρ), mul_assoc, mul_inv_cancel, mul_one]
  let τ : Gal(CyclotomicField N ℚ/ℚ) := σ'.restrictNormal (CyclotomicField N ℚ)
  have hτ : ∀ y, ι (τ y) = σ' (ι y) := fun y => AlgEquiv.restrictNormal_commutes σ' (CyclotomicField N ℚ) y
  have hτζ : τ ζ = ζ ^ ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
    apply ι.toRingHom.injective
    change ι (τ ζ) = ι (ζ ^ _)
    rw [hτ, map_pow, apply_eq_pow_val_galChar_of_isPrimitiveRoot Ω N σ' (ι ζ) (hζ.map_of_injective ι.toRingHom.injective), hgal]
  rw [← hQ τ _ hτζ, mem_galOf]
  apply forall_congr'
  intro x
  rw [← ι.toRingHom.injective.eq_iff]
  change _ ↔ ι (τ (j x)) = ι (j x)
  rw [hτ, ← hρ x]
  simp only [σ', AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  exact ρ.injective.eq_iff.symm

private theorem zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime (p m : ℕ) (hp : p.Prime) (hm : m = p) (a : ℕ) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = a) :
    u ∈ (powMonoidHom 2 : (ZMod m)ˣ →* (ZMod m)ˣ).range ↔ jacobiSym (a : ℤ) p = 1 := by
  subst hm
  haveI : Fact m.Prime := ⟨hp⟩
  have ha0 : (((a : ℤ)) : ZMod m) ≠ 0 := by
    rw [Int.cast_natCast, ← hu]
    exact u.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff m ha0, Int.cast_natCast, ← hu,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp [pow_two]⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simp [pow_two, hr]

private theorem mem_abU_sup_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A B : AbF) (σ : G ℚ Ω) :
    σ ∈ abU Ω (A.sup B) ↔ σ ∈ abU Ω A ∧ σ ∈ abU Ω B := by
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : NeZero B.m := ⟨B.pos.ne'⟩
  haveI : NeZero (A.sup B).m := ⟨(A.sup B).pos.ne'⟩
  have h1 : A.m ∣ (A.sup B).m := Dvd.intro B.m rfl
  have h2 : B.m ∣ (A.sup B).m := Dvd.intro_left A.m rfl
  have e1 := unitsMap_galChar_of_dvd Ω A.m (A.sup B).m h1 σ
  have e2 := unitsMap_galChar_of_dvd Ω B.m (A.sup B).m h2 σ
  change (ZMod.unitsMap h1 (galChar Ω (A.sup B).m σ) ∈ A.H ∧
    ZMod.unitsMap h2 (galChar Ω (A.sup B).m σ) ∈ B.H) ↔
    (galChar Ω A.m σ ∈ A.H ∧ galChar Ω B.m σ ∈ B.H)
  rw [e1, e2]

theorem UpperTheory.V.Two.compIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E] [Algebra E Ω], q.Prime → d.Prime → IsCompField M e q d E →
      levU 2 (abU Ω (base2 M q d)) (e + 2) ≤ galOf ℚ E Ω ∧ (levU 2 (abU Ω (base2 M q d)) (e + 2)).relIndex (galOf ℚ E Ω) ∣ 2 := by
  intro Ω _ _ _ M e q d E _ _ _ hq hd hE
  obtain ⟨N, hN, j, ζ, h2N, hMN, hqN, hdN, hζ, hτ⟩ := hE
  haveI := hN
  haveI : NeZero M.m := ⟨M.pos.ne'⟩
  haveI : NeZero (AbF.cyc 4).m := ⟨(AbF.cyc 4).pos.ne'⟩
  haveI : NeZero (AbF.quad q).m := ⟨(AbF.quad q).pos.ne'⟩
  haveI : NeZero (AbF.quad d).m := ⟨(AbF.quad d).pos.ne'⟩
  haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have hqm : (AbF.quad q).m = q := max_eq_left hq.one_lt.le
  have hdm : (AbF.quad d).m = d := max_eq_left hd.one_lt.le
  have h4m : (AbF.cyc 4).m = 4 := rfl
  have key := fun σ => mem_galOf_iff_val_galChar_of_fixes_iff Ω E N j ζ hζ _ hτ σ
  have hlev : ∀ σ : G ℚ Ω, σ ∈ levU 2 (abU Ω (base2 M q d)) (e + 2) ↔
      ((galChar Ω M.m σ ∈ M.H ∧ galChar Ω (AbF.cyc 4).m σ ∈ (AbF.cyc 4).H) ∧
        galChar Ω (AbF.quad q).m σ ∈ (AbF.quad q).H ∧ galChar Ω (AbF.quad d).m σ ∈ (AbF.quad d).H) ∧
        galChar Ω (2 ^ (e + 2)) σ = 1 := by
    intro σ
    rw [← mem_comap_cycZ_princ_two_iff_galChar_eq_one Ω (e + 2) σ]
    change σ ∈ abU Ω (base2 M q d) ∧ _ ↔ _
    simp only [base2, withI, mem_abU_sup_iff, and_assoc]
    rfl
  have hval : ∀ (k : ℕ) [NeZero k], k ∣ N → ∀ σ : G ℚ Ω,
      ((galChar Ω k σ : (ZMod k)ˣ) : ZMod k) = (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ZMod k) :=
    fun k _ hk σ => coe_galChar_eq_val_galChar_of_dvd Ω k N hk σ
  have hone : ∀ (k : ℕ) [NeZero k], k ∣ N → ∀ σ : G ℚ Ω,
      (galChar Ω k σ = 1 ↔ ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD k]) := by
    intro k _ hk σ
    rw [Units.ext_iff, hval k hk σ, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  have hker : ∀ σ : G ℚ Ω, galChar Ω M.m σ ∈ M.H ↔ M.ker ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
    intro σ
    constructor
    · intro h
      exact ⟨_, h, hval M.m hMN σ⟩
    · rintro ⟨u, hu, hua⟩
      have : u = galChar Ω M.m σ := Units.ext (by rw [hua, hval M.m hMN σ])
      rwa [← this]
  have hsq : ∀ σ : G ℚ Ω, (galChar Ω (AbF.quad q).m σ ∈ (AbF.quad q).H ↔
      jacobiSym (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ℤ) q = 1) ∧
      (galChar Ω (AbF.quad d).m σ ∈ (AbF.quad d).H ↔
      jacobiSym (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ℤ) d = 1) := by
    intro σ
    exact ⟨zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime q _ hq hqm _ _ (hval _ (by rw [hqm]; exact hqN) σ),
      zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime d _ hd hdm _ _ (hval _ (by rw [hdm]; exact hdN) σ)⟩
  have h4 : ∀ σ : G ℚ Ω, galChar Ω (2 ^ (e + 2)) σ = 1 → galChar Ω (AbF.cyc 4).m σ ∈ (AbF.cyc 4).H := by
    intro σ h
    have h4N : (AbF.cyc 4).m ∣ N := by
      rw [h4m]
      exact dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)) h2N
    rw [hone _ h2N] at h
    have h1 : galChar Ω (AbF.cyc 4).m σ = 1 := by
      rw [hone _ h4N, h4m]
      exact Nat.ModEq.of_dvd (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)) h
    rw [h1]
    exact Subgroup.one_mem _
  have hle : levU 2 (abU Ω (base2 M q d)) (e + 2) ≤ galOf ℚ E Ω := by
    intro σ hσ
    rw [hlev] at hσ
    obtain ⟨⟨⟨hM, -⟩, hQ, hD⟩, h2⟩ := hσ
    rw [key]
    exact ⟨Or.inl ((hone _ h2N σ).1 h2), (hker σ).1 hM, (hsq σ).1.1 hQ, (hsq σ).2.1 hD⟩
  refine ⟨hle, ?_⟩
  have hsub : (galChar Ω (2 ^ (e + 2))).ker.subgroupOf (galOf ℚ E Ω) ≤
      (levU 2 (abU Ω (base2 M q d)) (e + 2)).subgroupOf (galOf ℚ E Ω) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf, hlev]
    obtain ⟨-, hM, hQ, hD⟩ := (key x).1 x.2
    exact ⟨⟨⟨(hker _).2 hM, h4 _ hx⟩, (hsq _).1.2 hQ, (hsq _).2.2 hD⟩, hx⟩
  refine dvd_trans (Subgroup.index_dvd_of_le hsub) ?_
  rw [Subgroup.subgroupOf, MonoidHom.comap_ker, Subgroup.index_ker]
  have hrange : ((galChar Ω (2 ^ (e + 2))).comp (galOf ℚ E Ω).subtype).range ≤ Subgroup.zpowers (-1) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨h12, -⟩ := (key x).1 x.2
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rcases h12 with h1 | h1
    · rw [(hone _ h2N x).2 h1]
      exact Subgroup.one_mem _
    · have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
      have hm1 : galChar Ω (2 ^ (e + 2)) x = -1 := by
        ext
        rw [Units.val_neg, Units.val_one, hval _ h2N x, eq_neg_iff_add_eq_zero]
        push_cast at hc
        exact hc
      rw [hm1]
      exact Subgroup.mem_zpowers _
  refine dvd_trans (Subgroup.card_dvd_of_le hrange) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by simp)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.RkTransport
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.rkTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ),
      XRk l N (cycU l (⊤ : Subgroup (G K Ω))) r ↔ XRk l N (cycU l (galOf F K Ω)) r := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ N r
  have hDI : ∀ A : ValuationSubring Ω,
      (Dec (F := F) A).comap (galEmb F K Ω) = Dec (F := K) A ∧
      (Ine (F := F) A).comap (galEmb F K Ω) = Ine (F := K) A := by
    intro A
    have hD : (Dec (F := F) A).comap (galEmb F K Ω) = Dec (F := K) A := by
      ext σ
      rw [Subgroup.mem_comap, mem_Dec, mem_Dec]
      rfl
    refine ⟨hD, ?_⟩
    ext σ
    rw [Subgroup.mem_comap]
    exact and_congr (SetLike.ext_iff.1 hD σ) Iff.rfl
  obtain ⟨hE, -, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (σ : G K Ω), galEmb F K Ω σ ∈ Dec (F := F) A ↔ σ ∈ Dec (F := K) A :=
    fun A σ => by rw [← (hDI A).1]; rfl
  have hI : ∀ (A : ValuationSubring Ω) (σ : G K Ω), galEmb F K Ω σ ∈ Ine (F := F) A ↔ σ ∈ Ine (F := K) A :=
    fun A σ => by rw [← (hDI A).2]; rfl
  have hle : cycU l (galOf F K Ω) ≤ galOf F K Ω := inf_le_left
  let e : cycU l (⊤ : Subgroup (G K Ω)) → cycU l (galOf F K Ω) :=
    fun u => ⟨galEmb F K Ω u.1, galEmb_mem F K Ω u.1, u.2.2⟩
  let e' : cycU l (galOf F K Ω) → cycU l (⊤ : Subgroup (G K Ω)) :=
    fun u => ⟨toGal K hle u, trivial, u.2.2⟩
  have hee : ∀ u, e (e' u) = u := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  have hee' : ∀ u, e' (e u) = u := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  have he : Continuous e := (hE.continuous.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e' := by
    refine Continuous.subtype_mk ?_ _
    exact hE.continuous_iff.2 continuous_subtype_val
  have hm : ∀ a b, e (a * b) = e a * e b := fun a b => Subtype.ext (map_mul (galEmb F K Ω) a.1 b.1)
  have hm' : ∀ a b, e' (a * b) = e' a * e' b := fun a b => Subtype.ext (map_mul (toGal K hle) a b)
  constructor
  · intro h
    refine CardLe.of_injective h (fun φ => ⟨φ.1 ∘ e, φ.2.1.comp_continuous he,
      fun a b => by simp only [Function.comp, hm]; exact φ.2.2.1 _ _,
      fun A u hu => φ.2.2.2.1 A (e u) ((hI A u.1).2 hu),
      fun A hA u hu => φ.2.2.2.2 A hA (e u) ((hD A u.1).2 hu)⟩) fun φ ψ hh => Subtype.ext (funext fun u => ?_)
    have := congrFun (congrArg Subtype.val hh) (e' u)
    simpa only [Function.comp, hee] using this
  · intro h
    refine CardLe.of_injective h (fun φ => ⟨φ.1 ∘ e', φ.2.1.comp_continuous he',
      fun a b => by simp only [Function.comp, hm']; exact φ.2.2.1 _ _,
      fun A u hu => φ.2.2.2.1 A (e' u) ((hI A (e' u).1).1 hu),
      fun A hA u hu => φ.2.2.2.2 A hA (e' u) ((hD A (e' u).1).1 hu)⟩) fun φ ψ hh => Subtype.ext (funext fun u => ?_)
    have := congrFun (congrArg Subtype.val hh) (e u)
    simpa only [Function.comp, hee'] using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LayerFn
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.layerFn :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), (∃ ζ : F, IsPrimitiveRoot ζ l) → ∃ m, m ≤ n ∧ IsLayer l m F (Fn F Ω l n) := by
  intro F Ω _ _ _ _ _ l _ n hz
  obtain ⟨ζ0, hζ0⟩ := hz
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hl : l ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hl⟩
  haveI : NeZero (l ^ n) := ⟨hl⟩
  have key : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ k ∈ ({l ^ n} : Set ℕ), k ≠ 0 ∧ b ^ k = 1} := by
    unfold Fn
    congr 1
    ext x
    simp only [Polynomial.mem_rootSet, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_eq_left]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero, ne_eq, hl, not_false_eq_true, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun h0 => ?_, h⟩
      have := congrArg Polynomial.natDegree h0
      simp at this
      exact hp.ne_zero this.1
  haveI hcyc : IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) := by
    rw [key]
    apply IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
    rintro k rfl -
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  haveI : FiniteDimensional F (Fn F Ω l n) := IsCyclotomicExtension.finiteDimensional {l ^ n} F _
  haveI : IsGalois F (Fn F Ω l n) := IsCyclotomicExtension.isGalois {l ^ n} F _
  obtain ⟨μ, hμ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot F (Fn F Ω l n) (Set.mem_singleton (l ^ n)) hl
  set f := hμ.autToPow F with hf
  have hinj : Function.Injective f := hμ.autToPow_injective F
  have hcardG : Nat.card Gal((Fn F Ω l n)/F) = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h0 := hζ0.map_of_injective (algebraMap F (Fn F Ω l n)).injective
  have hdvd : Nat.card Gal((Fn F Ω l n)/F) ∣ l ^ n := by
    rcases n with _ | k
    · rw [hcardG]
      have : Nat.card f.range ∣ Nat.card (ZMod (l ^ 0))ˣ := Subgroup.card_subgroup_dvd_card _
      have h1 : Nat.card (ZMod (l ^ 0))ˣ = 1 := by
        rw [pow_zero]
        exact Nat.card_unique
      exact (this.trans h1.dvd).trans (one_dvd _)
    · have hd : l ∣ l ^ (k + 1) := dvd_pow_self l (Nat.succ_ne_zero k)
      set g := ZMod.unitsMap hd with hg
      have hle : f.range ≤ g.ker := by
        rintro _ ⟨σ, rfl⟩
        rw [MonoidHom.mem_ker]
        have hω := hμ.pow_of_dvd (pow_ne_zero k hp.ne_zero) (pow_dvd_pow l (Nat.le_succ k))
        have hlk : l ^ (k + 1) / l ^ k = l := by
          rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
        rw [hlk] at hω
        haveI : NeZero l := ⟨hp.ne_zero⟩
        obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one hω.pow_eq_one
        have hfix : σ (μ ^ l ^ k) = μ ^ l ^ k := by
          rw [← hi, map_pow, AlgEquiv.commutes]
        rw [map_pow, ← IsPrimitiveRoot.autToPow_spec F hμ σ, ← pow_mul, mul_comm, pow_mul] at hfix
        rw [← hf] at hfix
        generalize f σ = u at hfix ⊢
        obtain ⟨ω, hωd⟩ : ∃ ω, ω = μ ^ l ^ k := ⟨_, rfl⟩
        rw [← hωd] at hfix hω
        have hmod : (u : ZMod (l ^ (k + 1))).val ≡ 1 [MOD l] := by
          generalize (u : ZMod (l ^ (k + 1))).val = v at hfix ⊢
          rcases Nat.eq_zero_or_pos v with rfl | hv
          · exfalso
            rw [pow_zero] at hfix
            exact hω.ne_one hp.one_lt hfix.symm
          · have hω0 : ω ≠ 0 := hω.ne_zero hp.ne_zero
            have h3 : ω ^ (v - 1) = 1 := by
              have h4 := hfix
              rw [← Nat.sub_add_cancel hv, pow_succ] at h4
              exact mul_right_cancel₀ hω0 (h4.trans (one_mul ω).symm)
            exact ((Nat.modEq_iff_dvd' hv).mpr ((hω.pow_eq_one_iff_dvd _).mp h3)).symm
        have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
        ext
        rw [hg, ZMod.unitsMap_def]
        simp only [Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, Units.val_one]
        rw [← ZMod.natCast_val]
        simpa using hc
      have hsurj : Function.Surjective g := ZMod.unitsMap_surjective hd
      have hidx : g.ker.index = l - 1 := by
        rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
          Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
      have hker : Nat.card g.ker = l ^ k := by
        have h1 := Subgroup.card_mul_index g.ker
        rw [hidx, Nat.card_eq_fintype_card (α := (ZMod (l ^ (k + 1)))ˣ), ZMod.card_units_eq_totient,
          Nat.totient_prime_pow hp (Nat.succ_pos k)] at h1
        try simp only [Nat.add_sub_cancel] at h1
        exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) h1
      rw [hcardG]
      calc Nat.card f.range ∣ Nat.card g.ker := Subgroup.card_dvd_of_le hle
        _ = l ^ k := hker
        _ ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨m, hm, ⟨n, hcyc⟩, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank, hmeq]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.HasMuQ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem root_of_hasMu (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L] (hA : A.HasMu l)
    (hL : IsAbField A L) : ∃ ζ : L, IsPrimitiveRoot ζ l := by
  obtain ⟨N, hN, j, ζ, h1, h2, h3⟩ := hL
  obtain ⟨hl, hker⟩ := hA
  obtain ⟨k, hk⟩ := hl.trans h1
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    @IsCyclotomicExtension.isGalois {N} ℚ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ)
  have hη : IsPrimitiveRoot (ζ ^ k) l := h2.pow (NeZero.pos N) (by rw [hk, mul_comm])
  have key : ∀ b : ℕ, (ζ ^ k) ^ b = (ζ ^ k) ^ (b % l) := fun b => by
    conv_lhs => rw [← Nat.mod_add_div b l]
    rw [pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]
  have hmem : ζ ^ k ∈ j.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hfix : ∀ x : L, τ (j x) = j x := fun x => hτ _ ⟨x, rfl⟩
    have hτN : (τ ζ) ^ N = 1 := by rw [← map_pow, h2.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := h2.eq_pow_of_pow_eq_one hτN
    have hmod : a ≡ 1 [MOD l] := hker a ((h3 τ a ha.symm).1 hfix)
    have hpow : (ζ ^ k) ^ a = (ζ ^ k) ^ 1 := by
      rw [key a, key 1, show a % l = 1 % l from hmod]
    rw [map_pow, ← ha, ← pow_mul, mul_comm, pow_mul, hpow, pow_one]
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, IsPrimitiveRoot.of_map_of_injective (f := (j : L →+* CyclotomicField N ℚ)) ?_ j.toRingHom.injective⟩
  rw [show (j : L →+* CyclotomicField N ℚ) x = ζ ^ k from hx]
  exact hη

private theorem unitsMap_nat {m n a : ℕ} (h : m ∣ n) (u : (ZMod n)ˣ) (e : (u : ZMod n) = (a : ZMod n)) :
    ((ZMod.unitsMap h u : (ZMod m)ˣ) : ZMod m) = (a : ZMod m) := by
  rw [ZMod.unitsMap_def]
  simp [Units.coe_map, ZMod.castHom_apply, e, ZMod.cast_natCast h]

private theorem ker_sup {A B : AbF} {a : ℕ} (h : (A.sup B).ker a) : A.ker a ∧ B.ker a := by
  obtain ⟨u, ⟨hu1, hu2⟩, e⟩ := h
  exact ⟨⟨_, hu1, unitsMap_nat _ _ e⟩, ⟨_, hu2, unitsMap_nat _ _ e⟩⟩

private theorem hasMu_sup_left {A : AbF} (B : AbF) {l : ℕ} (h : A.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_left h.1 _, fun a ha => h.2 a (ker_sup ha).1⟩

private theorem hasMu_sup_right (A : AbF) {B : AbF} {l : ℕ} (h : B.HasMu l) : (A.sup B).HasMu l := by
  exact ⟨dvd_mul_of_dvd_right h.1 _, fun a ha => h.2 a (ker_sup ha).2⟩

private theorem hasMu_withI (M : AbF) : (withI M).HasMu 4 :=
  hasMu_sup_right M (AbF.hasMu_cyc (l := 4) (q := 1) (by norm_num) (by norm_num))

theorem UpperTheory.V.Two.hasMuQ :
    (∀ (l : ℕ) (A : AbF) (L : Type) [Field L] [NumberField L], A.HasMu l → IsAbField A L → ∃ ζ : L, IsPrimitiveRoot ζ l) ∧
      (∀ (M : AbF) (L : Type) [Field L] [NumberField L], IsAbField (withI M) L → ∃ ζ : L, IsPrimitiveRoot ζ 4) ∧
      ∀ (M : AbF) (q d : ℕ) (L : Type) [Field L] [NumberField L], IsAbField (base2 M q d) L → ∃ ζ : L, IsPrimitiveRoot ζ 4 := by
  refine ⟨fun l A L _ _ hA hL => root_of_hasMu l A L hA hL,
    fun M L _ _ hL => root_of_hasMu 4 _ L (hasMu_withI M) hL,
    fun M q d L _ _ hL => root_of_hasMu 4 _ L ?_ hL⟩
  exact hasMu_sup_left _ (hasMu_sup_left _ (hasMu_withI M))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbExists
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abExists :
    ∀ A : AbF, ∃ (L : Type) (_ : Field L) (_ : NumberField L), IsAbField A L := by
  intro A
  obtain ⟨L, hF, hN, h, -⟩ := UpperTheory.V.exists_numberField_isAbField_finrank_eq_deg A
  exact ⟨L, hF, hN, h⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbProps
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abProps :
    ∀ (A : AbF) (L : Type) [Field L] [NumberField L], IsAbField A L → IsAbelianGalois ℚ L ∧ Module.finrank ℚ L = A.deg ∧ Nonempty (L →ₐ[ℚ] CyclotomicField A.m ℚ) := by
  intro A L _ _ hA
  obtain ⟨N, hN, j, ζ, hmN, hζ, h⟩ := hA
  haveI := hN
  haveI hcN : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI hab : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfix : ∀ τ : Gal(CyclotomicField N ℚ/ℚ),
      τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ y : L, τ (j y) = j y := by
    intro τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro H y
      exact H _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)
    · intro H x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hx
      exact H y
  have hpow : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N).val) :=
    fun τ => (IsPrimitiveRoot.autToPow_spec ℚ hζ τ).symm
  have hker : ∀ v : (ZMod N)ˣ, A.ker ((v : ZMod N).val) ↔ ZMod.unitsMap hmN v ∈ A.H := by
    intro v
    have hc : ((ZMod.unitsMap hmN v : (ZMod A.m)ˣ) : ZMod A.m) = (((v : ZMod N).val : ℕ) : ZMod A.m) := by
      rw [ZMod.natCast_val]
      rfl
    constructor
    · rintro ⟨u, hu, hua⟩
      have : u = ZMod.unitsMap hmN v := Units.ext (hua.trans hc.symm)
      rwa [← this]
    · intro hv
      exact ⟨_, hv, hc⟩
  have hinj : Function.Injective (hζ.autToPow ℚ) := hζ.autToPow_injective ℚ
  have hcard : Nat.card Gal(CyclotomicField N ℚ/ℚ) = Nat.card (ZMod N)ˣ :=
    Nat.card_congr (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_neZero N))).toEquiv
  have hsurj : Function.Surjective (hζ.autToPow ℚ) :=
    ((Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2
  refine ⟨IsAbelianGalois.of_algHom j, ?_, ?_⟩
  · rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    change Module.finrank ℚ j.fieldRange = _
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    have hS : j.fieldRange.fixingSubgroup = (A.H.comap (ZMod.unitsMap hmN)).comap (hζ.autToPow ℚ) := by
      ext τ
      rw [hfix, h τ _ (hpow τ)]
      exact hker _
    rw [hS, Subgroup.index_comap_of_surjective _ hsurj,
      Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hmN)]
    rfl
  · have hdvd : N / A.m ∣ N := Nat.div_dvd_of_dvd hmN
    have hp0 : N / A.m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hmN) A.pos).ne'
    have hζm : IsPrimitiveRoot (ζ ^ (N / A.m)) A.m := by
      have := hζ.pow_of_dvd hp0 hdvd
      rwa [Nat.div_div_self hmN (NeZero.ne N)] at this
    haveI : NeZero A.m := ⟨A.pos.ne'⟩
    haveI hcm : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) :=
      CyclotomicField.isCyclotomicExtension A.m ℚ
    haveI : IsCyclotomicExtension {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}) :=
      hζm.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hMC : j.fieldRange ≤ IntermediateField.adjoin ℚ {ζ ^ (N / A.m)} := by
      rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}),
        IntermediateField.le_iff_le]
      intro τ hτ
      rw [hfix, h τ _ (hpow τ)]
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have h1 : τ (ζ ^ (N / A.m)) = ζ ^ (N / A.m) :=
        hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)
      rw [map_pow, hpow τ, ← pow_mul, mul_comm, pow_mul] at h1
      generalize ((hζ.autToPow ℚ τ : ZMod N)).val = a at h1 ⊢
      have hfo : IsOfFinOrder (ζ ^ (N / A.m)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζm.pow_eq_one⟩
      have h2 : a ≡ 1 [MOD A.m] := by
        rw [hζm.eq_orderOf]
        exact hfo.pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact h1)
      refine ⟨1, one_mem _, ?_⟩
      rw [Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact h2.symm
    exact ⟨(IsCyclotomicExtension.algEquiv {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)})
      (CyclotomicField A.m ℚ)).toAlgHom.comp
        ((IntermediateField.inclusion hMC).comp (AlgEquiv.ofInjectiveField j).toAlgHom)⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

noncomputable section

namespace UpperTheory.V.Two

theorem complex_of_root {L : Type} [Field L] [NumberField L] {n : ℕ} (hn : 2 < n) (h : ∃ ζ : L, IsPrimitiveRoot ζ n) :
    IsTotallyComplex L := by
  obtain ⟨ζ, hζ⟩ := h
  exact nrRealPlaces_eq_zero_iff.1 (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hn hζ)

theorem fwRk (hFW : Published.FerreroWashington) (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K]
    [IsAbelianGalois ℚ K] (hμ : HasMuQ l K) :
    ∃ r, ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], XRk l 1 (cycU l (⊤ : Subgroup (G K Ω))) r := by
  obtain ⟨r, hr⟩ := hFW l K hμ
  refine ⟨r, fun Ω _ _ _ => infRk K Ω l 1 r ⊤ one_ne_zero isClosed_univ fun n hn => ?_⟩
  haveI := (fnCyc K Ω l n).1
  exact levelRk K Ω l n r hn (hr n _)

theorem isAlgClosure_rat (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra ℚ Ω] :
    IsAlgClosure ℚ Ω :=
  ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans ℚ L Ω⟩

theorem abRk (hFW : Published.FerreroWashington) (l : ℕ) [Fact l.Prime] (A : AbF)
    (hμ : ∀ (L : Type) [Field L] [NumberField L], IsAbField A L → HasMuQ l L) :
    ∃ r, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω], XRk l 1 (cycU l (abU Ω A)) r := by
  obtain ⟨K, _, _, hK⟩ := abExists A
  haveI := (abProps A K hK).1
  obtain ⟨r, hr⟩ := fwRk hFW l K (hμ K hK)
  refine ⟨r, fun Ω _ _ _ => ?_⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  rw [← abField Ω A K hK]
  exact (rkTransport ℚ Ω K l 1 r).1 (hr Ω)

theorem genLE_of_abRk {l : ℕ} [Fact l.Prime] {A : AbF} {r : ℕ} (N : ℕ) (L : Type) [Field L] [NumberField L]
    [IsAlgClosure ℚ (AlgebraicClosure L)] (hL : IsAbField A L)
    (h : XRk l 1 (cycU l (abU (AlgebraicClosure L) A)) r) : Tower.GenLE ℤ_[l] (Tower.XN l L (AlgebraicClosure L) N) r := by
  rw [← abField _ A L hL] at h
  exact genOfRk L _ l N r ⊤ isClosed_univ (((rkTransport ℚ _ L l 1 r).2 h).of_one N)

theorem baseRk (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (q d g : ℕ) (hp : PrimePair M.m q d)
    (h : XRk 2 1 (cycU 2 (abU Ω (withI M))) g) : XRk 2 1 (cycU 2 (abU Ω (base2 M q d))) (4 * (g + 6 * M.deg)) := by
  obtain ⟨hq, hq8, hd, hd16, hc⟩ := hp
  have q2 : q.Coprime 2 := (Nat.coprime_two_right).2 (Nat.odd_iff.2 (by omega))
  have d2 : d.Coprime 2 := (Nat.coprime_two_right).2 (Nat.odd_iff.2 (by omega))
  have h0 : CardLe (CharOff (cycU 2 (abU Ω (withI M))) (ineOff ℚ Ω 1) 2) (2 ^ g) :=
    CardLe.of_injective h _ (Submodule.inclusion_injective (xDual_one _ 2).ge)
  have h1 := charStep ℚ Ω 2 _ 1 q _ _ q2 (orbTwo Ω M q 2 hq (Or.inl ⟨hq8, rfl⟩))
    (fun A hA => ineTwo Ω M q A (q2.mul_right (Nat.Coprime.coprime_mul_right hc)) hA) h0
  have h2 := charStep ℚ Ω 2 _ (1 * q) d _ _ d2 (orbTwo Ω M d 4 hd (Or.inr ⟨hd16, rfl⟩))
    (fun A hA => ineTwo Ω M d A (d2.mul_right (Nat.Coprime.coprime_mul_left hc)) hA) h1
  have h3 := quadStep Ω _ q _ _ hq (by simp) h2
  have h4 := quadStep Ω _ d _ _ hd (by simp) h3
  refine (h4.of_injective _ (Submodule.inclusion_injective (xDual_le_charOff 1 _ _ 2))).mono (le_of_eq ?_)
  rw [← pow_add, ← pow_add, ← pow_mul, ← pow_mul]
  congr 1
  ring

theorem towerTwo (hFW : Published.FerreroWashington) (M : AbF) : ∃ R : ℕ, ∀ q d : ℕ, PrimePair M.m q d →
    ∀ (L : Type) [Field L] [NumberField L], IsAbField (base2 M q d) L →
      Tower.GenLE ℤ_[2] (Tower.XX 2 L) R ∧ Tower.IsTower 2 L R := by
  obtain ⟨g, hg⟩ := abRk hFW 2 (withI M) fun L _ _ hL => hasMuQ.2.1 M L hL
  refine ⟨4 * (g + 6 * M.deg), fun q d hp L _ _ hL => ?_⟩
  haveI := isAlgClosure_rat L (AlgebraicClosure L)
  have h := baseRk (AlgebraicClosure L) M q d g hp (hg _)
  have hμ := hasMuQ.2.2 M q d L hL
  have ho := ((abBasic (AlgebraicClosure L)).2.1 M).2.1
  exact ⟨genLE_of_abRk 1 L hL h, complex_of_root (by norm_num) hμ, hμ, by omega, genLE_of_abRk 2 L hL h⟩

theorem towerFixed (hFW : Published.FerreroWashington) (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (A : AbF) (hA : A.HasMu l) :
    ∃ R : ℕ, ∀ (L : Type) [Field L] [NumberField L], IsAbField A L →
      Tower.GenLE ℤ_[l] (Tower.XX l L) R ∧ Tower.IsTower l L R := by
  have hμ : ∀ (L : Type) [Field L] [NumberField L], IsAbField A L → HasMuQ l L := fun L _ _ hL => by
    unfold HasMuQ
    rw [if_neg h2]
    exact hasMuQ.1 l A L hA hL
  obtain ⟨r, hr⟩ := abRk hFW l A hμ
  refine ⟨max 1 r, fun L _ _ hL => ?_⟩
  haveI := isAlgClosure_rat L (AlgebraicClosure L)
  have h := (hr (AlgebraicClosure L)).mono hl.out.pos (le_max_right 1 r)
  exact ⟨genLE_of_abRk 1 L hL h, complex_of_root (lt_of_le_of_ne hl.out.two_le h2.symm) (hasMuQ.1 l A L hA hL),
    hμ L hL, le_max_left _ _, genLE_of_abRk l L hL h⟩

theorem twoBase (M : AbF) (q d : ℕ) (hp : PrimePair M.m q d) (L : Type) [Field L] [NumberField L]
    (hL : IsAbField (base2 M q d) L) : Win.TwoBase M q d L := by
  obtain ⟨hq, -, hd, -, -⟩ := hp
  obtain ⟨-, h1, h2⟩ := abProps _ L hL
  have hμ := hasMuQ.2.2 M q d L hL
  refine ⟨hμ, h1 ▸ degBasic.2.2.2 M q d hq hd, ?_, fun e _ E _ _ hE => ?_⟩
  · rwa [modulus_adjoinISqrtNegPrimes M hq.pos hd.pos, mul_comm M.m 4] at h2
  · haveI := isAlgClosure_rat L (AlgebraicClosure L)
    letI : Algebra E (AlgebraicClosure L) := (IsAlgClosed.lift : E →ₐ[ℚ] AlgebraicClosure L).toRingHom.toAlgebra
    obtain ⟨ζ, hζ⟩ := hμ
    obtain ⟨m, hm, hlay⟩ := layerFn L (AlgebraicClosure L) 2 (e + 2) ⟨ζ ^ 2, hζ.pow (by norm_num) (by norm_num)⟩
    haveI := (fnCyc L (AlgebraicClosure L) 2 (e + 2)).1
    have e1 := galOfCyc ℚ (AlgebraicClosure L) 2 (e + 2) L (Fn L (AlgebraicClosure L) 2 (e + 2))
    rw [abField _ _ L hL] at e1
    obtain ⟨a, b⟩ := compIndex (AlgebraicClosure L) M e q d E hq hd hE
    exact ⟨m, Fn L (AlgebraicClosure L) 2 (e + 2), inferInstance, inferInstance, inferInstance, hlay, hm,
      fun k _ => shaTwo (AlgebraicClosure L) E _ k (e1 ▸ a) (e1 ▸ b)⟩

def TowerBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] (R : ℕ), Tower.IsTower l L R → Win.ABound l R L

theorem twoIn (hFW : Published.FerreroWashington) (hA : TowerBound) : Win.TwoIn := fun M => by
  obtain ⟨R, hR⟩ := towerTwo hFW M
  refine ⟨R, fun q d hp => ?_⟩
  obtain ⟨L, _, _, hL⟩ := abExists (base2 M q d)
  exact ⟨L, inferInstance, inferInstance, twoBase M q d hp L hL, hA 2 L R (hR q d hp L hL).2⟩

theorem fixedIn (hFW : Published.FerreroWashington) (hA : TowerBound) : Win.FixedIn := fun l _ h2 A hμ L _ _ hL => by
  obtain ⟨R, hR⟩ := towerFixed hFW l h2 A hμ
  exact ⟨R, hA l L R (hR L hL).2⟩

end UpperTheory.V.Two

end
