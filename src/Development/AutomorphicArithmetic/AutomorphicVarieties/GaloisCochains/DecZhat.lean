module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLocallyConstantDOneEqCocycleOfTameInertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FinChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DzExistsPrimeAlt
theorem UpperTheory.Reformulated.B.Qk5.dz_exists_prime :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers F) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers F) ∈ v.asIdeal := by
  intro F _ _ v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with ha | hb
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨p, hp, hd.mul_left a, hm⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

section SlopeTestRemainingChoices

open Formalism.GaloisCohomology UpperTheory.V.Base

private theorem dz_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem dz_exists_prime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : n ≠ 0) (h : (n : 𝓞 F) ∈ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 F) ∈ v.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk5.dz_exists_prime v n hn h

private theorem dz_not_both {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 F) ∈ v.asIdeal)
    (hb : (b : 𝓞 F) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, h⟩ : IsCoprime (a : 𝓞 F) (b : 𝓞 F) := hab.cast
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ha) (v.asIdeal.mul_mem_left _ hb)))

private theorem dz_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have h := hv ((n : ℕ) : 𝓞 F)
  have e : algebraMap F Ω (((n : ℕ) : 𝓞 F) : F) = (n : Ω) := by simp
  rw [e] at h
  exact h

private theorem dz_order {q n m : ℕ} (hq : 1 < q) (hn : 0 < n) (hm : m + 1 = q ^ n) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = q) : orderOf u = n := by
  rw [orderOf_eq_iff hn]
  refine ⟨Units.ext ?_, fun k hk hk0 h => ?_⟩
  · rw [Units.val_pow_eq_pow_val, hu, ← Nat.cast_pow, ← hm]
    simp
  · have h1 : ((q ^ k : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
      rw [Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h]
      simp
    have h2 : 1 < q ^ k := Nat.one_lt_pow hk0.ne' hq
    have h3 : q ^ k < q ^ n := Nat.pow_lt_pow_right hq hk
    have h4 := (Nat.modEq_iff_dvd' h2.le).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).symm
    have h5 := Nat.le_of_dvd (by omega) h4
    omega

private theorem dz_frob (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F))
    (hv : IsPlaceOver A v) (D I : Subgroup (G F Ω)) (hD : D = Dec (F := F) A) (hI : I = Ine (F := F) A) :
    ∃ φ : D, IsFrob (F := F) A (normV v) φ.1 ∧ (I.subgroupOf D ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
      ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I.subgroupOf D, d s = 1) ∧
        d φ = Multiplicative.ofAdd 1 := by
  subst hD hI
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  obtain ⟨γ, hγ⟩ := exists_isFrob hv
  refine ⟨⟨γ, hγ.1⟩, hγ, ?_, fun n hn => ?_⟩
  · have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G F Ω)
      ⟨(Ine (F := F) A ⊔ Subgroup.zpowers γ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have h1 : Dec (F := F) A ≤ (Ine (F := F) A ⊔ Subgroup.zpowers γ).topologicalClosure := by
      refine le_trans (le_sInf ?_) key.ge
      rintro N ⟨hNo, hN⟩
      have h := (Subgroup.le_topologicalClosure _).trans hN
      exact Kum.decGen F Ω A _ γ N hv hγ hNo (le_sup_left.trans h)
        (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers γ)))
    have h2 : ((Ine (F := F) A).subgroupOf (Dec (F := F) A) ⊔
        Subgroup.zpowers (⟨γ, hγ.1⟩ : Dec (F := F) A)).map (Dec (F := F) A).subtype =
        Ine (F := F) A ⊔ Subgroup.zpowers γ := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers, inf_eq_left.2 (Ine_le_Dec A)]
      rfl
    rw [eq_top_iff]
    intro x _
    have h3 := h1 x.2
    rw [← h2] at h3
    exact closure_subtype.2 h3
  · have hq : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have hq1 : 1 < normV v := by
      rw [hq]
      have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
      have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      omega
    have hqv : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := hq ▸ Ideal.absNorm_mem _
    obtain ⟨p, hp, hpq, hpv⟩ := dz_exists_prime v _ (by omega) hqv
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : 1 < normV v ^ n := Nat.one_lt_pow hn.ne' hq1
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = normV v ^ n := ⟨normV v ^ n - 1, by omega⟩
    haveI : NeZero m := ⟨by omega⟩
    have hmp : m.Coprime p := by
      refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_).symm
      have h2 : p ∣ m + 1 := hm ▸ hpq.trans (dvd_pow_self _ hn.ne')
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
    have hA := (dz_val hv p).2 hpv
    obtain ⟨hopen, -, -, -, hIne⟩ := Chr.clsFacts F Ω m
    have hI := hIne A fun h => dz_not_both v hmp ((dz_val hv m).1 h) hpv
    have hu : ((Chr.cls F Ω m γ : (ZMod m)ˣ) : ZMod m) = normV v := by
      haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
      have hv1 : A.valuation ζ ≤ 1 := by
        have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact ((pow_eq_one_iff_left (NeZero.ne m)).1 h1).le
      have h2 : γ ζ = ζ ^ normV v := by
        refine (LDataCardLeFinrank.ineFixRoots F Ω p A hA m hmp (ζ ^ normV v) ?_).1 (γ ζ) ?_ (hγ.2 ζ hv1)
        · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        · rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [Chr.cls_spec m γ ζ hζ.pow_eq_one, pow_eq_pow_mod (normV v) hζ.pow_eq_one] at h2
      have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h2
      rw [← ZMod.natCast_zmod_val ((Chr.cls F Ω m γ : (ZMod m)ˣ) : ZMod m), h3, ZMod.natCast_mod]
    have hord := dz_order hq1 hn hm _ hu
    have hle : Dec (F := F) A ≤ (Subgroup.zpowers (Chr.cls F Ω m γ)).comap (Chr.cls F Ω m) := by
      have hk : (Chr.cls F Ω m).ker ≤ (Subgroup.zpowers (Chr.cls F Ω m γ)).comap (Chr.cls F Ω m) :=
        Subgroup.ker_le_comap _ _
      exact Kum.decGen F Ω A _ γ _ hv hγ (Subgroup.isOpen_mono hk hopen) (hI.trans hk) (Subgroup.mem_zpowers _)
    let f : Dec (F := F) A →* Subgroup.zpowers (Chr.cls F Ω m γ) :=
      ((Chr.cls F Ω m).comp (Dec (F := F) A).subtype).codRestrict _ fun x => hle x.2
    have hg : ∀ x : Subgroup.zpowers (Chr.cls F Ω m γ), x ∈ Subgroup.zpowers (f ⟨γ, hγ.1⟩) := by
      rintro ⟨_, k, rfl⟩
      exact ⟨k, rfl⟩
    have hc : Nat.card (Subgroup.zpowers (Chr.cls F Ω m γ)) = n := by rw [Nat.card_zpowers, hord]
    have hf1 : ∀ s : Dec (F := F) A, Chr.cls F Ω m s = 1 → f s = 1 := fun s hs => Subtype.ext hs
    refine ⟨(zmodMulEquivOfGenerator hg hc).symm.toMonoidHom.comp f, dz_locConst _ ?_, fun s hs => ?_, ?_⟩
    · refine Subgroup.isOpen_mono (H₁ := (Chr.cls F Ω m).ker.subgroupOf _) (fun s hs => ?_)
        (hopen.preimage continuous_subtype_val)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf1 s hs, map_one]
    · rw [MonoidHom.comp_apply, hf1 s (hI hs), map_one]
    · exact zmodMulEquivOfGenerator_symm_apply_generator hg hc

end SlopeTestRemainingChoices

theorem UpperTheory.V.GC.decZhat :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∃ φ : Dec (F := F) A, IsFrob (F := F) A (normV v) φ.1 ∧ ((Ine (F := F) A).subgroupOf (Dec (F := F) A) ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
    ∀ n : ℕ, 0 < n → ∃ d : Dec (F := F) A →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ (Ine (F := F) A).subgroupOf (Dec (F := F) A), d s = 1) ∧ d φ = Multiplicative.ofAdd 1 := by
  intro F Ω _ _ _ _ _ v A hv
  exact dz_frob F Ω A v hv _ _ rfl rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

private theorem card_H0dual {R k Γ Γ' M : Type} [Field R] [Field k] [Finite k] [Algebra R k] [Group Γ] [Group Γ']
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] [Finite M]
    (ρ : Representation k Γ M) (ρ' : Representation R Γ' M) (e : Γ' ≃* Γ) (h : ∀ g m, ρ' g m = ρ (e g) m)
    (χ : Γ →* kˣ) (χ' : Γ' →* Rˣ) (hχ : ∀ g, (χ (e g) : k) = algebraMap R k (χ' g)) :
    Nat.card (Loc.H0dual χ ρ) = Nat.card (Loc.H0dual χ' ρ') := by
  haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective
  let T : Module.Dual k M →+ Module.Dual R M :=
    { toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R)
      map_zero' := by ext; simp
      map_add' := fun f f' => by ext; simp }
  have hT : ∀ f m, T f m = Algebra.trace R k (f m) := fun _ _ => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext m
    refine (traceForm_nondegenerate R k).1 (f m) fun a => ?_
    have := hT f (a • m)
    rw [hf, f.map_smul, smul_eq_mul, mul_comm] at this
    exact this.symm
  haveI : Finite (Module.Dual R M) := DFunLike.finite _
  have hbij : Function.Bijective T := hinj.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank])
  refine Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)
  rw [Equiv.ofBijective_apply]
  constructor
  · intro hf g x
    rw [hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro hf g x
    obtain ⟨g, rfl⟩ := e.surjective g
    have : f.comp (ρ (e g)) = (χ (e g) : k) • f := hinj (LinearMap.ext fun y => by
      have := hf g y
      rw [hT, hT, h] at this
      rw [hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def,
        map_smul, smul_eq_mul])
    exact LinearMap.congr_fun this x

private theorem card_twDual {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (ρ : Representation R Γ M) :
    Nat.card (H0 ((twDual χ ρ).comp (MonoidHom.id Γ))) = Nat.card (Loc.H0dual χ ρ) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)
  constructor
  · intro hy g m
    have e := congrArg (fun φ : TDual R M => φ (ρ g m)) (hy g)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e
    exact e.symm
  · intro hy g
    refine LinearMap.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]
    have := hy g (ρ g⁻¹ m)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem UpperTheory.V.GC.locEuler :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (Dec (F := F) A) M), ContAction ρ →
    Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + locDeg v * finrank k M) ∧
    (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ)) ∧ finrank k (H2 ρ) = finrank k (Loc.H0dual ((cycF F Ω l k).comp (Dec (F := F) A).subtype) ρ) := by
  intro hF hT hE0 F Ω _ _ _ _ _ l _ w A hAw k _ _ hc M _ _ _ _ _ ρ hρ
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F := F) A) M := Loc.resCoef (ZMod (l ^ 1)) ρ
  have h : ∀ g m, ρ' g m = ρ (MulEquiv.refl _ g) m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M A ρ' w one_pos hAw hρ'
  obtain ⟨⟨inv⟩, -, -, -, hb⟩ := hT F Ω l 1 M A ρ' w one_pos hAw hρ'
  have hE := hE0 F Ω l 1 M A ρ' w one_pos hAw hρ'
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, fun hw => ?_, fun hw => ?_, ?_⟩
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, pow_add, mul_comm (locDeg w), pow_mul, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1,
      Nat.card_congr e2]
    exact hE.1 hw
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
    exact hE.2 hw
  · apply Nat.pow_right_injective hk
    beta_reduce
    let χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype
    haveI : Finite (Module.Dual k M) := DFunLike.finite _
    haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
    let B : Type := H0 ((twDual χ ρ').comp (MonoidHom.id _))
    let E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv
    haveI : Finite B := Subtype.finite
    haveI := hc
    have hχ : ∀ g, ((((cycF F Ω l k).comp (Dec (F := F) A).subtype) (MulEquiv.refl _ g) : kˣ) : k) =
        algebraMap (ZMod (l ^ 1)) k (χ g) := fun g =>
      RingHom.congr_fun (Subsingleton.elim (ZMod.castHom (dvd_pow_self l one_ne_zero) k)
        (algebraMap (ZMod (l ^ 1)) k)) _
    rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2,
      card_H0dual ρ ρ' (MulEquiv.refl _) h _ χ hχ,
      ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.IsClosedOfClosedFiniteIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem isClosed_of_closed_finite_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (I J : Subgroup Γ) (hJI : J ≤ I) (hJ : IsClosed (J : Set Γ)) (h : J.relIndex I ≠ 0) : IsClosed (I : Set Γ) := by
  haveI : (J.subgroupOf I).FiniteIndex := ⟨h⟩
  have e : (I : Set Γ) = ⋃ q : I ⧸ J.subgroupOf I, (fun g : Γ => ((q.out : I) : Γ)⁻¹ * g) ⁻¹' (J : Set Γ) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hg
      refine ⟨(QuotientGroup.mk (⟨g, hg⟩ : I)), ?_⟩
      have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨g, hg⟩ : I) : I ⧸ J.subgroupOf I))
      exact Subgroup.mem_subgroupOf.1 this
    · rintro ⟨q, hq⟩
      have := I.mul_mem (q.out : I).2 (hJI hq)
      rwa [mul_inv_cancel_left] at this
  rw [e]
  exact isClosed_iUnion_of_finite fun q => hJ.preimage (by fun_prop)

theorem UpperTheory.V.GC.H2_unramified_inflation :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ → ∀ (I J : Subgroup Γ) [I.Normal] [J.Normal] (φ : Γ), J ≤ I → IsClosed (J : Set Γ) → ¬ l ∣ J.relIndex I → (∀ j ∈ J, ρ j = 1) →
    (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ → (∀ n : ℕ, 0 < n → ∃ d : Γ →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
    ∀ z : Z2 ρ, (∀ s t, ∀ j ∈ J, ∀ j' ∈ J, z.1 (s * j, t * j') = z.1 (s, t)) → ∃ b : Γ → M, IsLocallyConstant b ∧ (∀ s, ∀ j ∈ J, b (s * j) = b s) ∧ ∀ s t, z.1 (s, t) = ρ s (b t) - b (s * t) + b s := by
  intro l hl Γ _ _ _ _ _ _ k _ _ _ M _ _ _ _ _ ρ hρ I J _ _ φ hJI hJ hidx hJρ hφ hd z hz
  haveI : Finite M := Module.finite_of_finite k
  have hker : IsOpen (ρ.ker : Set Γ) := by
    have e : (ρ.ker : Set Γ) = ⋂ m : M, (fun g : Γ => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isOpen_iInter_of_finite fun m =>
      (isOpen_discrete _).preimage (Continuous.comp hρ (Continuous.prodMk_left m))
  have hI : IsClosed (I : Set Γ) := isClosed_of_closed_finite_index I J hJI hJ (fun h => hidx (h ▸ dvd_zero l))
  obtain ⟨a, ha1, ha2, ha3⟩ := UpperTheory.V.Alg.exists_locallyConstant_dOne_eq_cocycle_of_tame_inertia l k Γ M ρ hker I J hI hJ hJI (fun j hj => hJρ j hj) hidx ⟨φ, hφ⟩
    (by
      intro n
      obtain ⟨d, hd1, hd2, hd3⟩ := hd (l ^ n) (pow_pos hl.out.pos n)
      haveI : NeZero (l ^ n) := ⟨(pow_pos hl.out.pos n).ne'⟩
      refine ⟨d.ker, hd1.isOpen_fiber 1, fun s hs => hd2 s hs, ?_⟩
      have hs : d.range = ⊤ := by
        rw [eq_top_iff]
        intro x _
        refine ⟨φ ^ (Multiplicative.toAdd x).val, ?_⟩
        rw [map_pow, hd3, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
      rw [Subgroup.index_ker, hs, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])
    z.1 ((IsLocallyConstant.iff_continuous _).2 z.2.1)
    (by
      intro s t u
      have e := z.2.2 s t u
      rw [← sub_eq_zero, ← e]
      abel) hz
  refine ⟨a, ha1, ha2, fun s t => ?_⟩
  rw [← ha3]
  simp only [UpperTheory.V.Alg.dOne]
  abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LevelS
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem ine_le_open (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Subgroup (G F Ω)) (hK : IsOpen (K : Set (G F Ω))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
      Ine (F := F) A ≤ K := by
  obtain ⟨E, hE, hEK⟩ := (krullTopology_mem_nhds_one_iff F Ω (K : Set (G F Ω))).1 (hK.mem_nhds K.one_mem)
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  obtain ⟨T, hT⟩ := (Base.ramFinite F F E Ω).1
  refine ⟨T, fun v hv A hA g hg => hEK ?_⟩
  have h := hT v hv A hA (show g ∈ Base.galOf F F Ω ⊓ Ine (F := F) A from ⟨fun x => g.commutes x, hg⟩)
  exact (IntermediateField.mem_fixingSubgroup_iff E g).2 fun x hx => h ⟨x, hx⟩

theorem UpperTheory.V.GC.levelS :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GLink l S K π →
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 F))) (p : GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) →* Γ), S ⊆ S' ∧ Continuous p ∧ Function.Surjective p ∧ p.comp (toGS Ω _) = π ∧ ∀ A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (A v) v) →
    p.ker = (Subgroup.normalClosure (⋃ q : {v // v ∈ S' ∧ v ∉ S}, (((Ine (F := F) (A q.1) ⊓ K).map (toGS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) : Subgroup _) : Set (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))))))).topologicalClosure := by
  intro F Ω _ _ _ _ _ l _ S K Γ _ _ _ _ _ _ π h
  classical
  obtain ⟨T, hT⟩ := ine_le_open F Ω K h.isOpen
  have hgen : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ g ∈ Ine (F := F) B, g ∈ K → π g = 1 := by
    intro v hv B hB g hg hgK
    rw [← MonoidHom.mem_ker, h.ker]
    refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
    simp only [Set.mem_iUnion]
    exact ⟨v, hv, B, hB, hg, hgK⟩
  have hcl : IsClosed (π.ker : Set (G F Ω)) := isClosed_singleton.preimage h.cont
  have hNS : NS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))) ≤ π.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, B, hB, hg⟩ := hg
    exact hgen v (fun h' => hv (Finset.mem_union_left _ h')) B hB g hg
      (hT v (fun h' => hv (Finset.mem_union_right _ h')) B hB hg)
  have hp : Continuous (QuotientGroup.lift _ π hNS) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 h.cont
  refine ⟨S ∪ T, QuotientGroup.lift _ π hNS, Finset.subset_union_left, hp, fun y => ?_, rfl, fun A hA => ?_⟩
  · obtain ⟨g, rfl⟩ := h.onto y
    exact ⟨toGS Ω _ g, rfl⟩
  generalize hN : (Subgroup.normalClosure (⋃ q : {v // v ∈ S ∪ T ∧ v ∉ S}, (((Ine (F := F) (A q.1) ⊓ K).map
    (toGS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F)))) : Subgroup _) :
      Set (GS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))))))).topologicalClosure = N
  haveI hNn : N.Normal := by
    rw [← hN]
    exact Subgroup.is_normal_topologicalClosure _
  have hNc : IsClosed (N : Set (GS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))))) := by
    rw [← hN]
    exact Subgroup.isClosed_topologicalClosure _
  apply le_antisymm
  · have key : π.ker ≤ N.comap (toGS Ω _) := by
      rw [h.ker]
      refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
        (hNc.preimage QuotientGroup.continuous_mk)
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨v, hv, B, hB, hg, hgK⟩ := hg
      by_cases hvS : v ∈ S ∪ T
      · obtain ⟨u, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA v) hB
        have hm : u⁻¹ * g * u ∈ N.comap (toGS Ω _) := by
          rw [← hN]
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          exact Set.mem_iUnion.2 ⟨⟨v, hvS, hv⟩,
            Subgroup.mem_map_of_mem _ ⟨GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg, h.normal.conj_mem' g hgK u⟩⟩
        have := (hNn.comap (toGS Ω _)).conj_mem _ hm u
        simpa [mul_assoc] using this
      · have h1 : toGS Ω ((S ∪ T : Finset _) : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
          refine (QuotientGroup.eq_one_iff g).2 ?_
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          simp only [Set.mem_iUnion]
          exact ⟨v, hvS, B, hB, hg⟩
        show toGS Ω _ g ∈ N
        rw [h1]
        exact N.one_mem
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact key hx
  · rw [← hN]
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) (isClosed_singleton.preimage hp)
    intro x hx
    obtain ⟨q, g, hg, rfl⟩ := Set.mem_iUnion.1 hx
    exact hgen q.1 q.2.2 _ (hA q.1) g hg.1 hg.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Imports
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PhiGam
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem pG_nat {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ v ∈ S, ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  refine ⟨∏ v ∈ S, Ideal.absNorm v.asIdeal, Finset.prod_ne_zero_iff.2 fun v _ h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h),
    fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal) hv
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

private theorem pG_lc {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group M]
    (φ : H →* M) (h : IsOpen (φ.ker : Set H)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H)) := h.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H) by simp)] with y hy
  have : φ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

theorem UpperTheory.V.GC.phiGam :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GLink l S K π → Alg.PhiCond Γ l := by
  intro F Ω _ _ _ _ _ l hl S K Γ _ _ _ _ _ _ π hL H hH
  haveI : IsGalois F Ω := {}
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨N, hN, hNS⟩ := pG_nat S
  let V : Subgroup (G F Ω) := (H.comap π ⊓ K) ⊓ MulAction.stabilizer (G F Ω) ζ
  have hVo : IsOpen (V : Set (G F Ω)) :=
    ((hH.preimage hL.cont).inter hL.isOpen).inter (stabilizer_isOpen_of_isIntegral ζ)
  let E : IntermediateField F Ω := IntermediateField.fixedField V
  have hE : E.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, V.isClosed_of_isOpen hVo⟩
  haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [← hE] at hVo; exact hVo)
  haveI : NumberField E := NumberField.of_module_finite F E
  have hmem : ∀ σ : G E Ω, Base.galEmb F E Ω σ ∈ V := fun σ => by
    rw [← hE, IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => σ.commutes ⟨x, hx⟩
  have hgal : V ≤ Base.galOf F E Ω := fun u hu x => x.2 ⟨u, hu⟩
  have hζE : ζ ∈ E := fun v => v.2.2
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : E) l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap E Ω) hζ (algebraMap E Ω).injective
  haveI := (Kum.finChar E Ω l N _ hl.out.ne_zero hN hζ').to_subtype
  let e : G E Ω →* H := (π.comp (Base.galEmb F E Ω)).codRestrict H fun σ => (hmem σ).1.1
  have he : Continuous e := (hL.cont.comp (Base.galEmbTop F E Ω).1.continuous).subtype_mk _
  have hker : ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, e g = 1 := by
    intro A hA g hg
    by_cases hT : A = ⊤
    · subst hT
      rw [(Kum.placeDict E Ω).1, Subgroup.mem_bot] at hg
      rw [hg, map_one]
    · obtain ⟨v, hv⟩ := (Kum.placeDict F Ω).2.1 A hT
      have hvS : v ∉ S := fun h => hA (((Kum.placeDict F Ω).2.2.2 A v N hv).2 (hNS v h))
      have hI : Base.galEmb F E Ω g ∈ Ine (F := F) A := ⟨hg.1, hg.2⟩
      have : Base.galEmb F E Ω g ∈ π.ker := by
        rw [hL.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨v, hvS, A, hv, hI, (hmem g).1.2⟩
      exact Subtype.ext this
  haveI : Finite (G F Ω ⧸ V) := V.quotient_finite_of_isOpen hVo
  have hfin : Finite (H ⧸ e.range) := by
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have h1 : (V.map π).FiniteIndex :=
      ⟨fun h => Subgroup.FiniteIndex.index_ne_zero (H := V)
        (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd V hL.onto))⟩
    have h2 : (V.map π).subgroupOf H ≤ e.range := by
      rintro x ⟨u, hu, hx⟩
      exact ⟨Kum.toGal E hgal ⟨u, hu⟩, Subtype.ext hx⟩
    haveI := Subgroup.finiteIndex_of_le h2
    infer_instance
  refine Finite.of_injective (β := {φ : G E Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, φ g = 0} ×
      (H ⧸ e.range → Multiplicative (ZMod l)))
    (fun φ => (⟨fun g => Multiplicative.toAdd (φ.1 (e g)), ((pG_lc φ.1 φ.2).comp_continuous he).comp _,
      fun a b => by simp only [map_mul, toAdd_mul], fun A hA g hg => by
        show Multiplicative.toAdd (φ.1 (e g)) = 0
        rw [hker A hA g hg, map_one, toAdd_one]⟩, fun q => φ.1 q.out)) ?_
  intro φ ψ h
  have h1 : ∀ g, φ.1 (e g) = ψ.1 (e g) := fun g =>
    Multiplicative.toAdd.injective (congrFun (congrArg Subtype.val (congrArg Prod.fst h)) g)
  have h2 : ∀ q : H ⧸ e.range, φ.1 q.out = ψ.1 q.out := congrFun (congrArg Prod.snd h)
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := QuotientGroup.mk_out_eq_mul e.range x
  have h3 := h2 (QuotientGroup.mk x)
  rw [hg, map_mul, map_mul, h1] at h3
  exact mul_right_cancel h3
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

theorem UpperTheory.V.GC.phi :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → Alg.PhiCond Φ.Γ l := by
  intro F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c h
  exact UpperTheory.V.GC.phiGam F Ω l S K Φ.Γ π h.g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.EqOneOfPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

open scoped Pointwise in
private theorem galEmb_mem_inertia (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω]
    [Algebra k Ω] [Algebra E Ω] [Algebra k E] [IsScalarTower k E Ω] (Av : ValuationSubring Ω)
    (σ : G E Ω) (hσ : σ ∈ Ine Av) : UpperTheory.V.Base.galEmb k E Ω σ ∈ Ine Av := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hd, hv⟩ := hσ
  refine ⟨?_, fun x hx => by rw [UpperTheory.V.Base.galEmb_apply]; exact hv x hx⟩
  rw [MulAction.mem_stabilizer_iff] at hd ⊢
  conv_rhs => rw [← hd]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def,
    AlgEquiv.smul_def, UpperTheory.V.Base.galEmb_apply]

private theorem valuation_lt_one_iff_zero_or_inv_not_mem {Ω : Type} [Field Ω] (Av : ValuationSubring Ω) (x : Ω) :
    Av.valuation x < 1 ↔ (x = 0 ∨ x⁻¹ ∉ Av) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [← ValuationSubring.valuation_le_one_iff, not_le, map_inv₀]
    simp only [hx, false_or]
    rw [← map_inv₀, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

open scoped Pointwise in
private theorem conj_mem_inertia_of_mem_inertia_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (Av : ValuationSubring Ω) (σ τ : G F Ω) (hτ : τ ∈ Ine (σ • Av)) : σ⁻¹ * τ * σ ∈ Ine Av := by
  rw [mem_Ine] at hτ ⊢
  obtain ⟨hd, hv⟩ := hτ
  rw [MulAction.mem_stabilizer_iff] at hd
  refine ⟨?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hd, inv_smul_smul]
  · have hx' : σ x ∈ σ • Av := ValuationSubring.smul_mem_pointwise_smul σ x Av
      ((ValuationSubring.valuation_le_one_iff _ _).1 hx)
    have h := hv (σ x) ((ValuationSubring.valuation_le_one_iff _ _).2 hx')
    rw [valuation_lt_one_iff_zero_or_inv_not_mem] at h ⊢
    have he : (σ⁻¹ * τ * σ) x - x = σ⁻¹ (τ (σ x) - σ x) := by
      simp [map_sub]
    rw [he]
    rcases h with h | h
    · left; rw [h, map_zero]
    · right
      rw [← map_inv₀]
      intro hm
      apply h
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
      exact hm

private theorem eq_one_of_pow_coprime_in_pGroup {B : Type} [CommGroup B] {l : ℕ} (hl : l.Prime) (hB : IsPGroup l B)
    (y : B) (n : ℕ) (hn : ¬ l ∣ n) (hy : y ^ n = 1) : y = 1 := by
  obtain ⟨m, hm⟩ := hB y
  have h1 := orderOf_dvd_of_pow_eq_one hm
  have h2 := orderOf_dvd_of_pow_eq_one hy
  have hc : Nat.Coprime (l ^ m) n := Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hl).2 hn)
  have : orderOf y ∣ 1 := by
    rw [← hc]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

open UpperTheory.V.Base UpperTheory.V.Kum in
theorem UpperTheory.V.GC.cl :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → ∃ h : ℕ, h ≠ 0 ∧ ∀ (B : Type) [CommGroup B] [Finite B], IsPGroup l B → ∀ χ : Φ.G0 →* B,
    IsOpen (χ.ker : Set Φ.G0) → (∀ p : Φ.V × Bool, ∀ g ∈ Φ.Iv p.1, χ (Φ.loc2 p g) = 1) → ∀ g, χ g ^ h = 1 := by
  intro F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c hL
  classical
  set U : Subgroup (G F Ω) := Φ.del.ker.comap π with hU
  have hUo : IsOpen (U : Set (G F Ω)) := hL.g.cont.isOpen_preimage _ hL.del_open
  let Uc : ClosedSubgroup (G F Ω) := ⟨U, U.isClosed_of_isOpen hUo⟩
  set E : IntermediateField F Ω := IntermediateField.fixedField (Uc : Subgroup (G F Ω)) with hE
  have hEU : E.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField Uc
  haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [hEU]; exact hUo)
  haveI : NumberField E := inferInstance
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  have hgal : UpperTheory.V.Base.galOf F E Ω = U := by
    rw [← hEU]
    ext σ
    simp [UpperTheory.V.Base.galOf, IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨2 * Nat.card (ClassGroup (𝓞 E)), ?_, ?_⟩
  · have : 0 < Nat.card (ClassGroup (𝓞 E)) := Nat.card_pos
    omega
  intro B _ _ hB χ hχo hχI g
  have hmemU : ∀ σ : G E Ω, π (UpperTheory.V.Base.galEmb F E Ω σ) ∈ Φ.del.ker := fun σ => by
    have := UpperTheory.V.Base.galEmb_mem F E Ω σ
    rw [hgal] at this
    exact this
  let f : G E Ω →* Φ.G0 := (π.comp (UpperTheory.V.Base.galEmb F E Ω)).codRestrict Φ.del.ker hmemU
  let ψ : G E Ω →* B := (χ.comp f) ^ 2
  have key : ∀ (Av : ValuationSubring Ω) (τ : G F Ω), τ ∈ Ine Av → ∀ hτ : π τ ∈ Φ.del.ker, χ ⟨π τ, hτ⟩ = 1 := by
    intro Av τ hτA hτ
    have hZ : ∀ y : Ω, IsIntegral ℤ y → y ∈ Av := by
      intro y hy
      have hy' : IsIntegral Av y := hy.tower_top
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hy'
      rw [← ha]
      exact a.2
    let φ : 𝓞 F →+* Av := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict Av
      (fun x => hZ _ ((x.2).map (IsScalarTower.toAlgHom ℤ F Ω)))
    let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal Av).comap φ
    have hP : ∀ x : 𝓞 F, x ∈ P ↔ Av.valuation (algebraMap F Ω x) < 1 := by
      intro x
      exact (Av.valuation_lt_one_iff (φ x))
    by_cases hPb : P = ⊥
    · have hall : ∀ y : Ω, y ∈ Av := by
        intro y
        haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
        haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
        haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
        have halg : IsAlgebraic ℤ y := by
          rw [IsFractionRing.isAlgebraic_iff ℤ ℚ Ω]
          exact Algebra.IsAlgebraic.isAlgebraic y
        obtain ⟨m, hm0, hm⟩ := halg.exists_integral_multiple
        have h1 : m • y ∈ Av := hZ _ hm
        have hcast : algebraMap F Ω ((m : 𝓞 F) : F) = (m : Ω) := by simp
        have h2 : Av.valuation (m : Ω) = 1 := by
          have hnot : (m : 𝓞 F) ∉ P := by
            rw [hPb, Ideal.mem_bot]
            exact_mod_cast hm0
          rw [hP, hcast] at hnot
          have hle : Av.valuation (m : Ω) ≤ 1 := (Av.valuation_le_one_iff _).2 (intCast_mem Av m)
          exact le_antisymm hle (not_lt.1 hnot)
        rw [← Av.valuation_le_one_iff] at h1 ⊢
        rw [zsmul_eq_mul, map_mul, h2, one_mul] at h1
        exact h1
      have hτ1 : τ = 1 := by
        ext x
        rw [mem_Ine] at hτA
        have h := hτA.2 x ((Av.valuation_le_one_iff x).2 (hall x))
        rw [valuation_lt_one_iff_zero_or_inv_not_mem] at h
        rcases h with h | h
        · simpa [sub_eq_zero] using h
        · exact absurd (hall _) h
      have : (⟨π τ, hτ⟩ : Φ.G0) = 1 := by
        apply Subtype.ext
        simp [hτ1]
      rw [this, map_one]
    · haveI : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal Av)
      let v : HeightOneSpectrum (𝓞 F) := ⟨P, inferInstance, hPb⟩
      have hA : IsPlaceOver Av v := fun x => (hP x).symm
      by_cases hvS : v ∈ S
      · have hlv : (l : 𝓞 F) ∈ v.asIdeal := hL.only v hvS
        obtain ⟨u, hu⟩ := (hL.loc.mem v).2 hlv
        have hAu : IsPlaceOver Av (pl u) := hu ▸ hA
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hL.loc.isOver u) hAu
        rw [← hσ] at hτA
        have hc := conj_mem_inertia_of_mem_inertia_smul (A u) σ τ hτA
        have hdec : σ⁻¹ * τ * σ ∈ (ι u).range := by
          rw [hL.loc.range u]
          exact Ine_le_Dec _ hc
        obtain ⟨s, hs⟩ := hdec
        have hsI : s ∈ Φ.Iv u := by
          rw [hL.ine u, Subgroup.mem_comap, hs]
          exact hc
        have hπτ : π τ = π σ * ((Φ.loc0 u s : Φ.G0) : Φ.Γ) * (π σ)⁻¹ := by
          have h1 : ((Φ.loc0 u s : Φ.G0) : Φ.Γ) = π (ι u s) := hL.loc_eq u s
          rw [h1, hs, map_mul, map_mul, map_inv]
          group
        rcases Int.units_eq_one_or (Φ.del (π σ)) with hd | hd
        · have ha : π σ ∈ Φ.del.ker := hd
          have : (⟨π τ, hτ⟩ : Φ.G0) = ⟨π σ, ha⟩ * Φ.loc0 u s * (⟨π σ, ha⟩ : Φ.G0)⁻¹ := by
            apply Subtype.ext
            simp [hπτ]
          rw [this, map_mul, map_mul, map_inv, mul_comm (χ _), mul_inv_cancel_right]
          have h := hχI (u, false) s hsI
          simpa [UpperTheory.V.Fr.Frame.loc2] using h
        · have ha : Φ.c⁻¹ * π σ ∈ Φ.del.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hd, hL.del_c]
            rfl
          have : (⟨π τ, hτ⟩ : Φ.G0) =
              Φ.conj (⟨Φ.c⁻¹ * π σ, ha⟩ * Φ.loc0 u s * (⟨Φ.c⁻¹ * π σ, ha⟩ : Φ.G0)⁻¹) := by
            apply Subtype.ext
            simp only [UpperTheory.V.Fr.Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
            simp [hπτ]
            group
          rw [this, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, mul_comm (χ _),
            mul_inv_cancel_right]
          have h := hχI (u, true) s hsI
          simpa [UpperTheory.V.Fr.Frame.loc2] using h
      · haveI := hL.g.normal
        set n := K.index with hn
        have hK : τ ^ n ∈ K := K.pow_index_mem τ
        have hI : τ ^ n ∈ Ine Av := (Ine Av).pow_mem hτA n
        have hT : τ ^ n ∈ tameN (↑S) K := by
          apply Subgroup.le_topologicalClosure
          apply Subgroup.subset_normalClosure
          refine Set.mem_iUnion₂.2 ⟨v, by simpa using hvS, Set.mem_iUnion₂.2 ⟨Av, hA, ?_⟩⟩
          exact Subgroup.mem_inf.2 ⟨hI, hK⟩
        have hπ : π (τ ^ n) = 1 := by
          rw [← MonoidHom.mem_ker, hL.g.ker]
          exact hT
        apply eq_one_of_pow_coprime_in_pGroup (Fact.out : l.Prime) hB _ n hL.g.idx
        rw [← map_pow]
        have : (⟨π τ, hτ⟩ : Φ.G0) ^ n = 1 := by
          apply Subtype.ext
          simp [← map_pow, hπ]
        rw [this, map_one]
  have hopen : IsOpen (ψ.ker : Set (G E Ω)) := by
    have hc : Continuous f := by
      have h1 : Continuous (UpperTheory.V.Base.galEmb F E Ω) :=
        (UpperTheory.V.Base.galEmbTop F E Ω).1.continuous
      exact (hL.g.cont.comp h1).subtype_mk _
    have h2 : IsOpen ((χ.comp f).ker : Set (G E Ω)) := hχo.preimage hc
    refine Subgroup.isOpen_mono ?_ h2
    intro x hx
    simp only [MonoidHom.mem_ker] at hx ⊢
    simp [ψ, hx]
  have hine : ∀ Av : ValuationSubring Ω, Ine Av ≤ ψ.ker := by
    intro Av σ hσ
    have h := key Av _ (galEmb_mem_inertia F E Ω Av σ hσ) (hmemU σ)
    rw [MonoidHom.mem_ker]
    have : ψ σ = χ ⟨π (UpperTheory.V.Base.galEmb F E Ω σ), hmemU σ⟩ ^ 2 := rfl
    rw [this, h, one_pow]
  have hconj : ∀ σ : G E Ω, IsConjOm σ.toRingEquiv → ψ σ = 1 := by
    intro σ ⟨j, hj⟩
    have hsq : σ * σ = 1 := by
      ext x
      apply j.injective
      simp only [AlgEquiv.mul_apply, AlgEquiv.one_apply]
      have := hj (σ x)
      simp only [AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv] at this hj
      rw [this, hj, Complex.conj_conj]
    have : ψ σ = χ (f (σ * σ)) := by
      simp [ψ, pow_two]
    rw [this, hsq, map_one, map_one]
  have hker := UpperTheory.V.Kum.artKer E Ω B ψ hopen hine hconj
  obtain ⟨τ, hτ⟩ := hL.g.onto (g : Φ.Γ)
  have hτU : τ ∈ UpperTheory.V.Base.galOf F E Ω := by
    rw [hgal]
    show π τ ∈ Φ.del.ker
    rw [hτ]
    exact g.2
  let σ : G E Ω := { τ with commutes' := fun x => hτU x }
  have hσ : f σ = g := by
    apply Subtype.ext
    show π (UpperTheory.V.Base.galEmb F E Ω σ) = g
    rw [← hτ]
    congr 1
  have h1 : ψ (σ ^ Nat.card (ClassGroup (𝓞 E))) = 1 := by
    apply hker
    rw [MonoidHom.mem_ker, map_pow]
    exact pow_card_eq_one'
  rw [map_pow] at h1
  have h2 : ψ σ = χ g ^ 2 := by
    simp [ψ, hσ]
  rw [h2, ← pow_mul] at h1
  exact h1
end
