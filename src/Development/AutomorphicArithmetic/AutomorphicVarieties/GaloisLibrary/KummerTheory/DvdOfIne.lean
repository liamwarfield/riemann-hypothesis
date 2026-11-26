module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen
public import GroundTheory.GlobalFields.ExistenceTheorem.PowerIndex
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem ram_one {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (L : IntermediateField K E) (h : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup) :
    (P.under (𝓞 L)).ramificationIdx (𝓞 K) = 1 := by
  have hb := v.ne_bot
  have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hb P
  have hqb : P.under (𝓞 L) ≠ ⊥ := Ideal.under_ne_bot _ hPb
  have : IsGaloisGroup L.fixingSubgroup L E :=
    .of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv L) fun _ _ ↦ rfl
  have : IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ L E
  have := v.isMaximal
  have : (P.under (𝓞 L)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqb
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have : Finite (𝓞 L ⧸ P.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L.fixingSubgroup) (P.under (𝓞 L)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[K] E)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P L.fixingSubgroup] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 L)) P
  have h4 : Nat.card (P.inertia L.fixingSubgroup) =
      Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := by
    rw [← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]
  rw [← h1, ← h2, h4] at h3
  have hpos : 0 < Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := Nat.card_pos
  rw [inf_eq_left.mpr h] at h3 hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)

private theorem dvd_of_ram {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (h : Q.ramificationIdx (𝓞 K) = 1) (n : ℕ) (b : L) (a : Kˣ) (hb : b ^ n = algebraMap K L a) :
    (n : ℤ) ∣ ordv v a := by
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have : w.asIdeal.LiesOver v.asIdeal := (inferInstance : Q.LiesOver v.asIdeal)
  have h1 := HeightOneSpectrum.valuation_liesOver L v w (a : K)
  rw [h, pow_one, ← hb, map_pow,
    ← HeightOneSpectrum.valuationOfNeZero_eq] at h1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, ← WithZero.coe_one, WithZero.coe_inj] at h1
    simp [ordv, h1]
  · have h0 : w.valuation L b ≠ 0 := fun e => by
      rw [e, zero_pow hn.ne'] at h1
      exact WithZero.coe_ne_zero h1
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hm, ← WithZero.coe_pow, WithZero.coe_inj] at h1
    rw [ordv, h1, toAdd_pow, dvd_neg, nsmul_eq_mul]
    exact dvd_mul_right _ _

private theorem dvd_fin {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal] (n : ℕ) (b : E) (a : Kˣ)
    (hb : b ^ n = algebraMap K E a) (h : ∀ τ ∈ P.inertia (E ≃ₐ[K] E), τ b = b) : (n : ℤ) ∣ ordv v a := by
  let L : IntermediateField K E := IntermediateField.fixedField (P.inertia (E ≃ₐ[K] E))
  have hle : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hbL : b ∈ L := (IntermediateField.mem_fixedField_iff _ _).2 h
  have : (P.under (𝓞 L)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  exact dvd_of_ram v (P.under (𝓞 L)) (ram_one v P L hle) n ⟨b, hbL⟩ a (Subtype.ext hb)

theorem UpperTheory.V.Kum.dvdOfIne :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (β : Ω) (a : Kˣ), IsPlaceOver A v → β ^ n = algebraMap K Ω a → (∀ g ∈ Ine (F := K) A, g β = β) → (n : ℤ) ∣ ordv v a := by
  intro K Ω _ _ _ _ _ n A v β a hA hβ hI
  have : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField
  have hβL : β ∈ L := FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  have : NumberField L := NumberField.of_module_finite K _
  have hv : (CompanionTheory.PlaceDict.cen A).under (𝓞 K) = v.asIdeal := Ideal.ext fun x => hA x
  have : Algebra.IsIntegral (𝓞 K) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have hm : (CompanionTheory.PlaceDict.cen A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap (𝓞 K) (𝓞 Ω))
      (algebraMap_isIntegral_iff.mpr this) _ (by
      have := v.isMaximal
      rwa [← hv] at this)
  let P : Ideal (𝓞 L) := (CompanionTheory.PlaceDict.cen A).under (𝓞 L)
  have : P.LiesOver v.asIdeal := ⟨by rw [← hv]; exact (Ideal.under_under _).symm⟩
  refine dvd_fin v P n ⟨β, hβL⟩ a (Subtype.ext hβ) fun τ hτ => ?_
  obtain ⟨φ, h1, h2⟩ := CompanionTheory.PlaceDict.lift L (CompanionTheory.PlaceDict.cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact hτ x
  obtain ⟨h3, h4⟩ := CompanionTheory.PlaceDict.of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  have h5 : φ ∈ Ine (F := K) A := ⟨h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩
  rw [← h1]
  exact Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ h5))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HilbertNinety
@[reducible] noncomputable def UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

theorem UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90 :
    ∀ (K Ω : Type) [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsAlgClosure K Ω]
      (f : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω → Ω),
      IsLocallyConstant f →
        (∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f g ≠ (0 : Ω)) →
          (∀ (g h : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f (g * h) = f g * (g : Ω → Ω) (f h)) →
            ∃ (β : Ω), β ≠ (0 : Ω) ∧ ∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), (g : Ω → Ω) β = f g * β := by
  intro K Ω _ _ _ _ _ f hlc h0 hc
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : Gal(Ω/K)) :=
    (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : Gal(Ω/K)), h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set Gal(Ω/K)) := L.fixingSubgroup_isOpen
  haveI : Finite (Gal(Ω/K) ⧸ L.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (Gal(Ω/K) ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (Gal(Ω/K) ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : Gal(Ω/K)) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : Gal(Ω/K)) (x : Ω) := fun q x => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      funext x
      simpa [Finset.sum_apply] using hne x) (QuotientGroup.mk 1)
    exact h0 _ this
  obtain ⟨x, hx⟩ := hex
  have key : ∀ g : Gal(Ω/K),
      f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    have hq : g • q = QuotientGroup.mk (g * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)
    have hfix : (h : Gal(Ω/K)) (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2
    rw [MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix,
      AlgEquiv.mul_apply, map_mul, mul_assoc]
  refine ⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩
  have hk := key g
  generalize (∑ q, f q.out * χ q x) = b at hx hk
  have hg : g b ≠ 0 := (map_ne_zero g).2 hx
  rw [map_inv₀]
  field_simp
  rw [mul_comm]
  exact hk.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Imports
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.h90 :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (f : G K Ω → Ω), IsLocallyConstant f → (∀ g, f g ≠ 0) → (∀ g h, f (g * h) = f g * g (f h)) → ∃ β : Ω, β ≠ 0 ∧ ∀ g : G K Ω, g β = f g * β :=
  _root_.UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radExists :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) [NeZero n] (ζ : Ω) (η z : G K Ω → ZMod n), IsPrimitiveRoot ζ n → (∀ g : G K Ω, g ζ = ζ ^ (η g).val) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + η g * z h) →
    ∃ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a ∧ ∀ g : G K Ω, g β = ζ ^ (z g).val * β := by
  intro K Ω _ _ _ _ _ n _ ζ η z hζ hη hz hc
  have hmod : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => (pow_eq_pow_mod m hζ.pow_eq_one).symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  obtain ⟨β, hβ0, hβ⟩ := UpperTheory.V.Kum.h90 K Ω (fun g => ζ ^ (z g).val)
    (hz.comp fun x : ZMod n => ζ ^ x.val) (fun g => pow_ne_zero _ hζ0) (fun g h => by
      show ζ ^ (z (g * h)).val = ζ ^ (z g).val * g (ζ ^ (z h).val)
      rw [hc, ZMod.val_add, hmod, pow_add, ZMod.val_mul, hmod, map_pow, hη, ← pow_mul])
  haveI : IsGalois K Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g (β ^ n) = β ^ n := fun g => by
    rw [map_pow, hβ g, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β ^ n)).2 hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero n hβ0 ha.symm
  exact ⟨β, Units.mk0 a ha0, ha.symm, hβ⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RestrMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.restrMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) (U V : Subgroup (G F Ω)) (h : U ≤ V) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M), (XDual N V R M).map (restr R M h) ≤ XDual N U R M ∧ (EqHom N V ρ).map (restr R M h) ≤ EqHom N U ρ ∧ ∀ (σ : Ω ≃+* Ω) (s : R), (EqEig N V ρ σ s).map (restr R M h) ≤ EqEig N U ρ σ s := by
  intro F Ω _ _ _ _ _ N U V h R M _ _ _ ρ
  have hX : ∀ φ ∈ XDual N V R M, restr R M h φ ∈ XDual N U R M := by
    intro φ hφ
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (f := Subgroup.inclusion h) (continuous_inclusion h), fun a b => ?_, fun A u hu => ?_,
      fun A hA u hu => ?_⟩
    · exact h2 (Subgroup.inclusion h a) (Subgroup.inclusion h b)
    · exact h3 A (Subgroup.inclusion h u) hu
    · exact h4 A hA (Subgroup.inclusion h u) hu
  have hC : ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M), ∀ φ ∈ conjCond V σ T, restr R M h φ ∈ conjCond U σ T := by
    intro σ T φ hφ u u' hu
    exact hφ (Subgroup.inclusion h u) (Subgroup.inclusion h u') hu
  have hE : ∀ φ ∈ EqHom N V ρ, restr R M h φ ∈ EqHom N U ρ := by
    intro φ hφ
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    refine Submodule.mem_inf.2 ⟨hX φ h1, (Submodule.mem_iInf _).2 fun g => ?_⟩
    exact hC _ _ φ ((Submodule.mem_iInf _).1 h2 g)
  refine ⟨?_, ?_, fun σ s => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hX φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hE φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    exact Submodule.mem_inf.2 ⟨hE φ h1, hC _ _ φ h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenDirected
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.lenDirected :
    ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (W : Submodule R X) (P : ℕ → Submodule R X) (Bd : ℕ∞), Monotone P → W ≤ ⨆ n, P n →
    (∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) → Module.length R W ≤ Bd := by
  intro R X _ _ _ W P Bd hP hW hBd
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim, iSup_le_iff]
  intro p
  have hstep : ∀ i : Fin p.length, ∃ x : W, x ∈ p i.succ ∧ x ∉ p i.castSucc := by
    intro i
    exact SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hstep
  have hdir : Directed (· ≤ ·) P := hP.directed_le
  have hmem : ∀ i : Fin p.length, ∃ n, (x i : X) ∈ P n := by
    intro i
    exact (Submodule.mem_iSup_of_directed P hdir).mp (hW (x i).2)
  choose m hm using hmem
  obtain ⟨n, hn, hlen⟩ := hBd (Finset.univ.sup m)
  have hxn : ∀ i, (x i : X) ∈ P n := by
    intro i
    exact hP ((Finset.le_sup (Finset.mem_univ i)).trans hn) (hm i)
  let f : Submodule R W → Submodule R (P n) := fun S => (S.map W.subtype).comap (P n).subtype
  have hfmono : Monotone f := by
    intro S T hST
    exact Submodule.comap_mono (Submodule.map_mono hST)
  let q : LTSeries (Submodule R (P n)) :=
    { length := p.length
      toFun := fun i => f (p i)
      step := by
        intro i
        refine lt_of_le_of_ne (hfmono (p.step i).le) ?_
        intro heq
        have h1 : (⟨(x i : X), hxn i⟩ : P n) ∈ f (p i.succ) := by
          simp only [f, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map]
          exact ⟨x i, hx1 i, rfl⟩
        rw [← heq] at h1
        simp only [f, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map] at h1
        obtain ⟨y, hy, hyx⟩ := h1
        have : y = x i := Subtype.ext hyx
        exact hx2 i (this ▸ hy) }
  have hq := Order.LTSeries.length_le_krullDim q
  rw [← Module.coe_length] at hq
  exact hq.trans (WithBot.coe_le_coe.mpr hlen)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CobOfGen
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.cobOfGen :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (γ : Γ),
    Continuous χ → ContAction ρ → (∀ g, χ g = 1 → ∀ m, ρ g m = m) → (∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure) → (Function.Surjective fun m => ρ γ m - m) →
    ∀ z ∈ Z1 ρ, (∀ g, χ g = 1 → z g = 0) → z ∈ B1 ρ := by
  intro l _ Γ _ _ _ _ χ R M _ _ _ _ _ ρ γ hχ hρ hker hgen hsurj z hz hz0
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hm' : ρ γ m - m = z γ := hm
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, Module.End.mul_apply]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm'.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSUnit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem index_range_eq_card_ker {T : Type*} [CommGroup T] [Finite T] (f : T →* T) :
    f.range.index = Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.range
  have h2 := Subgroup.card_mul_index f.ker
  have hk : f.ker.index = Nat.card f.range := by
    show Nat.card (T ⧸ f.ker) = _
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hk] at h2
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h3 : Nat.card f.range * f.range.index = Nat.card f.range * Nat.card f.ker := by
    rw [h1, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

private theorem mem_unit_of_pow_mem {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {p : ℕ}
    (hp : p ≠ 0) {b : Kˣ} (hb : b ^ p ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have h := hb v hv
  rw [Units.val_pow_eq_pow_val, map_pow] at h
  simpa [hp] using h

private theorem powK_subgroupOf {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) {p : ℕ}
    (hp : p ≠ 0) : (powK (K := K) p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext x
  rw [Subgroup.mem_subgroupOf, powK.eq_1, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    rw [powMonoidHom_apply] at hb
    have hbS : b ∈ S.unit K := mem_unit_of_pow_mem hp (by rw [hb]; exact x.2)
    refine ⟨⟨b, hbS⟩, ?_⟩
    apply Subtype.ext
    simpa using hb
  · rintro ⟨c, hc⟩
    refine ⟨c.1, ?_⟩
    rw [← hc]
    simp

private theorem card_ker_eq {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n] :
    Nat.card (powMonoidHom n : CommGroup.torsion (S.unit K) →* CommGroup.torsion (S.unit K)).ker =
      Nat.card (rootsOfUnity n K) := by
  have hfin : ∀ ζ : rootsOfUnity n K, IsOfFinOrder (ζ : Kˣ) := fun ζ =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, (mem_rootsOfUnity _ _).mp ζ.2⟩
  have hS : ∀ ζ : rootsOfUnity n K, (ζ : Kˣ) ∈ S.unit K := fun ζ v _ =>
    GroundTheory.Global.SUnit.valuation_eq_one_of_isOfFinOrder (hfin ζ) v
  refine Nat.card_congr
    { toFun := fun t => ⟨t.1.1.1, (mem_rootsOfUnity _ _).mpr (by
        have h := congrArg (fun y : CommGroup.torsion (S.unit K) => ((y : S.unit K) : Kˣ))
          (MonoidHom.mem_ker.mp t.2)
        simpa using h)⟩
      invFun := fun ζ => ⟨⟨⟨ζ.1, hS ζ⟩, (CommGroup.mem_torsion _).mpr
          (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)⟩)⟩,
        MonoidHom.mem_ker.mpr (Subtype.ext (Subtype.ext (by
            simpa using (mem_rootsOfUnity _ _).mp ζ.2)))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem UpperTheory.V.Kum.cardSUnit :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n], S.Finite → Nat.card (S.unit K ⧸ (powK (K := K) n).subgroupOf (S.unit K)) = n ^ (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 + Nat.card S) * Nat.card (rootsOfUnity n K) := by
  intro K _ _ S n _ hS
  haveI : Finite S := hS
  rw [← Subgroup.index_eq_card, powK_subgroupOf S (NeZero.ne n),
    GroundTheory.Global.index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), GroundTheory.Global.SUnit.finrank_quotient_torsion,
    index_range_eq_card_ker, card_ker_eq, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClMapBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem clMapBasic_mem {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (τ : K ≃+* K')
    (I : Ideal (𝓞 K)) (y : 𝓞 K') :
    y ∈ I.map (RingOfIntegers.mapRingEquiv τ) ↔ ∃ x ∈ I, RingOfIntegers.mapRingEquiv τ x = y :=
  Ideal.mem_map_iff_of_surjective _ (RingOfIntegers.mapRingEquiv τ).surjective

private theorem clMapBasic_lemma {K K' K'' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K'') (c : ClassGroup (𝓞 K)) :
    clMap (τ.trans τ') c = clMap τ' (clMap τ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_map_mk0, class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = Ideal.map _ (Ideal.map _ _)
  ext y
  rw [clMapBasic_mem, clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv τ x, (clMapBasic_mem τ _ _).mpr ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (clMapBasic_mem τ _ _).mp hz
    exact ⟨x, hx, rfl⟩
private theorem clMap_refl_apply {K : Type} [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    clMap (RingEquiv.refl K) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map _ _ = _
  ext y
  rw [clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem UpperTheory.V.Kum.clMapBasic :
    ∀ (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K''),
    (∀ c, clMap (RingEquiv.refl K) c = c) ∧ (∀ c, clMap (τ.trans τ') c = clMap τ' (clMap τ c)) ∧ Function.Bijective (clMap τ) ∧
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K')), (∀ x, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ w.asIdeal) → clMap τ (primeCl v) = primeCl w := by
  intro K K' K'' _ _ _ _ _ _ τ τ'
  refine ⟨clMap_refl_apply, clMapBasic_lemma τ τ', ?_, ?_⟩
  · have hl : ∀ c, clMap τ.symm (clMap τ c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.self_trans_symm, clMap_refl_apply]
    have hr : ∀ c, clMap τ (clMap τ.symm c) = c := by
      intro c
      rw [← clMapBasic_lemma, RingEquiv.symm_trans_self, clMap_refl_apply]
    exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩
  · intro v w hvw
    unfold primeCl
    rw [class_map_mk0]
    congr 1
    apply Subtype.ext
    show Ideal.map _ _ = _
    ext y
    rw [clMapBasic_mem]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hvw x).mp hx
    · intro hy
      refine ⟨(RingOfIntegers.mapRingEquiv τ).symm y, ?_, ?_⟩
      · rw [hvw, RingEquiv.apply_symm_apply]
        exact hy
      · exact RingEquiv.apply_symm_apply _ y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LevCompact
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mem_princ_iff_norm_sub_one_le (l : ℕ) [Fact l.Prime] (a : ℕ) (x : ℤ_[l]ˣ) :
    x ∈ KStar.TotallyRealRoots.princ l a ↔ ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ)) := by
  have h : x ∈ KStar.TotallyRealRoots.princ l a ↔ PadicInt.toZModPow a (x : ℤ_[l]) = 1 := by
    simp [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff]
  rw [h, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero]

private theorem princ_isClosed (l : ℕ) [Fact l.Prime] (a : ℕ) :
    IsClosed ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
  have e : ((KStar.TotallyRealRoots.princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) =
      {x : ℤ_[l]ˣ | ‖(x : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(a : ℤ))} := by
    ext x
    exact mem_princ_iff_norm_sub_one_le l a x
  rw [e]
  exact isClosed_le (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

private theorem princ_antitone (l : ℕ) [Fact l.Prime] {a b : ℕ} (hab : a ≤ b) (x : ℤ_[l]ˣ)
    (hx : x ∈ KStar.TotallyRealRoots.princ l b) : x ∈ KStar.TotallyRealRoots.princ l a := by
  rw [mem_princ_iff_norm_sub_one_le] at hx ⊢
  refine hx.trans (zpow_le_zpow_right₀ ?_ (by omega))
  exact_mod_cast (Fact.out : l.Prime).one_lt.le

private theorem eq_one_of_mem_all_princ (l : ℕ) [Fact l.Prime] (x : ℤ_[l]ˣ)
    (hx : ∀ a, x ∈ KStar.TotallyRealRoots.princ l a) : x = 1 := by
  apply Units.ext
  refine (PadicInt.ext_of_toZModPow (x := (x : ℤ_[l])) (y := 1)).mp fun a => ?_
  have h := hx a
  simp only [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff] at h
  simpa using h

theorem UpperTheory.V.Kum.levCompact :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (n : ℕ) (T : Type) [TopologicalSpace T] [CompactSpace T] (M : Type) [Zero M] (ψ : T × levU l U n → M), IsClosed (U : Set (G F Ω)) → IsLocallyConstant ψ →
    (∀ t (u : levU l U n), u.1 ∈ cycU l U → ψ (t, u) = 0) → ∃ m, n ≤ m ∧ ∀ t (u : levU l U n), u.1 ∈ levU l U m → ψ (t, u) = 0 := by
  intro F Ω _ _ _ _ _ l _ U n T _ _ M _ ψ hU hψ h0
  have memL : ∀ (m : ℕ) (x : G F Ω), x ∈ levU l U m ↔ x ∈ U ∧ cycZ F Ω l x ∈ KStar.TotallyRealRoots.princ l m := by
    intro m x
    simp [UpperTheory.V.Base.levU, Subgroup.mem_inf, Subgroup.mem_comap]
  have memC : ∀ x : G F Ω, x ∈ cycU l U ↔ x ∈ U ∧ cycZ F Ω l x = 1 := by
    intro x
    simp [UpperTheory.V.Base.cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
  have closedL : ∀ m : ℕ, IsClosed ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro m
    have e : ((levU l U m : Subgroup (G F Ω)) : Set (G F Ω)) =
        (U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' ((KStar.TotallyRealRoots.princ l m : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
      ext x
      exact memL m x
    rw [e]
    exact hU.inter ((princ_isClosed l m).preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (levU l U n) := isCompact_iff_compactSpace.mp (closedL n).isCompact
  let K : Set (T × levU l U n) := {p | ψ p ≠ 0}
  have hKc : IsClosed K := by
    have ho : IsOpen (ψ ⁻¹' {0}) := hψ.isOpen_fiber 0
    exact ho.isClosed_compl
  let t : ℕ → Set (T × levU l U n) := fun m => {p | (p.2 : G F Ω) ∈ levU l U m}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (closedL m).preimage (continuous_subtype_val.comp continuous_snd)
  have hst : K ∩ ⋂ m, t m = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hall
    apply hp
    obtain ⟨s, u⟩ := p
    apply h0 s u
    rw [memC]
    refine ⟨((memL n u.1).1 u.2).1, eq_one_of_mem_all_princ l _ fun a => ((memL a u.1).1 (hall a)).2⟩
  obtain ⟨v, hv⟩ := hKc.isCompact.elim_finite_subfamily_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst)
  refine ⟨max n (v.sup id), le_max_left _ _, ?_⟩
  intro s u hu
  by_contra hne
  have hmem : (s, u) ∈ K ∩ ⋂ i ∈ v, t i := by
    refine ⟨hne, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    show (u : G F Ω) ∈ levU l U i
    rw [memL] at hu ⊢
    refine ⟨hu.1, princ_antitone l ?_ _ hu.2⟩
    exact (Finset.le_sup (f := id) hi).trans (le_max_right _ _)
  exact Set.disjoint_left.mp hv hmem.1 hmem.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClSubUniv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.clSubUniv :
    ∀ (K : Type) [Field K] [NumberField K], clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  intro K _ _
  classical
  have key : ∀ I : Ideal (𝓞 K), ∀ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)),
      ClassGroup.mk0 ⟨I, hI⟩ ∈ clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro hI
      exact absurd hI (zero_notMem_nonZeroDivisors)
    | h₂ u hu =>
      intro hI
      have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
      subst hu'
      have : (⟨⊤, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = 1 := Subtype.ext Ideal.one_eq_top.symm
      rw [this, map_one]
      exact Subgroup.one_mem _
    | h₃ a p ha hp ih =>
      intro hI
      have ha' : a ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero ha
      have hp0 : p ≠ 0 := hp.ne_zero
      have hp' : p ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hp0
      have hsplit : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨p, hp'⟩ * ⟨a, ha'⟩ := rfl
      rw [hsplit, map_mul]
      refine Subgroup.mul_mem _ ?_ (ih ha')
      have hpr : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
      let v : HeightOneSpectrum (𝓞 K) := ⟨p, hpr, hp0⟩
      have hv : primeCl v = ClassGroup.mk0 ⟨p, hp'⟩ := rfl
      rw [← hv]
      exact Subgroup.subset_closure ⟨v, Set.mem_univ _, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective x
  exact key I hI
end
