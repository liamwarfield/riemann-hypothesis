module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem exists_coef_ge (l : ℕ) [Fact l.Prime] (A : Subalgebra ℤ_[l] (PadicAlgCl l)) [hA : Module.Finite ℤ_[l] A] :
    ∃ c : Coef l, A ≤ c.O := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule A).FG := Module.Finite.iff_fg.1 hA
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩
  change Subalgebra.toSubmodule A ≤ Subalgebra.toSubmodule ((integralClosure ℤ_[l] K).map f)
  rw [← hs, Submodule.span_le]
  intro x hx
  have hxA : x ∈ A := by
    change x ∈ Subalgebra.toSubmodule A
    rw [← hs]
    exact Submodule.subset_span hx
  have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hxA⟩ : A)).map A.val
  exact ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩

private theorem unram_adjoin {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    {ζ : S} (hζ : ζ ^ n = 1) : Algebra.FormallyUnramified R (Algebra.adjoin R {ζ}) := by
  let z : Algebra.adjoin R {ζ} := ⟨ζ, Algebra.self_mem_adjoin_singleton R ζ⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  let D := KaehlerDifferential.D R (Algebra.adjoin R {ζ})
  have hDz : D z = 0 := by
    have h := D.leibniz_pow z n
    rw [hz, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul R] at h
    exact ((IsUnit.of_pow_eq_one hz hn0).pow _).smul_eq_zero.1 (hn.smul_eq_zero.1 h.symm)
  have hD : ∀ x (hx : x ∈ Algebra.adjoin R {ζ}), D ⟨x, hx⟩ = 0 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain rfl := hx; exact hDz
    | algebraMap r => exact D.map_algebraMap r
    | add x y hx hy h1 h2 =>
      have := D.map_add ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, add_zero] at this
      exact this
    | mul x y hx hy h1 h2 =>
      have := D.leibniz ⟨x, hx⟩ ⟨y, hy⟩
      rw [h1, h2, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨⟨fun a b => ?_⟩⟩
  have h := KaehlerDifferential.span_range_derivation R (Algebra.adjoin R {ζ})
  have h0 : (⊤ : Submodule (Algebra.adjoin R {ζ}) Ω[Algebra.adjoin R {ζ}⁄R]) ≤ ⊥ := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hD x.1 x.2
  rw [(Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := a))), (Submodule.mem_bot _).1 (h0 (Submodule.mem_top (x := b)))]

private theorem eO_eq_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hm : Ideal.span {(l : O)} = IsLocalRing.maximalIdeal O) : eO l O = 1 := by
  unfold eO
  rw [hm, Module.length_eq_one_iff]
  exact isSimpleModule_iff_quot_maximal.2 ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩

private theorem exists_unram (l : ℕ) [hl : Fact l.Prime] (n : ℕ) [NeZero n] (hn : ¬ l ∣ n) :
    ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  have hu : IsUnit (n : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
  let A : Subalgebra ℤ_[l] (PadicAlgCl l) := Algebra.adjoin ℤ_[l] {ζ}
  haveI hfin : Module.Finite ℤ_[l] A := Module.Finite.iff_fg.2 hζi.fg_adjoin_singleton
  haveI : Algebra.FormallyUnramified ℤ_[l] A := unram_adjoin (NeZero.ne n) hu hζ.pow_eq_one
  obtain ⟨c, hc⟩ := exists_coef_ge l A
  let f : A →ₐ[ℤ_[l]] c.O := Subalgebra.inclusion hc
  have hf : Function.Injective f := Subalgebra.inclusion_injective hc
  haveI hloc : IsLocalRing A := by
    letI : Algebra A c.O := f.toAlgebra
    haveI : IsScalarTower ℤ_[l] A c.O := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    haveI : Algebra.IsIntegral A c.O := Algebra.IsIntegral.tower_top ℤ_[l]
    haveI : FaithfulSMul A c.O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
    haveI : IsLocalHom (algebraMap A c.O) := inferInstance
    exact (algebraMap A c.O).domain_isLocalRing
  have hinj : Function.Injective (algebraMap ℤ_[l] A) := by
    intro a b hab
    have h := congrArg (fun x : A => (x : PadicAlgCl l)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h)
  haveI : FaithfulSMul ℤ_[l] A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsLocalHom (algebraMap ℤ_[l] A) := inferInstance
  have hm : Ideal.span {(l : A)} = IsLocalRing.maximalIdeal A := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := ℤ_[l]), PadicInt.maximalIdeal_eq_span_p,
      Ideal.map_span, Set.image_singleton, map_natCast]
  have hnf : ¬ IsField A := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[l] A
  have hp : (IsLocalRing.maximalIdeal A).IsPrincipal := hm ▸ inferInstance
  have hd : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hp
  refine ⟨⟨A, hd, hfin⟩, ?_, ?_⟩
  · exact eO_eq_one l A hm
  · refine ⟨⟨⟨ζ, Algebra.self_mem_adjoin_singleton _ ζ⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := A.val) hζ Subtype.val_injective

theorem UpperTheory.V.HV.coefSup :
    ∀ (l : ℕ) [Fact l.Prime], (∀ c c' : Coef l, ∃ c'' : Coef l, c.O ≤ c''.O ∧ c'.O ≤ c''.O) ∧
      (∀ (n : ℕ) [NeZero n], ¬ l ∣ n → ∃ c : Coef l, eO l c.O = 1 ∧ HasEnoughRootsOfUnity c.O n) ∧
      (∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ∃ c' : Coef l, c.O ≤ c'.O ∧ x ∈ c'.O) ∧
      ∀ (c : Coef l) (x : PadicAlgCl l), IsIntegral ℤ_[l] x → (∃ a b : c.O, (b : PadicAlgCl l) ≠ 0 ∧ x * b = a) → x ∈ c.O := by
  intro l _
  refine ⟨fun c c' => ?_, fun n _ hn => exists_unram l n hn, fun c x hx => ?_, fun c x hx ⟨a, b, hb, hab⟩ => ?_⟩
  · haveI := Subalgebra.finite_sup c.O c'.O
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ c'.O)
    exact ⟨d, le_sup_left.trans hd, le_sup_right.trans hd⟩
  · haveI : Module.Finite ℤ_[l] (Algebra.adjoin ℤ_[l] {x}) := Module.Finite.iff_fg.2 hx.fg_adjoin_singleton
    haveI := Subalgebra.finite_sup c.O (Algebra.adjoin ℤ_[l] {x})
    obtain ⟨d, hd⟩ := exists_coef_ge l (c.O ⊔ Algebra.adjoin ℤ_[l] {x})
    exact ⟨d, le_sup_left.trans hd, (le_sup_right.trans hd) (Algebra.self_mem_adjoin_singleton _ x)⟩
  · let g : FractionRing c.O →ₐ[c.O] PadicAlgCl l :=
      IsFractionRing.liftAlgHom (g := Algebra.ofId c.O (PadicAlgCl l)) Subtype.val_injective
    have hg : g (algebraMap c.O _ a / algebraMap c.O _ b) = x := by
      rw [map_div₀, g.commutes, g.commutes]
      exact (div_eq_iff hb).2 hab.symm
    have hi : IsIntegral c.O (algebraMap c.O (FractionRing c.O) a / algebraMap c.O _ b) := by
      rw [← isIntegral_algHom_iff g g.injective, hg]
      exact hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hg, ← hy, g.commutes]
    exact y.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountZ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.countZ :
    PropZ → CountZ := by
  intro hZ χ
  refine ⟨0, fun h _ t hB Ω _ _ _ l hl c e hl2 he0 het ψ hψ hc => ?_⟩
  obtain ⟨hnB, hdiv, rfl⟩ := hc
  have h5 : 5 ≤ l := by
    have h3 : l ≠ 3 := fun h3 => hnB (h3 ▸ Finset.mem_insert_self _ _)
    have h4 : l ≠ 4 := fun h4 => absurd (h4 ▸ hl.out) (by norm_num)
    have := hl.out.two_le
    omega
  have hev : Even e := by
    have h1 := (h.mem_X.1 hψ).2
    unfold PsiEven at h1
    rw [MulChar.one_apply (isUnit_one.neg)] at h1
    by_contra hne
    rw [(Nat.not_even_iff_odd.1 hne).neg_one_pow] at h1
    have h2 : (2 : c.O) = 0 := by linear_combination h1
    exact two_ne_zero h2
  have h2e : 2 ≤ e := by obtain ⟨k, rfl⟩ := hev; omega
  have hd : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext σ
    simp [Chr.dirG]
  have h0 : Vlen Ω c e (1 : DirichletCharacter c.O h.N) = 0 := by
    unfold Vlen
    rw [hd]
    exact le_antisymm ((Chr.V'_le_V l h.N e 1).trans (hZ Ω l c e h5 h2e hev hdiv).le) bot_le
  refine ⟨by rw [h0]; simp, ?_⟩
  simp [Vn, h0, Chr.nrm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orderOf_pow_coprime_parts {Γ : Type} [Group Γ] (x : Γ) (P C e : ℕ) (hn : orderOf x = P * C)
    (hP : 0 < P) (hC : 0 < C) (hco : P.Coprime C) (h1 : C ∣ e) (h2 : e ≡ 1 [MOD P]) :
    orderOf (x ^ e) = P ∧ orderOf (x * (x ^ e)⁻¹) = C := by
  have hcx : Commute (x ^ e) x := (Commute.refl x).pow_left e
  have hcomm : Commute (x ^ e) (x * (x ^ e)⁻¹) := hcx.mul_right (Commute.refl _).inv_right
  have hyz : x ^ e * (x * (x ^ e)⁻¹) = x := by
    rw [← mul_assoc, hcx.eq, mul_inv_cancel_right]
  have hoy : orderOf (x ^ e) ∣ P := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, orderOf_dvd_iff_pow_eq_one.mp]
    rw [hn, mul_comm P C]
    exact Nat.mul_dvd_mul_right h1 P
  have hoz : orderOf (x * (x ^ e)⁻¹) ∣ C := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(hcx.symm.inv_right).mul_pow, inv_pow, ← pow_mul]
    have : x ^ (e * C) = x ^ C := by
      rw [pow_eq_pow_iff_modEq, hn]
      have := Nat.ModEq.mul_right' C h2
      simpa using this
    rw [this, mul_inv_cancel]
  have hco' : (orderOf (x ^ e)).Coprime (orderOf (x * (x ^ e)⁻¹)) := Nat.Coprime.of_dvd hoy hoz hco
  have hprod : orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹) = P * C := by
    rw [← hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco', hyz, hn]
  obtain ⟨a, ha⟩ := hoy
  obtain ⟨b, hb⟩ := hoz
  have hab : a * b = 1 := by
    have : P * C * (a * b) = P * C * 1 := by
      calc P * C * (a * b)
          = (orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹)) * (a * b) := by rw [hprod]
        _ = (orderOf (x ^ e) * a) * (orderOf (x * (x ^ e)⁻¹) * b) := by ring
        _ = P * C * 1 := by rw [← ha, ← hb, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hP hC) this
  have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right hab
  have hb1 : b = 1 := Nat.eq_one_of_mul_eq_one_left hab
  refine ⟨?_, ?_⟩
  · rw [ha, ha1, mul_one]
  · rw [hb, hb1, mul_one]

theorem UpperTheory.V.HV.partOrd :
    ∀ (Γ : Type) [Group Γ] (l : ℕ), l.Prime → ∀ x : Γ, 0 < orderOf x →
      orderOf (lPart l x) = ordProj[l] (orderOf x) ∧ orderOf (lPrime l x) = ordCompl[l] (orderOf x) ∧ ¬ l ∣ orderOf (lPrime l x) ∧
      lPart l x ∈ Subgroup.zpowers x ∧ lPrime l x ∈ Subgroup.zpowers x ∧ (¬ l ∣ orderOf x → lPart l x = 1 ∧ lPrime l x = x) ∧
      ∀ a b : Γ, Commute a b → a * b = x → ¬ l ∣ orderOf a → (∃ s, b ^ l ^ s = 1) → lPrime l x = a ∧ lPart l x = b := by
  intro Γ _ l hl x hx
  have hn0 : orderOf x ≠ 0 := hx.ne'
  obtain ⟨P, hPd⟩ : ∃ P, P = ordProj[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = ordCompl[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, e = C ^ Nat.totient P := ⟨_, rfl⟩
  have hPC : P * C = orderOf x := by rw [hPd, hCd]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hP : 0 < P := by rw [hPd]; exact pow_pos hl.pos _
  have hC : 0 < C := by rw [hCd]; exact Nat.ordCompl_pos l hn0
  have hlC : ¬ l ∣ C := by rw [hCd]; exact Nat.not_dvd_ordCompl hl hn0
  have hcoC : l.Coprime C := (Nat.Prime.coprime_iff_not_dvd hl).2 hlC
  have hco : P.Coprime C := by rw [hPd]; exact hcoC.pow_left _
  have hlp : lPart l x = x ^ e := by rw [hed, hPd, hCd]; rfl
  have hlpr : lPrime l x = x * (lPart l x)⁻¹ := rfl
  have h1 : C ∣ e := by rw [hed]; exact dvd_pow_self _ (Nat.totient_pos.2 hP).ne'
  have h2 : e ≡ 1 [MOD P] := by rw [hed]; exact Nat.ModEq.pow_totient hco.symm
  obtain ⟨hA, hB⟩ := orderOf_pow_coprime_parts x P C e hPC.symm hP hC hco h1 h2
  rw [← hlp] at hA hB
  rw [← hlpr] at hB
  rw [← hCd, ← hPd]
  refine ⟨hA, hB, hB ▸ hlC, ?_, ?_, ?_, ?_⟩
  · rw [hlp]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  · rw [hlpr, hlp]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
  · intro hnd
    have hf : (orderOf x).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    have ho : orderOf (lPart l x) = 1 := by rw [hA, hPd, hf, pow_zero]
    have h1' := orderOf_eq_one_iff.mp ho
    exact ⟨h1', by rw [hlpr, h1', inv_one, mul_one]⟩
  · rintro a b hab habx hna ⟨s, hs⟩
    have hcoa : (orderOf a).Coprime l := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hna)
    have hob : orderOf b ∣ l ^ s := orderOf_dvd_of_pow_eq_one hs
    have hab' : (orderOf a).Coprime (orderOf b) := Nat.Coprime.coprime_dvd_right hob (hcoa.pow_right s)
    have hx' : orderOf x = orderOf a * orderOf b := by
      rw [← habx]; exact hab.orderOf_mul_eq_mul_orderOf_of_coprime hab'
    have hoaC : orderOf a ∣ C := by
      have hd : orderOf a ∣ P * C := by rw [hPC, hx']; exact dvd_mul_right _ _
      have hcP : (orderOf a).Coprime P := by rw [hPd]; exact hcoa.pow_right _
      exact hcP.dvd_of_dvd_mul_left hd
    have hobP : orderOf b ∣ P := by
      have hd : orderOf b ∣ P * C := by rw [hPC, hx']; exact dvd_mul_left _ _
      have hcC : (orderOf b).Coprime C := Nat.Coprime.coprime_dvd_left hob (hcoC.pow_left s)
      exact hcC.dvd_of_dvd_mul_right hd
    have hae : a ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp (hoaC.trans h1)
    have hbe : b ^ e = b := by
      have := (pow_eq_pow_iff_modEq (x := b) (n := e) (m := 1)).2 (h2.of_dvd hobP)
      simpa using this
    have hpart : lPart l x = b := by
      calc lPart l x = x ^ e := hlp
        _ = (a * b) ^ e := by rw [habx]
        _ = b := by rw [hab.mul_pow, hae, hbe, one_mul]
    refine ⟨?_, hpart⟩
    rw [hlpr, hpart, ← habx, mul_inv_cancel_right]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem index_inf_dvd_index_mul_index_of_commGroup {G : Type*} [CommGroup G] (A B : Subgroup G) :
    (A ⊓ B).index ∣ A.index * B.index := by
  have h := Subgroup.relIndex_inf_mul_relIndex A B ⊤
  rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
  rw [← h]
  exact Nat.mul_dvd_mul_right (Subgroup.relIndex_dvd_index_of_normal _ _) _

private theorem index_comap_dvd_index_of_commGroup {G G' : Type*} [CommGroup G] [Group G'] (A : Subgroup G) (f : G' →* G) :
    (A.comap f).index ∣ A.index := by
  rw [Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

private theorem index_range_sq_units_zmod_prime_dvd_two (p : ℕ) (hp : p.Prime) :
    ((powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range).index ∣ 2 := by
  haveI := Fact.mk hp
  set S := (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range
  haveI : IsCyclic ((ZMod p)ˣ ⧸ S) :=
    isCyclic_of_surjective (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
  have hcard : Nat.card ((ZMod p)ˣ ⧸ S) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
  exact hcard

private theorem index_zpowers_neg_one_units_zmod_two_pow_dvd (e : ℕ) :
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ)).index ∣ 2 ^ e := by
  have h4 : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : Fact (1 < 2 ^ (e + 2)) := ⟨by omega⟩
  have h := Subgroup.index_mul_card (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one,
    ZMod.ringChar_zmod_n, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_two, if_neg (by omega)] at h
  have h' : 2 ^ (e + 1) * (2 - 1) = 2 ^ e * 2 := by ring
  rw [h'] at h
  rw [Nat.eq_of_mul_eq_mul_right (by norm_num) h]

private theorem index_ker_toUnitHom_dvd_orderOf_dirichletCharacter (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) :
    (MulChar.toUnitHom χ).ker.index ∣ orderOf χ := by
  rw [Subgroup.index_ker]
  haveI : IsCyclic (MulChar.toUnitHom χ).range := inferInstance
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  obtain ⟨_, u, rfl⟩ := x
  apply Subtype.ext
  apply Units.ext
  have ho : orderOf χ ≠ 0 := (orderOf_pos χ).ne'
  simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom,
    OneMemClass.coe_one, Units.val_one]
  rw [← MulChar.pow_apply' χ ho, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem orderOf_dirichletCharacter_le_level (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) : orderOf χ ≤ n := by
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have h1 : χ ^ n.totient = 1 := by
    ext u
    rw [MulChar.pow_apply' χ hpos.ne', ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient,
      Units.val_one, map_one, MulChar.one_apply_coe]
  exact (Nat.le_of_dvd hpos (orderOf_dvd_of_pow_eq_one h1)).trans (Nat.totient_le n)

theorem UpperTheory.V.HV.hostIndex :
    ∀ h : Host, h.H.index ∣ 2 ^ (h.ex + 2) * h.o ∧ h.H.index ≤ h.N ∧ 16 ∣ h.N ∧ 0 < h.o ∧ h.o ≤ h.q ∧
      (∀ p, p.Prime → (p ∣ h.N ↔ p = 2 ∨ p ∣ h.q ∨ p = h.q1 ∨ p = h.d)) ∧
      (∀ p, p.Prime → p ≠ 2 → p ≠ h.q1 → p ≠ h.d → ordProj[p] h.N = ordProj[p] h.q) ∧ ordProj[h.q1] h.N = h.q1 ∧ ordProj[h.d] h.N = h.d ∧
      ∀ u : (ZMod h.N)ˣ, u ^ (2 ^ (h.ex + 1) * h.o) ∈ h.H := by
  intro h
  obtain ⟨hq1, hq1m, hd, hdm, hcop⟩ := h.pair
  haveI := h.chi.ne
  have hq0 : h.q ≠ 0 := NeZero.ne _
  have hq12 : h.q1 ≠ 2 := by intro e; omega
  have hd2 : h.d ≠ 2 := by intro e; omega
  have hq1d : h.q1 ≠ h.d := by intro e; omega
  have cq1 : ¬ h.q1 ∣ h.q := fun hdv => hq1.one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hcop) hdv)
  have cd : ¬ h.d ∣ h.q := fun hdv => hd.one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop) hdv)
  have hN : h.N = (2 ^ (h.ex + 2)).lcm h.q * (h.q1 * h.d) := rfl
  have hN0 : h.N ≠ 0 := by
    rw [hN]
    exact Nat.mul_ne_zero (Nat.lcm_ne_zero (by positivity) hq0) (Nat.mul_ne_zero hq1.ne_zero hd.ne_zero)
  haveI : NeZero h.N := ⟨hN0⟩
  have hfac : ∀ p, p.Prime → h.N.factorization p =
      max ((h.ex + 2) * (if p = 2 then 1 else 0)) (h.q.factorization p) +
        ((if p = h.q1 then 1 else 0) + (if p = h.d then 1 else 0)) := by
    intro p hp
    rw [hN, Nat.factorization_mul (Nat.lcm_ne_zero (by positivity) hq0)
        (Nat.mul_ne_zero hq1.ne_zero hd.ne_zero),
      Nat.factorization_lcm (by positivity) hq0, Nat.factorization_mul hq1.ne_zero hd.ne_zero,
      Nat.factorization_pow, Nat.prime_two.factorization, hq1.factorization, hd.factorization]
    simp [Finsupp.single_apply, eq_comm]
    split_ifs <;> simp
  have fq1 : h.q.factorization h.q1 = 0 := Nat.factorization_eq_zero_of_not_dvd cq1
  have fd : h.q.factorization h.d = 0 := Nat.factorization_eq_zero_of_not_dvd cd
  have hdiv : h.H.index ∣ 2 ^ (h.ex + 2) * h.o := by
    have i1 := index_comap_dvd_index_of_commGroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (h.ex + 2)))ˣ))
      (ZMod.unitsMap (Host.two_pow_dvd h))
    have i2 := index_comap_dvd_index_of_commGroup (MulChar.toUnitHom h.chi.χ).ker (ZMod.unitsMap (Host.q_dvd h))
    have i3 := index_comap_dvd_index_of_commGroup (powMonoidHom 2 : (ZMod h.q1)ˣ →* (ZMod h.q1)ˣ).range
      (ZMod.unitsMap (Host.host_q1_dvd_N h))
    have i4 := index_comap_dvd_index_of_commGroup (powMonoidHom 2 : (ZMod h.d)ˣ →* (ZMod h.d)ˣ).range
      (ZMod.unitsMap (Host.d_dvd h))
    have j1 := i1.trans (index_zpowers_neg_one_units_zmod_two_pow_dvd h.ex)
    have j2 := i2.trans (index_ker_toUnitHom_dvd_orderOf_dirichletCharacter h.chi.N h.chi.χ)
    have j3 := i3.trans (index_range_sq_units_zmod_prime_dvd_two h.q1 hq1)
    have j4 := i4.trans (index_range_sq_units_zmod_prime_dvd_two h.d hd)
    have k := ((((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul_right
      ((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul_right
        ((index_inf_dvd_index_mul_index_of_commGroup _ _).trans (Nat.mul_dvd_mul j1 j2)) _)) _))).trans
      (Nat.mul_dvd_mul (Nat.mul_dvd_mul (dvd_refl _) j3) j4))
    have e : 2 ^ h.ex * orderOf h.chi.χ * 2 * 2 = 2 ^ (h.ex + 2) * h.o := by
      simp only [Host.o, ordC]
      ring
    rw [← e]
    exact k
  refine ⟨hdiv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : h.H.index ∣ h.N.totient := by
      have := Subgroup.index_dvd_card h.H
      rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at this
    exact (Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)) hc).trans (Nat.totient_le _)
  · rw [hN]
    exact (Nat.pow_dvd_pow 2 (by have := h.two_le; omega : 4 ≤ h.ex + 2)).trans
      ((Nat.dvd_lcm_left _ _).trans (dvd_mul_right _ _))
  · exact orderOf_pos _
  · exact orderOf_dirichletCharacter_le_level _ _
  · intro p hp
    rw [hp.dvd_iff_one_le_factorization hN0, hp.dvd_iff_one_le_factorization hq0, hfac p hp]
    by_cases e2 : p = 2 <;> by_cases e3 : p = h.q1 <;> by_cases e4 : p = h.d <;>
      simp [e2, e3, e4] <;> omega
  · intro p hp h2 h3 h4
    rw [hfac p hp]
    simp [h2, h3, h4]
  · rw [hfac _ hq1, fq1]
    simp [hq12, hq1d]
  · rw [hfac _ hd, fd]
    simp [hd2, hq1d.symm]
  · intro u
    have sq : ∀ (n : ℕ) (w : (ZMod n)ˣ),
        w ^ (2 ^ (h.ex + 1) * h.o) ∈ (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
      intro n w
      refine ⟨w ^ (2 ^ h.ex * h.o), ?_⟩
      rw [powMonoidHom_apply, ← pow_mul]
      congr 1
      ring
    simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap, map_pow]
    refine ⟨⟨⟨?_, ?_⟩, sq _ _⟩, sq _ _⟩
    · have ht : (2 ^ (h.ex + 2)).totient = 2 ^ (h.ex + 1) := by
        rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp
      rw [pow_mul, ← ht, ZMod.pow_totient, one_pow]
      exact Subgroup.one_mem _
    · rw [MonoidHom.mem_ker, map_pow]
      have h1 : (MulChar.toUnitHom h.chi.χ) (ZMod.unitsMap (Host.q_dvd h) u) ^ h.o = 1 := by
        apply Units.ext
        have ho : orderOf h.chi.χ ≠ 0 := (orderOf_pos _).ne'
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, Units.val_one]
        simp only [Host.o, ordC]
        rw [← MulChar.pow_apply' _ ho, pow_orderOf_eq_one, MulChar.one_apply_coe]
      rw [mul_comm, pow_mul, h1, one_pow]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.Top

namespace UpperTheory.V.HV

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)

def Congr (a b : G ℚ Ω →* c.Oˣ) : Prop := ∀ σ, ((a σ : c.Oˣ) : c.O) - ((b σ : c.Oˣ) : c.O) ∈ IsLocalRing.maximalIdeal c.O

def IsOmT (w : G ℚ Ω →* c.Oˣ) : Prop :=
  w ^ (l - 1) = 1 ∧ Congr c w (UpperTheory.V.Base.chiO (k := ℚ) (Ω := Ω) l c.O)

structure GDlit (K : Type) [Field K] [NumberField K] [Algebra K Ω] (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N)
    (w η : G ℚ Ω →* c.Oˣ) (a : ℕ) : Prop where
  om : IsOmT c w
  eta_ker : η.ker = galOf ℚ K Ω
  l_odd : l ≠ 2
  e_pos : 1 ≤ e
  N_even : Even N
  ord : ¬ l ∣ orderOf (Chr.dirG ℚ Ω ψ)
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ σ ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ σ = w σ ^ a
  a_lt : a < l - 1
  two_a : l - 1 ∣ 2 * a
  par : ∀ σ : G ℚ Ω, IsCC σ → UpperTheory.V.Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1
  quad : Module.finrank ℚ K = 2
  imag : IsTotallyComplex K
  l_cop : ¬ l ∣ (discr K).natAbs * classNumber K
  cop : (discr K).natAbs.Coprime N
  eta : ∀ i j : ℕ, ¬ Congr c η (w ^ i * (Chr.dirG ℚ Ω ψ * (w ^ a)⁻¹) ^ j)
  gen : ¬ l - 1 ∣ 2 * (e + a)

end UpperTheory.V.HV

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompOrd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem co_proj_eq_one {N : ℕ} (r : ℕ) (hr : r.Prime) (u : (ZMod N)ˣ)
    (h : ((ordProj[r] N : ℕ) : ZMod N) ∣ (u : ZMod N) - 1) : proj r N u = 1 := by
  obtain ⟨t, ht⟩ := h
  have hpos : 0 < Nat.totient (ordProj[r] N) := by
    rw [Nat.totient_pos]
    exact pow_pos hr.pos _
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have h0 : idem r N * ((ordProj[r] N : ℕ) : ZMod N) = 0 := by
    unfold idem
    rw [hk, ← Nat.cast_mul, pow_succ, mul_assoc, mul_comm (ordCompl[r] N),
      Nat.ordProj_mul_ordCompl_eq_self, Nat.cast_mul, ZMod.natCast_self, mul_zero]
  ext
  change idem r N * (u : ZMod N) + (1 - idem r N) = 1
  linear_combination idem r N * ht + t * h0

private theorem co_dvd_of_unitsMap {N d : ℕ} [NeZero N] (hd : d ∣ N) (u : (ZMod N)ˣ)
    (h : ZMod.unitsMap hd u = 1) : ((d : ℕ) : ZMod N) ∣ (u : ZMod N) - 1 := by
  rw [Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
      Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
  obtain ⟨t, ht⟩ := h.symm.dvd
  refine ⟨(t : ZMod N), ?_⟩
  have := congrArg (Int.cast : ℤ → ZMod N) ht
  simpa using this

private theorem co_toUnitHom {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u) := by
  simp [comp]

private theorem co_pow_toUnitHom {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (u : (ZMod N)ˣ) :
    (χ ^ k).toUnitHom u = χ.toUnitHom u ^ k := by
  ext
  simp [MulChar.pow_apply_coe]

private theorem co_pow_eq_one_iff {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) :
    χ ^ k = 1 ↔ ∀ u, χ.toUnitHom u ^ k = 1 := by
  simp_rw [← co_pow_toUnitHom]
  constructor
  · intro h u
    rw [h]
    ext
    simp
  · intro h
    ext u
    simpa using congrArg Units.val (h u)

private theorem co_ord_dvd {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) : orderOf (comp r χ) ∣ Nat.totient (ordProj[r] N) := by
  rw [orderOf_dvd_iff_pow_eq_one, co_pow_eq_one_iff]
  intro u
  have : NeZero (ordProj[r] N) := ⟨(pow_pos hr.pos _).ne'⟩
  rw [← map_pow, co_toUnitHom, co_proj_eq_one r hr, map_one]
  apply co_dvd_of_unitsMap (Nat.ordProj_dvd N r)
  rw [map_pow, ZMod.pow_totient]

private theorem co_tame {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (r : ℕ)
    (hr : r.Prime) (h : ¬ r ∣ orderOf (comp r χ)) :
    orderOf (comp r χ) ∣ r - 1 ∧ (comp r χ).conductor ∣ r := by
  have hc : (orderOf (comp r χ)).Coprime r := ((Nat.Prime.coprime_iff_not_dvd hr).2 h).symm
  have h1 := co_ord_dvd χ r hr
  by_cases hN : r ∣ N
  · have hpos : 0 < N.factorization r := hr.factorization_pos_of_dvd (NeZero.ne N) hN
    rw [Nat.totient_prime_pow hr hpos] at h1
    refine ⟨(hc.pow_right _).dvd_of_dvd_mul_left h1, ?_⟩
    apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
    rw [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.factorsThrough_iff_ker_unitsMap hN]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h2 := dvd_sub_pow_of_dvd_sub (co_dvd_of_unitsMap hN u hu) (N.factorization r)
    have h3 : (comp r χ).toUnitHom u ^ (r ^ N.factorization r) = 1 := by
      rw [← map_pow, co_toUnitHom, co_proj_eq_one r hr, map_one]
      rw [one_pow] at h2
      refine dvd_trans ?_ (by simpa using h2)
      rw [Nat.cast_pow]
      exact pow_dvd_pow _ (Nat.le_succ _)
    have h4 := (co_pow_eq_one_iff (comp r χ) _).1 (pow_orderOf_eq_one _) u
    have h5 := pow_gcd_eq_one.2 ⟨h4, h3⟩
    rwa [hc.pow_right _, pow_one] at h5
  · rw [Nat.factorization_eq_zero_of_not_dvd hN, pow_zero, Nat.totient_one, Nat.dvd_one] at h1
    refine ⟨by rw [h1]; exact one_dvd _, ?_⟩
    rw [orderOf_eq_one_iff] at h1
    rw [h1, DirichletCharacter.conductor_one]
    exact one_dvd _

theorem UpperTheory.V.HV.compOrd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (r : ℕ), r.Prime →
      orderOf (comp r χ) ∣ Nat.totient (ordProj[r] N) ∧ (∃ k, orderOf (comp 2 χ) = 2 ^ k) ∧
      (¬ r ∣ orderOf (comp r χ) → orderOf (comp r χ) ∣ r - 1 ∧ (comp r χ).conductor ∣ r) ∧
      ∀ l s : ℕ, l.Prime → l ≠ r → χ ^ l ^ s = 1 → comp r χ ≠ 1 → r ≡ 1 [MOD l] ∧ (comp r χ).conductor = r := by
  intro O _ _ N _ χ r hr
  refine ⟨co_ord_dvd χ r hr, ?_, co_tame χ r hr, ?_⟩
  · have h1 := co_ord_dvd χ 2 Nat.prime_two
    have h2 : Nat.totient (ordProj[2] N) ∣ 2 ^ (N.factorization 2 - 1) := by
      rcases Nat.eq_zero_or_pos (N.factorization 2) with h | h
      · simp [h]
      · rw [Nat.totient_prime_pow Nat.prime_two h]; simp
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (h1.trans h2)
    exact ⟨k, hk⟩
  · intro l s hl hlr hχ hne
    have h1 : orderOf (comp r χ) ∣ l ^ s := by
      rw [orderOf_dvd_iff_pow_eq_one, co_pow_eq_one_iff]
      intro u
      rw [co_toUnitHom]
      exact (co_pow_eq_one_iff χ _).1 hχ _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).1 h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.1 (by simpa using hk))
    have h2 : ¬ r ∣ orderOf (comp r χ) := by
      rw [hk]
      intro h
      exact hlr ((Nat.prime_dvd_prime_iff_eq hr hl).1 (hr.dvd_of_dvd_pow h)).symm
    obtain ⟨h3, h4⟩ := co_tame χ r hr h2
    refine ⟨?_, ?_⟩
    · rw [hk] at h3
      exact ((Nat.modEq_iff_dvd' hr.one_le).2 ((dvd_pow_self l hk0).trans h3)).symm
    · rcases (Nat.dvd_prime hr).1 h4 with h | h
      · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h) hne
      · exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

open Polynomial in
private theorem splitting_field_iso_quadratic (p : ℕ) (hp : 0 < p) (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = -(p : K)) (L : Type) [Field L] [NumberField L]
    [hL : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Nonempty (L ≃ₐ[ℚ] K) := by
  classical
  set f : ℚ[X] := X ^ 2 + C (p : ℚ) with hf
  have hsK : (f.map (algebraMap ℚ K)).Splits := by
    have hfac : f.map (algebraMap ℚ K) = (X + C δ) * (X + C (-δ)) := by
      have hpK : (p : K) = -(δ ^ 2) := by rw [hδ]; ring
      rw [hf, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        map_natCast, hpK]
      simp only [map_neg, map_pow]
      ring
    rw [hfac]
    exact (Splits.X_add_C _).mul (Splits.X_add_C _)
  let φ := IsSplittingField.lift L f hsK
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hLK : Module.finrank ℚ L ≤ 2 :=
    hK ▸ LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
  have hL1 : Module.finrank ℚ L ≠ 1 := by
    intro h1
    have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one (F := ℚ) (E := L) h1
    have hsL := IsSplittingField.splits L f
    have hdeg : (f.map (algebraMap ℚ L)).degree ≠ 0 := by
      rw [Polynomial.degree_map, hf, Polynomial.degree_X_pow_add_C (by norm_num)]
      norm_num
    obtain ⟨r, hr⟩ := hsL.exists_eval_eq_zero hdeg
    have hrm : r ∈ (⊥ : Subalgebra ℚ L) := hbt ▸ Algebra.mem_top
    obtain ⟨q, rfl⟩ := Algebra.mem_bot.mp hrm
    have hq : algebraMap ℚ L (q ^ 2 + p) = 0 := by
      simpa [hf, Polynomial.eval_map] using hr
    have hq0 : q ^ 2 + (p : ℚ) = 0 := (algebraMap ℚ L).injective (by rw [hq, map_zero])
    have hpq : (0 : ℚ) < q ^ 2 + p := by
      have : (0 : ℚ) < p := by exact_mod_cast hp
      positivity
    linarith
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have h2 : Module.finrank ℚ L = 2 := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (h2.trans hK.symm)).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem UpperTheory.V.HV.kstar :
    ∀ p : ℕ, p.Prime → p % 4 = 3 → discr (Kstar p) = -(p : ℤ) ∧ IsTotallyComplex (Kstar p) ∧ Module.finrank ℚ (Kstar p) = 2 ∧ ∃ s : Kstar p, s ^ 2 = -(p : Kstar p) := by
  intro p hp h3
  obtain ⟨K, _, _, hK2, hd⟩ := KStar.Consta.exists_quadField hp h3
  obtain ⟨⟨δ, hδ⟩, -⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hK2 hp.ne_zero hd
  haveI : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
    have h := Polynomial.IsSplittingField.splittingField (K := ℚ) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))
    have h' : Polynomial.IsSplittingField ℚ (Polynomial.SplittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)))
        (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
      convert h
    exact h'
  obtain ⟨e⟩ := splitting_field_iso_quadratic p hp.pos K hK2 δ hδ (Kstar p)
  have hfr : Module.finrank ℚ (Kstar p) = 2 := e.toLinearEquiv.finrank_eq.trans hK2
  have hdisc : discr (Kstar p) = -(p : ℤ) := by
    rw [NumberField.discr_eq_discr_of_algEquiv (Kstar p) e, hd]
  obtain ⟨hs, htc⟩ := KStar.Choice.exists_sq_eq_neg_of_discr hfr hp.ne_zero hdisc
  exact ⟨hdisc, htc, hfr, hs⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem projA {N : ℕ} (r d : ℕ) (h : d ∣ N) (hd : d ∣ ordProj[r] N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h (proj r N u) = ZMod.unitsMap h u := by
  have h1 : ZMod.castHom h (ZMod d) (idem r N) = 1 := by
    unfold idem
    rw [map_natCast, ← Nat.cast_one (R := ZMod d), ZMod.natCast_eq_natCast_iff]
    exact (Nat.ModEq.pow_totient (coprime_ordProj_ordCompl r N).symm).of_dvd hd
  apply Units.ext
  show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = ZMod.castHom h (ZMod d) u
  rw [map_add (f := _), map_mul, map_sub, h1, map_one]
  ring

private theorem projB {N : ℕ} (r d : ℕ) (hr : r.Prime) (h : d ∣ N) (hd : d ∣ ordCompl[r] N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h (proj r N u) = 1 := by
  have h1 : ZMod.castHom h (ZMod d) (idem r N) = 0 := by
    unfold idem
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_pow hd (Nat.totient_pos.2 (pow_pos hr.pos _)).ne'
  apply Units.ext
  show ZMod.castHom h (ZMod d) (idem r N * u + (1 - idem r N)) = 1
  rw [map_add (f := _), map_mul, map_sub, h1, map_one]
  ring

private theorem crtExt {N : ℕ} [NeZero N] (r : ℕ) {u v : (ZMod N)ˣ}
    (h1 : ZMod.unitsMap (Nat.ordProj_dvd N r) u = ZMod.unitsMap (Nat.ordProj_dvd N r) v)
    (h2 : ZMod.unitsMap (Nat.ordCompl_dvd N r) u = ZMod.unitsMap (Nat.ordCompl_dvd N r) v) : u = v := by
  have key : ∀ (d : ℕ) (h : d ∣ N), ZMod.unitsMap h u = ZMod.unitsMap h v →
      (u : ZMod N).val ≡ (v : ZMod N).val [MOD d] := by
    intro d h e
    have e' : ZMod.castHom h (ZMod d) (u : ZMod N) = ZMod.castHom h (ZMod d) (v : ZMod N) := congrArg Units.val e
    rw [← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N), map_natCast, map_natCast] at e'
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 e'
  have h3 := (Nat.modEq_and_modEq_iff_modEq_mul (coprime_ordProj_ordCompl r N)).1 ⟨key _ _ h1, key _ _ h2⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h3
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (u : ZMod N), ← ZMod.natCast_zmod_val (v : ZMod N)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

private theorem dvdCompl {N : ℕ} [NeZero N] {r d : ℕ} (hr : r.Prime) (h : d ∣ N) (hd : ¬ r ∣ d) : d ∣ ordCompl[r] N := by
  have hc : d.Coprime (ordProj[r] N) := (((Nat.Prime.coprime_iff_not_dvd hr).2 hd).symm).pow_right _
  apply hc.dvd_of_dvd_mul_left
  rwa [Nat.ordProj_mul_ordCompl_eq_self]

private theorem mapMap {N M d : ℕ} (h1 : d ∣ M) (h2 : M ∣ N) (u : (ZMod N)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← ZMod.unitsMap_comp h1 h2]; rfl

theorem UpperTheory.V.HV.projFacts :
    ∀ (N : ℕ) [NeZero N] (r : ℕ), r.Prime →
      (∀ u, ZMod.unitsMap (Nat.ordProj_dvd N r) (proj r N u) = ZMod.unitsMap (Nat.ordProj_dvd N r) u) ∧
      (∀ u, ZMod.unitsMap (Nat.ordCompl_dvd N r) (proj r N u) = 1) ∧ (∀ u, proj r N (proj r N u) = proj r N u) ∧
      (∀ r', r'.Prime → r' ≠ r → ∀ u, proj r N (proj r' N u) = 1) ∧ (¬ r ∣ N → ∀ u, proj r N u = 1) ∧
      (proj r N).range = (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker ∧ (proj r N).ker = (ZMod.unitsMap (Nat.ordProj_dvd N r)).ker ∧
      (∀ (M : ℕ) (h : M ∣ N), ¬ r ∣ M → ∀ u, ZMod.unitsMap h (proj r N u) = 1) ∧
      ∀ (M : ℕ) (h : M ∣ N) u, ZMod.unitsMap h (proj r N u) = proj r M (ZMod.unitsMap h u) := by
  intro N _ r hr
  have hA := projA r _ (Nat.ordProj_dvd N r) dvd_rfl
  have hB := projB r _ hr (Nat.ordCompl_dvd N r) dvd_rfl
  have hM : ∀ (r : ℕ), r.Prime → ∀ (M : ℕ) (h : M ∣ N), ¬ r ∣ M → ∀ u, ZMod.unitsMap h (proj r N u) = 1 :=
    fun r hr M h hM u => projB r M hr h (dvdCompl hr h hM) u
  refine ⟨hA, hB, fun u => crtExt r (hA _) (by rw [hB, hB]), fun r' hr' hne u => ?_, fun hN u => ?_, ?_, ?_,
    hM r hr, fun M h u => ?_⟩
  · refine crtExt r ?_ (by rw [hB, map_one])
    rw [hA, map_one]
    exact hM r' hr' _ _ (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hr' hr).1 (hr'.dvd_of_dvd_pow hd))) u
  · have := hM r hr N dvd_rfl hN u
    rwa [ZMod.unitsMap_self] at this
  · ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact hB v
    · intro hu
      exact ⟨u, crtExt r (hA u) ((hB u).trans (MonoidHom.mem_ker.1 hu).symm)⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hu
      rw [← hA, hu, map_one]
    · intro hu
      exact crtExt r (by rw [hA, hu, map_one]) (by rw [hB, map_one])
  · haveI : NeZero M := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) h⟩
    refine crtExt r ?_ ?_
    · rw [projA r _ _ dvd_rfl, mapMap, mapMap]
      exact projA r _ _ (Nat.ordProj_dvd_ordProj_of_dvd (NeZero.ne N) h r) u
    · rw [projB r _ hr _ dvd_rfl, mapMap]
      exact projB r _ hr _ (Nat.ordCompl_dvd_ordCompl_of_dvd h r) u
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PZeroLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.pZeroLe :
    ∀ m : ℕ, 0 < m → (pZero m).Prime ∧ 5 ≤ pZero m ∧ ¬ pZero m ∣ m ∧ pZero m ≤ 2 * m + 10 := by
  intro m hm
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 5) (by omega)
  have hmem : p ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} :=
    ⟨hp, by omega, fun h => by have := Nat.le_of_dvd hm h; omega⟩
  have h3 : UpperTheory.V.HV.pZero m ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} := Nat.sInf_mem ⟨p, hmem⟩
  have h4 : UpperTheory.V.HV.pZero m ≤ p := Nat.sInf_le hmem
  exact ⟨h3.1, h3.2.1, h3.2.2, by omega⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostLevel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem coe_unitsMap {g N : ℕ} [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g) = (((u : ZMod N).val : ℕ) : ZMod g) := by
  show ZMod.castHom h (ZMod g) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem pm_iff {n : ℕ} (v : (ZMod n)ˣ) (a : ℕ) (hv : (v : ZMod n) = (a : ZMod n)) :
    (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) := by
  have key : v ∈ Subgroup.zpowers (-1 : (ZMod n)ˣ) ↔ v = 1 ∨ v = -1 := by
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd k with he | ho
      · left
        exact he.neg_one_zpow
      · right
        exact ho.neg_one_zpow
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  rw [key, ← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [← hv]
  simp only [Units.ext_iff, Units.val_one, Units.val_neg, eq_neg_iff_add_eq_zero]

private theorem jac_iff {p : ℕ} (hp : p.Prime) (v : (ZMod p)ˣ) (a : ℕ) (hv : (v : ZMod p) = (a : ZMod p)) :
    jacobiSym (a : ℤ) p = 1 ↔ v ∈ (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
  haveI := Fact.mk hp
  have ha : ((a : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    rw [← hv]
    exact v.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p ha]
  push_cast
  rw [← hv]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← hw]
    simp [sq]

theorem UpperTheory.V.HV.hostLevel :
    ∀ (h : Host) (E : Type) [Field E] [NumberField E], IsChiField h.chi h.ex h.q1 h.d E → Chr.HasLevel E h.N h.H := by
  intro h E _ _ hchi
  have hc := (isCompField_ofChar h.chi h.ex h.q1 h.d E).mpr hchi
  obtain ⟨H', hlev, hmem⟩ := Chr.abLevel.2 (AbF.ofChar h.chi) h.ex h.q1 h.d E hc h.N h.two_pow_dvd h.q_dvd h.host_q1_dvd_N h.d_dvd
  have hq1 : h.q1.Prime := h.pair.1
  have hd : h.d.Prime := h.pair.2.2.1
  convert hlev using 1
  ext u
  have hu : (u : ZMod h.N) = (((u : ZMod h.N).val : ℕ) : ZMod h.N) := (ZMod.natCast_zmod_val _).symm
  rw [hmem u _ hu]
  simp only [Host.H, Subgroup.mem_inf, Subgroup.mem_comap]
  rw [← pm_iff (ZMod.unitsMap h.two_pow_dvd u) _ (coe_unitsMap _ u),
    ← jac_iff hq1 (ZMod.unitsMap h.host_q1_dvd_N u) _ (coe_unitsMap _ u),
    ← jac_iff hd (ZMod.unitsMap h.d_dvd u) _ (coe_unitsMap _ u)]
  have hk : (ZMod.unitsMap h.q_dvd u) ∈ (MulChar.toUnitHom h.chi.χ).ker ↔
      (AbF.ofChar h.chi).ker ((u : ZMod h.N).val) := by
    constructor
    · intro hv
      exact ⟨_, hv, coe_unitsMap _ u⟩
    · rintro ⟨w, hw, hwa⟩
      have hweq : w = ZMod.unitsMap h.q_dvd u := Units.ext (hwa.trans (coe_unitsMap _ u).symm)
      rwa [← hweq]
  rw [hk]
  tauto
end
