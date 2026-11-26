module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
noncomputable section

open IsLocalRing UpperTheory.V.HV

namespace UpperTheory.V.UnitaryThreeInertia

def Frame.shaLen {O : Type} [CommRing O] [IsLocalRing O] {G Γ : Type} [Group G] [Group Γ] {ι : Type}
    (F : Frame O G Γ ι) [TopologicalSpace Γ] (a : O) : ℕ∞ := Module.length O (F.ShaO a)

instance Coef.isLocalRing {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalRing c.O := c.dvr.toIsLocalRing

instance Coef.complete {l : ℕ} [Fact l.Prime] (c : Coef l) : IsAdicComplete (maximalIdeal c.O) c.O :=
  (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1

instance Coef.finite_residue {l : ℕ} [Fact l.Prime] (c : Coef l) : Finite (ResidueField c.O) := by
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[l])

class CFin (O : Type) [CommRing O] [IsLocalRing O] : Prop where
  complete : IsAdicComplete (maximalIdeal O) O
  fin : Finite (ResidueField O)

attribute [instance] CFin.complete CFin.fin

end UpperTheory.V.UnitaryThreeInertia

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalEulerCharacteristicRationalsOddPrime
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CardGlobalEulerCharacteristicRationals
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

theorem UpperTheory.card_global_euler_characteristic_rationals :
    GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (ρ : Representation (ZMod (l ^ 1)) (Gam Ω S) M),
            ContainsAbove S l → ContAction ρ → ∀ σ : Formalism.ConjugateSelfDual.G ℚ Ω, IsCC σ →
            Nat.card (H1 ρ) * Nat.card {m : M // ρ (toGS Ω _ σ) m = m} = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M := by
  intro hG Ω _ _ _ l _ _ M _ _ _ _ _ S ρ hS hρ σ hσ
  have h := hG ℚ Ω l 1 M S ρ Nat.one_pos hS hρ (fun _ => σ) (by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩)
  have hc : NumberField.InfinitePlace.nrComplexPlaces ℚ = 0 :=
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  simp only [archH0Card, hc, pow_zero, mul_one, Module.finrank_self, pow_one] at h
  rw [Finset.prod_eq_single_of_mem Rat.infinitePlace
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Rat.isReal_infinitePlace)
    (fun b _ hb => absurd (Subsingleton.elim b _) hb)] at h
  exact h.symm
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

theorem UpperTheory.global_euler_characteristic_rationals_odd_prime :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (ρ : Representation k (Gam Ω S) M),
        ContainsAbove S l → ContAction ρ → ∀ σ : Formalism.ConjugateSelfDual.G ℚ Ω, IsCC σ →
        Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
          finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - LinearMap.id)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
  intro hF hE Ω _ _ _ l _ hl k M _ _ _ _ _ _ _ _ S ρ hS hρ σ hσ
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (l ^ 1)) M := Module.compHom _ (ZMod.castHom (dvd_refl _) k)
  let ρ' : Representation (ZMod (l ^ 1)) (Gam Ω S) M :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add (ρ g)
          map_smul' := fun c m => map_smul (ρ g) (ZMod.castHom (dvd_refl _) k c) m }
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have ec : LinearMap.ker (ρ (toGS Ω _ σ) - LinearMap.id) ≃ {m : M // ρ' (toGS Ω _ σ) m = m} :=
    Equiv.subtypeEquivRight fun m => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact Iff.rfl
  obtain ⟨-, f1, f2, -⟩ := hF ℚ Ω l 1 M S ρ' one_pos hS hρ
  have h := UpperTheory.card_global_euler_characteristic_rationals hE Ω l hl M S ρ' hS hρ σ hσ
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  haveI : Module.Finite k M := Module.Finite.of_finite
  haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨inferInstance, inferInstance, ?_⟩
  apply Nat.pow_right_injective hk
  beta_reduce
  rw [pow_add, pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
    ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
    Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2, Nat.card_congr ec]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalCohomologyFiniteSet
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private theorem twDual_inv_eq_zero {Γ k M : Type} [Group Γ] [Field k] [AddCommGroup M] [Module k M]
    (N : ℕ) [Module (ZMod N) M] (μ : Γ →* (ZMod N)ˣ) (ρ : Representation k Γ M)
    (g : Γ) (a : k) (n : ℕ) (hg : ∀ m, ρ g m = a • m) (hn : (n : ZMod N) = μ g) (han : a ≠ (n : k))
    (y : H0 (twDual μ (GlobalTheory.Published.zmodRep N ρ))) : y = 0 := by
  obtain ⟨φ, hφ⟩ := y
  apply Subtype.ext
  have h1 : twDual μ (GlobalTheory.Published.zmodRep N ρ) g φ = φ := hφ _
  show φ = 0
  apply LinearMap.ext
  intro x
  set m : M := (a - (n : k))⁻¹ • x with hm
  have hx : x = a • m - n • m := by
    rw [← Nat.cast_smul_eq_nsmul k, ← sub_smul, hm, smul_smul,
      mul_inv_cancel₀ (sub_ne_zero.2 han), one_smul]
  have h3 := congrArg (fun ψ : TDual (ZMod N) M => ψ (GlobalTheory.Published.zmodRep N ρ g m)) h1
  simp only [twDual_apply] at h3
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    ← hn] at h3
  have h4 : GlobalTheory.Published.zmodRep N ρ g m = a • m := hg m
  rw [h4] at h3
  show φ x = 0
  rw [hx]
  refine (LinearMap.map_sub (φ : Module.Dual (ZMod N) M) _ _).trans (sub_eq_zero.mpr ?_)
  refine h3.symm.trans ?_
  rw [← nsmul_eq_mul]
  exact (map_nsmul (F := Module.Dual (ZMod N) M) φ n m).symm

theorem UpperTheory.global_cohomology_finite_set :
    GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (A : S → ValuationSubring Ω) (ρ : Representation k (Gam Ω S) M),
                 ContainsAbove S l → (∀ v, Formalism.ConjugateSelfDual.IsPlaceOver (A v) v.1) → ContAction ρ →
                 (∃ (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (a : k) (n : ℕ), (∀ m, ρ (toGS Ω _ σ) m = a • m) ∧ (n : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) ∧ a ≠ (n : k)) →
                 ∀ κ : ∀ v : S, Z2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M), ∃ z : Z2 ρ, ∀ v : S,
                   (fun p : Dec (F := ℚ) (A v) × Dec (F := ℚ) (A v) => z.1 (toGS Ω _ p.1.1, toGS Ω _ p.2.1)) - (κ v).1 ∈
                     B2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M) := by
  intro hPT Ω _ _ _ l _ hl k M _ _ _ _ _ _ _ _ S A ρ hS hA hρ hσ κ
  obtain ⟨σ, a, n, hσa, hn, han⟩ := hσ
  have hM : ∀ m : M, (l ^ 1) • m = 0 := fun m => by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := 1) hS
  obtain ⟨inv, -, h⟩ := hPT ℚ Ω l 1 (Or.inl hl) Nat.one_pos ζ hζ
  have hex := (h S hS A hA μ hμ M (GlobalTheory.Published.zmodRep (l ^ 1) ρ) hρ).1
  have hμσ : μ (toGS Ω _ σ) = cycMod ℚ Ω l 1 σ := DFunLike.congr_fun hμ σ
  obtain ⟨z, hz⟩ := (hex.mem_range_localization_H2_iff
    (fun v => Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩)).2 (fun y => by
      rw [twDual_inv_eq_zero (l ^ 1) μ ρ _ a n hσa (by rw [hμσ]; exact hn) han y]
      simp only [map_zero, Finset.sum_const_zero])
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    refine ⟨⟨z.1, z.2⟩, fun v => ?_⟩
    have e : (Submodule.Quotient.mk (restrictCocycles2 (GlobalTheory.Published.zmodRep (l ^ 1) ρ) (locFam S A v)
        (continuous_locFam S A v) z) : H2 ((GlobalTheory.Published.zmodRep (l ^ 1) ρ).comp (locFam S A v))) =
        Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩ := congrFun hz v
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.eq _).1 e)
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, hcf⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostEx
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Base

private theorem prime_l {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl

private noncomputable def vQ {l : ℕ} (hl : l.Prime) : Pl where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l hl).ne_zero).mpr (prime_l hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l hl).ne_zero

private theorem fin_above {n : ℕ} (hn : n ≠ 0) : {v : Pl | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {((n : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact hv

private theorem cls_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) [NeZero M] (S : Set Pl)
    (hS : ∀ v ∉ S, ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ μ : GS Ω S →* (ZMod M)ˣ, μ.comp (toGS Ω S) = Chr.cls ℚ Ω M := by
  obtain ⟨hopen, -, -, -, hine⟩ := Chr.clsFacts ℚ Ω M
  obtain ⟨-, -, -, hpl⟩ := Kum.placeDict ℚ Ω
  have hle : NS Ω S ≤ (Chr.cls ℚ Ω M).ker := by
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    have hn : ¬ A.valuation ((M : ℕ) : Ω) < 1 := by
      rw [hpl A v M hA]
      exact hS v hv
    exact hine A hn hσA
  exact ⟨QuotientGroup.lift (NS Ω S) (Chr.cls ℚ Ω M) hle, QuotientGroup.lift_comp_mk' _ _ _⟩

private theorem cc_exists (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ σ : G ℚ Ω, IsCC σ := by
  obtain ⟨σ, j, hj⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) (fun q => by simp), j, fun x => hj x⟩

end

theorem UpperTheory.V.UnitaryThreeInertia.exists_hostFrame :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∃ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ hd
  have hl : l.Prime := Fact.out
  have hlN : l * N ≠ 0 := Nat.mul_ne_zero hl.ne_zero (NeZero.ne N)
  set S : Finset Pl := (fin_above hlN).toFinset with hSdef
  have hmem : ∀ v : Pl, v ∈ S ↔ (((l * N : ℕ)) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal :=
    fun v => Set.Finite.mem_toFinset _
  have hout : ∀ m : ℕ, m ∣ l * N → ∀ v ∉ (S : Set Pl),
      ((m : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro m hm v hv hmv
    apply hv
    rw [Finset.mem_coe, hmem]
    obtain ⟨k, hk⟩ := hm
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hmv
  have h4 : ∀ v ∉ (S : Set Pl), ((4 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    intro v hv h4v
    have h2 : ((2 : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
      have h22 : ((4 : ℕ) : NumberField.RingOfIntegers ℚ) =
          ((2 : ℕ) : NumberField.RingOfIntegers ℚ) * ((2 : ℕ) : NumberField.RingOfIntegers ℚ) := by
        rw [← Nat.cast_mul]
      rw [h22] at h4v
      rcases v.isPrime.mem_or_mem h4v with h | h <;> exact h
    exact hout 2 (dvd_mul_of_dvd_right (even_iff_two_dvd.mp hd.N_even) l) v hv h2
  obtain ⟨μN, hμN⟩ := cls_exists Ω N (S : Set Pl) (hout N (dvd_mul_left N l))
  obtain ⟨μ4, hμ4⟩ := cls_exists Ω 4 (S : Set Pl) h4
  obtain ⟨χl, hχl⟩ :=
    Formalism.GaloisCohomology.chi_exists (F := ℚ) (Ω := Ω) l (S : Set Pl) (hout l (dvd_mul_right l N))
  obtain ⟨σ, hσ⟩ := cc_exists Ω
  let A : S → ValuationSubring Ω := fun v => Classical.choose (exists_isPlaceOver Ω (v : Pl))
  have hA := fun v : S => Classical.choose_spec (exists_isPlaceOver Ω (v : Pl))
  have hvl : vQ hl ∈ S := by
    rw [hmem]
    exact Ideal.mem_span_singleton.mpr ⟨(N : NumberField.RingOfIntegers ℚ), by push_cast; ring⟩
  let F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S :=
    { π := toGS Ω (S : Set Pl)
      η := (MulChar.toUnitHom ZMod.χ₄).comp μ4
      Ψ := ((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN
      c := toGS Ω (S : Set Pl) σ
      D := fun v => Dec (A v)
      I := fun v => Ine (A v)
      vl := ⟨vQ hl, hvl⟩
      Sb := {v | ∃ p ∈ Sb l ψ, (p : NumberField.RingOfIntegers ℚ) ∈ (v : Pl).asIdeal} }
  refine ⟨S, A, F, ?_⟩
  refine ⟨hmem, hA, rfl, ?_, ?_, ⟨σ, hσ, rfl⟩, fun _ => rfl, fun _ => rfl, ?_, fun _ => Iff.rfl⟩
  · show ((MulChar.toUnitHom ZMod.χ₄).comp μ4).comp (toGS Ω (S : Set Pl)) = eta4 Ω
    rw [MonoidHom.comp_assoc, hμ4]
    unfold eta4 UpperTheory.V.Chr.dirG
    rfl
  · show (((Units.map (algebraMap ℤ_[l] c.O : ℤ_[l] →* c.O)).comp χl) ^ e *
        (MulChar.toUnitHom ψ).comp μN).comp (toGS Ω (S : Set Pl)) = _
    unfold UpperTheory.V.Chr.Psi UpperTheory.V.Chr.dirG UpperTheory.V.Base.chiO
    rw [← hχl, ← hμN]
    ext τ
    simp
  · exact Ideal.mem_span_singleton_self _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FinrankUnramifiedCocyclesEqFinrankInvariants
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private def affPairs (N : Type) [AddCommGroup N] : Subgroup (Equiv.Perm N × Equiv.Perm N) where
  carrier := {p | ∀ x y, p.2 (x + y) = p.1 x + p.2 y}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x y => by
    show a.2 (b.2 (x + y)) = a.1 (b.1 x) + a.2 (b.2 y)
    rw [hb, ha]
  inv_mem' := fun {a} ha x y => by
    show a.2.symm (x + y) = a.1.symm x + a.2.symm y
    apply a.2.injective
    rw [ha]
    simp

private theorem zhat_lift :
    ∀ {D E E' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group E] [Finite E] [Group E'] (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
      (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
      ∀ (q : E →* E') (w' : D →* E') (e : E), IsLocallyConstant w' → (∀ s ∈ I, w' s = 1) → q e = w' φ →
      ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ q.comp w = w' ∧ w φ = e ∧ ∀ g, w g ∈ Subgroup.zpowers e := by
  intro D E E' _ _ _ _ _ _ I φ hcl hd q w' e hw' hI hq
  have hn : 0 < orderOf e := orderOf_pos e
  haveI : NeZero (orderOf e) := ⟨hn.ne'⟩
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf e) hn
  let f : Multiplicative (ZMod (orderOf e)) →* E :=
    MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by
      intro a b
      simp only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])
  have hf1 : f (Multiplicative.ofAdd 1) = e := by
    show e ^ (1 : ZMod (orderOf e)).val = e
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hwl : IsLocallyConstant (f.comp d) := hdl.comp f
  have hwI : ∀ s ∈ I, (f.comp d) s = 1 := by
    intro s hs
    simp [hdI s hs]
  refine ⟨f.comp d, hwl, hwI, ?_, ?_, ?_⟩
  · have h1 : IsLocallyConstant (q.comp (f.comp d)) := hwl.comp q
    have h2 := (h1.prodMk hw').comp (fun p : E' × E' => p.1 = p.2)
    have hclosed : IsClosed (((q.comp (f.comp d)).eqLocus w' : Subgroup D) : Set D) := by
      have := h2.isClosed_fiber True
      convert this using 1
      ext x
      simp [MonoidHom.eqLocus]
      rfl
    have hle : I ⊔ Subgroup.zpowers φ ≤ (q.comp (f.comp d)).eqLocus w' := by
      refine sup_le ?_ ?_
      · intro s hs
        show q ((f.comp d) s) = w' s
        rw [hwI s hs, hI s hs, map_one]
      · rw [Subgroup.zpowers_le]
        show q (f (d φ)) = w' φ
        rw [hdφ, hf1, hq]
    have := Subgroup.topologicalClosure_minimal _ hle hclosed
    rw [hcl] at this
    ext x
    exact this (Subgroup.mem_top x)
  · show f (d φ) = e
    rw [hdφ, hf1]
  · intro g
    exact Subgroup.npow_mem_zpowers e _

theorem UpperTheory.finrank_unramified_cocycles_eq_finrank_invariants :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (I : Subgroup D) (W : Submodule k (D → M)), ContAction ρ → I.Normal → (∃ φ : D, (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
        (∀ y, y ∈ W ↔ y ∈ Z1 ρ ∧ ∀ s ∈ I, y s = 0) → finrank k W = finrank k (H0 (ρ.comp I.subtype : Representation k I M)) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ I W hρ hI ⟨φ, hcl, hd⟩ hW
  set N : Submodule k M := H0 (ρ.comp I.subtype : Representation k I M) with hNdef
  have hN : ∀ m, m ∈ N ↔ ∀ s ∈ I, ρ s m = m := fun m =>
    ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩
  have hev : ∀ y ∈ W, y φ ∈ N := by
    intro y hy
    obtain ⟨⟨-, hc⟩, h0⟩ := (hW y).1 hy
    rw [hN]
    intro s hs
    have h1 := hc s φ
    have h2 := hc φ (φ⁻¹ * s * φ)
    rw [h0 _ (hI.conj_mem' s hs φ), map_zero, add_zero] at h2
    rw [h0 s hs, zero_add] at h1
    rw [← h1, ← h2]
    congr 1
    group
  let ev : W →ₗ[k] N := ((LinearMap.proj φ).comp W.subtype).codRestrict N (fun y => hev y.1 y.2)
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have hyφ : y.1 φ = 0 := congrArg Subtype.val hy
    obtain ⟨⟨hcont, hc⟩, h0⟩ := (hW y.1).1 y.2
    have h1 : y.1 1 = 0 := h0 1 I.one_mem
    let Z : Subgroup D :=
      { carrier := {g | y.1 g = 0}
        one_mem' := h1
        mul_mem' := fun {a b} ha hb => by
          show y.1 (a * b) = 0
          rw [hc, show y.1 a = 0 from ha, show y.1 b = 0 from hb, map_zero, add_zero]
        inv_mem' := fun {a} ha => by
          have := hc a⁻¹ a
          rw [inv_mul_cancel, h1, show y.1 a = 0 from ha, map_zero, add_zero] at this
          exact this.symm }
    have hZ : IsClosed (Z : Set D) := isClosed_eq hcont continuous_const
    have hle : I ⊔ Subgroup.zpowers φ ≤ Z := sup_le h0 (by rw [Subgroup.zpowers_le]; exact hyφ)
    have := Subgroup.topologicalClosure_minimal _ hle hZ
    rw [hcl] at this
    ext g
    exact this (Subgroup.mem_top g)
  have hst : ∀ g : D, ∀ m : N, ρ g m ∈ N := by
    intro g m
    rw [hN]
    intro s hs
    have h := (hN m).1 m.2 _ (hI.conj_mem' s hs g)
    calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = ρ g m := by rw [h]
  let a0 : D →* Function.End N :=
    { toFun := fun g m => ⟨ρ g m, hst g m⟩
      map_one' := by
        funext m
        apply Subtype.ext
        show ρ 1 m = m
        simp
      map_mul' := fun g h => by
        funext m
        apply Subtype.ext
        show ρ (g * h) m = ρ g (ρ h m)
        simp }
  let a : D →* Equiv.Perm N := a0.toHomPerm
  have ha : ∀ g m, (a g m : M) = ρ g m := fun _ _ => rfl
  have hal : IsLocallyConstant a := by
    refine IsLocallyConstant.desc a (fun (p : Equiv.Perm N) (m : N) => (p m : M)) ?_ ?_
    · rw [IsLocallyConstant.iff_continuous]
      exact continuous_pi fun m => hρ.comp (continuous_id.prodMk continuous_const)
    · intro p q h
      ext m
      exact congrFun h m
  have haI : ∀ s ∈ I, a s = 1 := by
    intro s hs
    ext m
    exact (hN m).1 m.2 s hs
  have hsurj : Function.Surjective ev := by
    intro m
    obtain ⟨w, hwl, hwI, hq, hwφ, hw⟩ := zhat_lift I φ hcl hd (MonoidHom.fst _ (Equiv.Perm N)) a
      (a φ, Equiv.addRight m * a φ) hal haI rfl
    have hP : ∀ g, w g ∈ affPairs N := by
      intro g
      refine (Subgroup.zpowers_le.2 ?_ : _ ≤ affPairs N) (hw g)
      intro x y
      apply Subtype.ext
      show ρ φ (x + y : M) + m = ρ φ x + (ρ φ y + m)
      rw [map_add (f := _), add_assoc]
    have hw1 : ∀ g, (w g).1 = a g := fun g => DFunLike.congr_fun hq g
    refine ⟨⟨fun g => ((w g).2 0 : M), (hW _).2 ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
    · exact (hwl.comp (fun p : Equiv.Perm N × Equiv.Perm N => (p.2 0 : M))).continuous
    · intro g h
      have := hP g ((w h).2 0) 0
      rw [add_zero, hw1] at this
      show (((w (g * h)).2 0 : N) : M) = (w g).2 0 + ρ g ((w h).2 0)
      rw [map_mul, Prod.snd_mul, Equiv.Perm.mul_apply, this, Submodule.coe_add, ha, add_comm]
    · intro s hs
      show (((w s).2 0 : N) : M) = 0
      rw [hwI s hs]
      rfl
    · apply Subtype.ext
      show (((w φ).2 0 : N) : M) = m
      rw [hwφ]
      show ρ φ 0 + m = m
      simp
  exact (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq
end
