module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KrullDimQuotientComapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrAbs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivativeLocallyConstant
theorem UpperTheory.Reformulated.B.DerivativeLocallyConstant.dz_locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ ψ.ker
    simp
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DzExistsPrime
theorem UpperTheory.Reformulated.B.Qk11.dz_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_right _, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_left _, hm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGlobEuler
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.globEuler :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
  intro hF hE Ω _ inst _ l _ hl S hS k _ _ _ M _ _ _ _ _ ρ hρ σ hσ
  have hc : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hM : Finite M := Module.finite_of_finite k
  exact UpperTheory.global_euler_characteristic_rationals_odd_prime hF hE Ω l hl k M S ρ hS hρ σ hσ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FiniteCompactlySupportedH1
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem ker_open {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M) (h : ContAction ρ) :
    IsOpen (ρ.ker : Set Γ) := by
  let b := Module.finBasis k M
  have hset : (ρ.ker : Set Γ) = ⋂ i, {g | ρ g (b i) = b i} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg i
      rw [hg]
      rfl
    · intro hg
      exact b.ext fun i => by simpa using hg i
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous fun g : Γ => ρ g (b i) :=
    (show Continuous fun p : Γ × M => ρ p.1 p.2 from h).comp (continuous_id.prodMk continuous_const)
  exact hc.isOpen_preimage {b i} (isOpen_discrete _)

private theorem finite_compactly_supported_H1 {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)
    [Module.Finite k (H1 ρ)] : Module.Finite k (F.H1c ρ) := by
  have hB : (B1 ρ).FG := by
    show (LinearMap.range (d0 ρ)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian k ↥(B1 ρ) := isNoetherian_of_fg_of_noetherian _ hB
  have hK : (Submodule.comap (Z1 ρ).subtype (B1 ρ)).FG :=
    Submodule.fg_of_fg_map_injective (Z1 ρ).subtype Subtype.val_injective
      (Submodule.FG.of_le_of_isNoetherian (Submodule.map_comap_le _ _))
  have hZ : (⊤ : Submodule k ↥(Z1 ρ)).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Submodule.comap (Z1 ρ).subtype (B1 ρ)))
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq, Submodule.ker_mkQ]
      exact hK
  haveI : Module.Finite k ↥(Z1 ρ) := ⟨hZ⟩
  have hZ1 : (Z1 ρ).FG := Module.Finite.iff_fg.mp inferInstance
  have hP : ((Z1 ρ).prod (⊤ : Submodule k (F.T → M))).FG := hZ1.prod Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : F.H1c ρ ≤ (Z1 ρ).prod ⊤ := by
    rintro x ⟨hlc, hcoc, -, -, -⟩
    exact ⟨⟨hlc.continuous, hcoc⟩, trivial⟩
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)

theorem UpperTheory.V.X.framed_h1_euler_formula :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M), ContAction ρ → (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (H1 ρ) → Module.Finite k (F.H1c ρ) ∧ finrank k (F.H1c ρ) + finrank k (H0 ρ) = finrank k (selF F ρ) + ∑ v, finrank k (H0 (ρ.comp (F.φ v))) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ F ρ hc hN hH
  refine ⟨finite_compactly_supported_H1 F ρ, ?_⟩
  have e := Alg.finrank_compact_support_H1 k Γ M ρ (ker_open ρ hc) F hN hH
  have hs : finrank k ↥(selF F ρ) = finrank k ↥(Sha1 ρ F.φ F.hφ ⊓
      Sel ρ F.ψ F.hψ fun q => H1ur (ρ.comp (F.ψ q)) (F.N q)) := rfl
  rw [hs]
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcLocEuler
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

private theorem ef_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  haveI := v.isPrime
  have h1 := Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal
  have h2 := Ideal.inertiaDeg_pos v.asIdeal ℤ
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)
  rw [NumberField.RingOfIntegers.rank, Module.finrank_self] at hsum
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨v.asIdeal, inferInstance, ⟨rfl⟩⟩)
  rw [hsum] at hle
  exact le_antisymm hle (Nat.mul_pos h1 h2)

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
    apply LinearMap.ext
    intro m
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]
    have := hy g (ρ g⁻¹ m)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem UpperTheory.V.X.locEuler :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (Dec (F := ℚ) A) M), ContAction ρ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + (if p = l then finrank k M else 0) ∧ finrank k (H2 ρ) = finrank k (Loc.H0dual ((cycK Ω l k).comp (Dec (F := ℚ) A).subtype) ρ) := by
  intro hF hT hE0 Ω _ _ _ l _ p hp A hA k _ _ hc M _ _ _ _ _ ρ hρ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := p) (F := ℚ) A hA
  have hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := hw
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F := ℚ) A) M := Loc.resCoef (ZMod (l ^ 1)) ρ
  have h : ∀ g m, ρ' g m = ρ (MulEquiv.refl _ g) m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨-, f1, f2, -⟩ := hF ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  obtain ⟨⟨inv⟩, -, -, -, hb⟩ := hT ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  have hE := hE0 ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hd : locDeg w = 1 := ef_eq_one w
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_, ?_⟩
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
    split_ifs with hvl
    · subst hvl
      have h1 : Nat.card (H1 ρ') = Nat.card (H0 ρ') * Nat.card (H2 ρ') * Nat.card M ^ locDeg w := hE.1 hw
      rw [hd, pow_one (Nat.card M)] at h1
      rw [← Module.natCard_eq_pow_finrank]
      exact h1
    · rw [pow_zero, mul_one]
      refine hE.2 fun hlw => w.isPrime.ne_top ?_
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hvl)).map
        (Int.castRingHom (𝓞 ℚ))
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by simpa using hw))
        (w.asIdeal.mul_mem_left _ (by simpa using hlw))
  · apply Nat.pow_right_injective hk
    beta_reduce
    let χ := (cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype
    haveI : Finite (Module.Dual k M) := DFunLike.finite _
    haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
    let B : Type := H0 ((twDual χ ρ').comp (MonoidHom.id _))
    let E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv
    haveI : Finite B := Subtype.finite
    haveI := hc
    have hχ : ∀ g, ((((cycK Ω l k).comp (Dec (F := ℚ) A).subtype) (MulEquiv.refl _ g) : kˣ) : k) =
        algebraMap (ZMod (l ^ 1)) k (χ g) := fun g =>
      RingHom.congr_fun (Subsingleton.elim (ZMod.castHom (dvd_pow_self l one_ne_zero) k)
        (algebraMap (ZMod (l ^ 1)) k)) _
    rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2,
      card_H0dual ρ ρ' (MulEquiv.refl _) h _ χ hχ,
      ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDecZhat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

section SlopeTestRemainingChoices

open Formalism.GaloisCohomology UpperTheory.V.Base

private theorem dz_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.DerivativeLocallyConstant.dz_locConst ψ h

private theorem dz_exists_prime (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : n ≠ 0) (h : (n : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 ℚ) ∈ v.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk11.dz_exists_prime v n hn h

private theorem dz_not_both (v : HeightOneSpectrum (𝓞 ℚ)) {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 ℚ) ∈ v.asIdeal)
    (hb : (b : 𝓞 ℚ) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, h⟩ : IsCoprime (a : 𝓞 ℚ) (b : 𝓞 ℚ) := hab.cast
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ha) (v.asIdeal.mul_mem_left _ hb)))

private theorem dz_val {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hv ((n : ℕ) : 𝓞 ℚ)
  have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
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

private theorem dz_frob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : IsPlaceOver A v) (D I : Subgroup (G ℚ Ω)) (hD : D = Dec (F := ℚ) A) (hI : I = Ine (F := ℚ) A) :
    ∃ φ : D, (I.subgroupOf D ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
      ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I.subgroupOf D, d s = 1) ∧
        d φ = Multiplicative.ofAdd 1 := by
  subst hD hI
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨γ, hγ⟩ := exists_isFrob hv
  refine ⟨⟨γ, hγ.1⟩, ?_, fun n hn => ?_⟩
  · have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω)
      ⟨(Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have h1 : Dec (F := ℚ) A ≤ (Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure := by
      refine le_trans (le_sInf ?_) key.ge
      rintro N ⟨hNo, hN⟩
      have h := (Subgroup.le_topologicalClosure _).trans hN
      exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (le_sup_left.trans h)
        (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers γ)))
    have h2 : ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔
        Subgroup.zpowers (⟨γ, hγ.1⟩ : Dec (F := ℚ) A)).map (Dec (F := ℚ) A).subtype =
        Ine (F := ℚ) A ⊔ Subgroup.zpowers γ := by
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
    have hqv : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := hq ▸ Ideal.absNorm_mem _
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
    obtain ⟨hopen, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω m
    have hI := hIne A fun h => dz_not_both v hmp ((dz_val hv m).1 h) hpv
    have hu : ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m) = normV v := by
      haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
      have hv1 : A.valuation ζ ≤ 1 := by
        have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact ((pow_eq_one_iff_left (NeZero.ne m)).1 h1).le
      have h2 : γ ζ = ζ ^ normV v := by
        refine (LDataCardLeFinrank.ineFixRoots ℚ Ω p A hA m hmp (ζ ^ normV v) ?_).1 (γ ζ) ?_ (hγ.2 ζ hv1)
        · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        · rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [Chr.cls_spec m γ ζ hζ.pow_eq_one, pow_eq_pow_mod (normV v) hζ.pow_eq_one] at h2
      have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h2
      rw [← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m), h3, ZMod.natCast_mod]
    have hord := dz_order hq1 hn hm _ hu
    have hle : Dec (F := ℚ) A ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) := by
      have hk : (Chr.cls ℚ Ω m).ker ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) :=
        Subgroup.ker_le_comap _ _
      exact Kum.decGen ℚ Ω A _ γ _ hv hγ (Subgroup.isOpen_mono hk hopen) (hI.trans hk) (Subgroup.mem_zpowers _)
    let f : Dec (F := ℚ) A →* Subgroup.zpowers (Chr.cls ℚ Ω m γ) :=
      ((Chr.cls ℚ Ω m).comp (Dec (F := ℚ) A).subtype).codRestrict _ fun x => hle x.2
    have hg : ∀ x : Subgroup.zpowers (Chr.cls ℚ Ω m γ), x ∈ Subgroup.zpowers (f ⟨γ, hγ.1⟩) := by
      rintro ⟨_, k, rfl⟩
      exact ⟨k, rfl⟩
    have hc : Nat.card (Subgroup.zpowers (Chr.cls ℚ Ω m γ)) = n := by rw [Nat.card_zpowers, hord]
    have hf1 : ∀ s : Dec (F := ℚ) A, Chr.cls ℚ Ω m s = 1 → f s = 1 := fun s hs => Subtype.ext hs
    refine ⟨(zmodMulEquivOfGenerator hg hc).symm.toMonoidHom.comp f, dz_locConst _ ?_, fun s hs => ?_, ?_⟩
    · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω m).ker.subgroupOf _) (fun s hs => ?_)
        (hopen.preimage continuous_subtype_val)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf1 s hs, map_one]
    · rw [MonoidHom.comp_apply, hf1 s (hI hs), map_one]
    · exact zmodMulEquivOfGenerator_symm_apply_generator hg hc

end SlopeTestRemainingChoices

theorem UpperTheory.V.X.decZhat :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∃ φ : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : Dec (F := ℚ) A →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A), d s = 1) ∧ d φ = Multiplicative.ofAdd 1 := by
  intro Ω _ _ _ p hp A hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hP := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := hP.1 fun h => (hP.2.1 h).2 hA
  exact dz_frob Ω A v hv _ _ rfl rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcFrameOb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

noncomputable section

namespace UpperTheory.V.X.FrameOb

section Lin

variable {k A W L O S : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup W] [Module k W]
  [AddCommGroup L] [Module k L] [AddCommGroup O] [Module k O] [AddCommGroup S] [Module k S]

private theorem count [Module.Finite k A] [Module.Finite k L] [Module.Finite k S]
    (f : A →ₗ[k] L) (π : W →ₗ[k] L) (hπ : Function.Surjective π) (g : W →ₗ[k] O) (h : O →ₗ[k] S)
    (h1 : LinearMap.ker g = (LinearMap.range f).comap π) (h2 : LinearMap.ker h = LinearMap.range g) :
    Module.Finite k O ∧ finrank k O + finrank k A =
      finrank k (LinearMap.range h) + finrank k L + finrank k (LinearMap.ker f) := by
  have hs : Function.Surjective ((LinearMap.range f).mkQ ∘ₗ π) :=
    (Submodule.mkQ_surjective _).comp hπ
  have hk : LinearMap.ker g = LinearMap.ker ((LinearMap.range f).mkQ ∘ₗ π) := by
    rw [h1, LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : LinearMap.ker h ≃ₗ[k] (L ⧸ LinearMap.range f) :=
    (LinearEquiv.ofEq _ _ h2).trans (g.quotKerEquivRange.symm.trans
      ((Submodule.quotEquivOfEq _ _ hk).trans (LinearMap.quotKerEquivOfSurjective _ hs)))
  haveI : Module.Finite k (LinearMap.ker h) := Module.Finite.equiv e.symm
  haveI : Module.Finite k (O ⧸ LinearMap.ker h) := Module.Finite.equiv h.quotKerEquivRange.symm
  haveI hO : Module.Finite k O := Module.Finite.of_submodule_quotient (LinearMap.ker h)
  refine ⟨hO, ?_⟩
  have a1 := h.finrank_range_add_finrank_ker
  have a2 := f.finrank_range_add_finrank_ker
  have a3 := (LinearMap.range f).finrank_quotient_add_finrank
  have a4 := e.finrank_eq
  omega

private theorem rk {I J : Type} [Fintype I] [Fintype J] (P : I → Type) (Q : J → Type) [∀ i, AddCommGroup (P i)]
    [∀ i, Module k (P i)] [∀ i, AddCommGroup (Q i)] [∀ i, Module k (Q i)] [∀ i, Module.Finite k (P i)]
    [∀ i, Module.Finite k (Q i)] (U : ∀ j, Submodule k (Q j)) :
    finrank k ((∀ i, P i) × (∀ j, Q j ⧸ U j)) + ∑ j, finrank k (U j) =
      ∑ i, finrank k (P i) + ∑ j, finrank k (Q j) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype, add_assoc,
    ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun q _ => Submodule.finrank_quotient_add_finrank _)

end Lin

variable {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)

private theorem mem_coboundaries_compact (x : F.C2 M) : x ∈ F.framedTwoCoboundaries ρ ↔
    ∃ (h : Γ → M) (y : F.T → M) (e : ∀ q, F.Gq q → M), IsLocallyConstant h ∧
    (∀ q, IsLocallyConstant (e q) ∧ (∀ s t, e q (s * t) = e q s + ρ (F.ψ q s) (e q t)) ∧ ∀ n ∈ F.N q, e q n = 0) ∧
    x.1 = Alg.dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧
    ∀ q s, x.2.2 q s = h (F.ψ q s) - e q s := by
  refine ⟨fun hx => ?_, fun hx => Submodule.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 0, 0, IsLocallyConstant.const 0, fun q => ⟨IsLocallyConstant.const 0, by simp, by simp⟩,
      by funext p; simp [Alg.dOne], by simp, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := hx
    obtain ⟨h', y', e', b1, b2, b3, b4, b5⟩ := hx'
    refine ⟨h + h', y + y', e + e', a1.add b1, fun q => ⟨(a2 q).1.add (b2 q).1, fun s t => ?_, fun n hn => ?_⟩,
      ?_, fun v s => ?_, fun q s => ?_⟩
    · simp only [Pi.add_apply, (a2 q).2.1, (b2 q).2.1, map_add (f := _)]; abel
    · simp [(a2 q).2.2 n hn, (b2 q).2.2 n hn]
    · funext p
      simp only [Prod.fst_add, Pi.add_apply, a3, b3, Alg.dOne, map_add (f := _)]; abel
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add (f := _)]; abel
    · simp only [Prod.snd_add, Pi.add_apply, a5, b5]; abel
  | smul c x _ hx =>
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := hx
    refine ⟨c • h, c • y, c • e, a1.comp (c • ·), fun q => ⟨(a2 q).1.comp (c • ·), fun s t => ?_, fun n hn => ?_⟩,
      ?_, fun v s => ?_, fun q s => ?_⟩
    · simp [(a2 q).2.1]
    · simp [(a2 q).2.2 n hn]
    · funext p
      simp [a3, Alg.dOne, smul_sub]
    · simp [a4, smul_sub]
    · simp [a5, smul_sub]

private theorem first_differential_eq {G : Type} [Group G] [TopologicalSpace G] (σ : Representation k G M) (c : G → M) :
    d1 σ c = Alg.dOne σ c := by
  funext p
  obtain ⟨s, t⟩ := p
  simp only [d1_apply, Alg.dOne]; abel

private def hZ : F.framedTwoCocycles ρ →ₗ[k] Z2 ρ where
  toFun x := ⟨x.1.1, x.2.1.continuous, fun s t u => by
    have := x.2.2.2.2.1 s t u
    rw [sub_add_eq_add_sub, this]; abel⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def hO : F.Ob ρ →ₗ[k] H2 ρ :=
  Submodule.mapQ _ _ (hZ F ρ) fun x hx => by
    obtain ⟨h, y, e, a1, -, a3, -⟩ := (mem_coboundaries_compact F ρ _).1 hx
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨h, a1.continuous, by rw [first_differential_eq]; exact a3.symm⟩

private abbrev WW := (∀ v, Z1 (ρ.comp (F.φ v))) × (∀ q, Z1 (ρ.comp (F.ψ q)))

private abbrev LL := (∀ v, H1 (ρ.comp (F.φ v))) × (∀ q, H1 (ρ.comp (F.ψ q)) ⧸ H1ur (ρ.comp (F.ψ q)) (F.N q))

private def gZ : WW F ρ →ₗ[k] F.framedTwoCocycles ρ where
  toFun a := ⟨(0, fun v => (a.1 v).1, fun q => (a.2 q).1), IsLocallyConstant.const 0,
    fun v => (IsLocallyConstant.iff_continuous _).2 (a.1 v).2.1,
    fun q => (IsLocallyConstant.iff_continuous _).2 (a.2 q).2.1, by simp,
    fun v s t => by simp only [Alg.dOne, (a.1 v).2.2 s t, sub_self, Pi.zero_apply],
    fun q s t => by simp only [Alg.dOne, (a.2 q).2.2 s t, sub_self, Pi.zero_apply]⟩
  map_add' _ _ := Subtype.ext (Prod.ext (by simp) rfl)
  map_smul' _ _ := Subtype.ext (Prod.ext (by simp) rfl)

private def gO : WW F ρ →ₗ[k] F.Ob ρ := Submodule.mkQ _ ∘ₗ gZ F ρ

private def pL : WW F ρ →ₗ[k] LL F ρ where
  toFun a := (fun v => Submodule.Quotient.mk (a.1 v), fun q => Submodule.Quotient.mk (Submodule.Quotient.mk (a.2 q)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fL : H1 ρ →ₗ[k] LL F ρ where
  toFun a := (fun v => resH1 ρ (F.φ v) (F.hφ v) a, fun q => Submodule.Quotient.mk (resH1 ρ (F.ψ q) (F.hψ q) a))
  map_add' _ _ := by simp only [map_add (f := _)]; rfl
  map_smul' _ _ := by simp only [map_smul]; rfl

private theorem pL_surj : Function.Surjective (pL F ρ) := by
  rintro ⟨a, b⟩
  choose a' ha using fun v => Submodule.Quotient.mk_surjective _ (a v)
  choose b' hb using fun q => Submodule.Quotient.mk_surjective _ (b q)
  choose b'' hb' using fun q => Submodule.Quotient.mk_surjective _ (b' q)
  refine ⟨(a', b''), Prod.ext (funext ha) (funext fun q => ?_)⟩
  change Submodule.Quotient.mk (Submodule.Quotient.mk (b'' q)) = b q
  rw [hb', hb]

private theorem ker_fL : LinearMap.ker (fL F ρ) = selF F ρ := by
  ext x
  simp only [selF, LinearMap.mem_ker, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, Prod.ext_iff,
    funext_iff]
  refine and_congr Iff.rfl (forall_congr' fun q => ?_)
  exact Submodule.Quotient.mk_eq_zero _

private theorem range_hO : LinearMap.range (hO F ρ) = shaF F ρ := by
  ext x
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [shaF, LinearMap.mem_ker, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← hy]
    refine ⟨fun v => ?_, fun q => ?_⟩
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨y.1.2.1 v, (y.2.2.1 v).continuous, ?_⟩)
      rw [first_differential_eq]
      funext p
      exact (y.2.2.2.2.2.1 v p.1 p.2).symm
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨y.1.2.2 q, (y.2.2.2.1 q).continuous, ?_⟩)
      rw [first_differential_eq]
      funext p
      exact (y.2.2.2.2.2.2 q p.1 p.2).symm
  · rintro ⟨h1, h2⟩
    choose a ha ha' using fun v => (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (h1 v))
    choose b hb hb' using fun q => (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (h2 q))
    refine ⟨Submodule.Quotient.mk ⟨(κ.1, a, b), (IsLocallyConstant.iff_continuous _).2 κ.2.1,
      fun v => (IsLocallyConstant.iff_continuous _).2 (ha v),
      fun q => (IsLocallyConstant.iff_continuous _).2 (hb q), fun s t u => ?_, fun v s t => ?_, fun q s t => ?_⟩, rfl⟩
    · have := κ.2.2 s t u
      rw [← sub_eq_zero, ← this]; abel
    · rw [← first_differential_eq, ha']; rfl
    · rw [← first_differential_eq, hb']; rfl

private theorem ker_hO : LinearMap.ker (hO F ρ) = LinearMap.range (gO F ρ) := by
  ext x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro hx
    obtain ⟨c, hc, hc'⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    rw [first_differential_eq] at hc'
    have hc2 : x.1.1 = Alg.dOne ρ c := hc'.symm
    obtain ⟨x, a1, a2, a3, a4, a5, a6⟩ := x
    dsimp only at hc2
    refine ⟨(fun v => ⟨fun s => x.2.1 v s - c (F.φ v s), (a2 v).continuous.sub (hc.comp (F.hφ v)), fun s t => ?_⟩,
      fun q => ⟨fun s => x.2.2 q s - c (F.ψ q s), (a3 q).continuous.sub (hc.comp (F.hψ q)), fun s t => ?_⟩), ?_⟩
    · have := a5 v s t
      rw [hc2] at this
      simp only [Alg.dOne, MonoidHom.comp_apply, map_sub, map_mul] at this ⊢
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    · have := a6 q s t
      rw [hc2] at this
      simp only [Alg.dOne, MonoidHom.comp_apply, map_sub, map_mul] at this ⊢
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    · symm
      refine (Submodule.Quotient.eq _).2 ((mem_coboundaries_compact F ρ _).2 ⟨c, 0, 0, (IsLocallyConstant.iff_continuous _).2 hc,
        fun q => ⟨IsLocallyConstant.const 0, by simp, by simp⟩, ?_, fun v s => ?_, fun q s => ?_⟩)
      · change x.1 - 0 = _
        rw [sub_zero, hc2]
      · change x.2.1 v s - (x.2.1 v s - c (F.φ v s)) = _
        simp
      · change x.2.2 q s - (x.2.2 q s - c (F.ψ q s)) = _
        simp
  · rintro ⟨a, ha⟩
    rw [← ha]
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨0, continuous_const, ?_⟩)
    rw [map_zero]; rfl

private theorem ker_gO (hN : ∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) :
    LinearMap.ker (gO F ρ) = (LinearMap.range (fL F ρ)).comap (pL F ρ) := by
  ext a
  constructor
  · intro ha
    have ha' : gZ F ρ a ∈ (F.framedTwoCoboundaries ρ).comap (F.framedTwoCocycles ρ).subtype := (Submodule.Quotient.mk_eq_zero _).1 ha
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := (mem_coboundaries_compact F ρ (gZ F ρ a).1).1 ha'
    have hz : h ∈ Z1 ρ := ⟨a1.continuous, fun s t => by
      have : (0 : M) = Alg.dOne ρ h (s, t) := congrFun a3 (s, t)
      simp only [Alg.dOne] at this
      exact (sub_eq_zero.1 this.symm).symm⟩
    refine ⟨Submodule.Quotient.mk ⟨h, hz⟩, Prod.ext (funext fun v => ?_) (funext fun q => ?_)⟩
    · refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨y v, fun s => ?_⟩)
      have : (a.1 v).1 s = _ := a4 v s
      change h (F.φ v s) - (a.1 v).1 s = ρ (F.φ v s) (y v) - y v
      rw [this]; abel
    · refine (Submodule.Quotient.eq _).2 ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun s => ?_⟩))
      have : (a.2 q).1 s = _ := a5 q s
      change h (F.ψ q s) - (a.2 q).1 s = _
      rw [this, (a2 q).2.2 s s.2]; simp
  · rintro ⟨h, hh⟩
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    choose y hy using fun v => (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 (congrFun (congrArg Prod.fst hh) v))
    choose m hm using fun q => (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1
      ((Submodule.Quotient.eq _).1 (congrFun (congrArg Prod.snd hh) q)))
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries_compact F ρ _).2 ⟨h.1, y, fun q s => h.1 (F.ψ q s) - (a.2 q).1 s,
      (IsLocallyConstant.iff_continuous _).2 h.2.1, fun q => ⟨(IsLocallyConstant.iff_continuous _).2
        ((h.2.1.comp (F.hψ q)).sub (a.2 q).2.1), fun s t => ?_, fun n hn => ?_⟩, ?_, fun v s => ?_, fun q s => ?_⟩)
    · simp only [map_mul, h.2.2, (a.2 q).2.2 s t, map_sub, MonoidHom.comp_apply]; abel
    · have : h.1 (F.ψ q n) - (a.2 q).1 n = ρ (F.ψ q n) (m q) - m q := hm q ⟨n, hn⟩
      refine this.trans ?_
      rw [hN q n hn]; simp
    · funext p
      change (0 : M) = _
      simp only [Alg.dOne, h.2.2, sub_self]
    · have : h.1 (F.φ v s) - (a.1 v).1 s = ρ (F.φ v s) (y v) - y v := hy v s
      change (a.1 v).1 s = _
      rw [← this]; abel
    · exact (sub_sub_cancel _ _).symm

end UpperTheory.V.X.FrameOb

end

open UpperTheory.V.X.FrameOb in
theorem UpperTheory.V.X.frameOb :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M), ContAction ρ → (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (H1 ρ) → Module.Finite k (H2 ρ) → (∀ v, Module.Finite k (H1 (ρ.comp (F.φ v)))) → (∀ q, Module.Finite k (H1 (ρ.comp (F.ψ q)))) → Module.Finite k (F.Ob ρ) ∧ finrank k (F.Ob ρ) + finrank k (H1 ρ) + ∑ q, finrank k (H1ur (ρ.comp (F.ψ q)) (F.N q)) = finrank k (shaF F ρ) + ∑ v, finrank k (H1 (ρ.comp (F.φ v))) + ∑ q, finrank k (H1 (ρ.comp (F.ψ q))) + finrank k (selF F ρ) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ F ρ _ hN i1 i2 i3 i4
  obtain ⟨c1, c2⟩ := count (fL F ρ) (pL F ρ) (pL_surj F ρ) (gO F ρ) (hO F ρ) (ker_gO F ρ hN) (ker_hO F ρ)
  refine ⟨c1, ?_⟩
  rw [range_hO, ker_fL] at c2
  have c3 : finrank k (LL F ρ) + _ = _ := rk (k := k) (fun v => H1 (ρ.comp (F.φ v))) (fun q => H1 (ρ.comp (F.ψ q)))
    (fun q => H1ur (ρ.comp (F.ψ q)) (F.N q))
  omega
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galCount :
    HcPublished → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M), (∀ m, IsLocallyConstant fun g => ρ g m) → (∀ q ∈ Q, ∀ g ∈ Ine (F := ℚ) (pl q), g ∈ K → ρ (toGS Ω SP g) = 1) → ∀ σ : G ℚ Ω, IsCC σ → Module.Finite k ((galFrame SP T Q v0 pl K).Ob ρ) ∧ Module.Finite k ((galFrame SP T Q v0 pl K).H1c ρ) ∧ finrank k ((galFrame SP T Q v0 pl K).Ob ρ) = finrank k ((galFrame SP T Q v0 pl K).H1c ρ) + finrank k (LinearMap.ker (ρ (toGS Ω SP σ) - 1)) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro P Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ ρ hlc hN σ hσ
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : Finite M := Module.finite_of_finite k
  have hρ : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    exact fun m => (hlc m).continuous
  have hN' : ∀ q, ∀ n ∈ (galFrame SP T Q v0 pl K).N q, ρ ((galFrame SP T Q v0 pl K).ψ q n) = 1 :=
    fun q n hn => hN q.1 q.2 n.1 hn.1 hn.2
  have tail := galTail P.lf P.gf P.pt Ω l v0 hD k M ρ hρ
  have hG : Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
    obtain ⟨S, e, rfl, hS, -⟩ := galIdx Ω l v0 hD
    exact globEuler P.gf P.ge Ω l hD.l_odd S hS k M ρ hρ σ hσ
  obtain ⟨g1, g2, g3⟩ := hG
  have hc : ∀ p, ContAction (ρ.comp (locHom SP (pl p))) := fun p =>
    hρ.comp ((continuous_locHom SP (pl p)).prodMap continuous_id)
  have loc := fun p (hp : p ∈ T ∨ p ∈ Q) => locEuler P.lf P.lt P.le Ω l p (hD.prime p hp) (pl p) (hD.isOver p hp) k M _ (hc p)
  obtain ⟨a1, a2⟩ := framed_h1_euler_formula (galFrame SP T Q v0 pl K) ρ hρ hN' g1
  obtain ⟨b1, b2⟩ := frameOb (galFrame SP T Q v0 pl K) ρ hρ hN' g1 g2 (fun v => (loc v.1 (.inl v.2)).1)
    (fun q => (loc q.1 (.inr q.2)).1)
  refine ⟨b1, a1, ?_⟩
  have hT : ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) = ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) +
      ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + finrank k M := by
    rw [Finset.sum_congr rfl fun (v : T) _ => (loc v.1 (.inl v.2)).2.2.1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨l, hD.l_mem⟩]
    · simp
    · intro b _ hb
      exact if_neg fun h => hb (Subtype.ext h)
    · simp
  have hQ : ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) =
      ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) +
      ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hql : (q : ℕ) ≠ l := fun h => Finset.disjoint_left.1 hD.disj hD.l_mem (h ▸ q.2)
    obtain ⟨φ, h1, h2⟩ := decZhat Ω q (hD.prime _ (.inr q.2)) (pl q) (hD.isOver _ (.inr q.2))
    rw [(loc q.1 (.inr q.2)).2.2.1, if_neg hql, add_zero,
      urIndex l _ (hc q) ((Ine (F := ℚ) (pl q)).subgroupOf (Dec (F := ℚ) (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))
        (Subgroup.comap_mono inf_le_left) ?_,
      urAbs _ (hc q) _ φ h1 h2]
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
    exact hD.idx q q.2
  change _ + _ = _ + ∑ v : T, finrank k (H0 (ρ.comp (locHom SP (pl v)))) at a2
  change _ + _ + ∑ q : Q, finrank k (H1ur (ρ.comp (locHom SP (pl q))) ((Ine (F := ℚ) (pl q) ⊓ K).subgroupOf (Dec (F := ℚ) (pl q)))) =
    _ + ∑ v : T, finrank k (H1 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H1 (ρ.comp (locHom SP (pl q)))) + _ at b2
  omega
