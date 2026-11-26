module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivLabelledLatticesUnitaryTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTrait
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

namespace GlobalTheory.QuotientCardinalityFinrank

theorem free_baseChange_quot (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Finite (𝓞 K) L] [Module.IsTorsionFree (𝓞 K) L] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (j : ℕ) :
    Module.Free (𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)})
      ((𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ⊗[𝓞 K] L) := by
  set I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}
  let P : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  haveI : P.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hℓ)
  have hP0 : P ≠ ⊥ := by simp [P, hℓ.ne_zero]
  let T := Algebra.algebraMapSubmonoid (𝓞 K) P.primeCompl
  have hT : T ≤ nonZeroDivisors (𝓞 K) :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
      P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain (Localization T) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hT
  haveI : IsDedekindDomain (Localization T) := IsLocalization.isDedekindDomain (𝓞 K) hT _
  haveI : IsPrincipalIdealRing (Localization T) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) P hP0
  have hunit : ∀ t : T, IsUnit (Ideal.Quotient.mk I (t : 𝓞 K)) := by
    rintro ⟨_, z, hz, rfl⟩
    have hz' : ¬ (ℓ : ℤ) ∣ z := fun h => hz (Ideal.mem_span_singleton.mpr h)
    have hc : IsCoprime z ((ℓ : ℤ) ^ j) :=
      (((Nat.prime_iff_prime_int.mp hℓ).irreducible.coprime_iff_not_dvd).mpr hz').symm.pow_right
    obtain ⟨u, v, huv⟩ := hc
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (u : 𝓞 K)) ?_
    have hmem : (((ℓ ^ j : ℕ) : 𝓞 K)) ∈ I := Ideal.mem_span_singleton_self _
    have : (algebraMap ℤ (𝓞 K) z) * (u : 𝓞 K) = 1 - (v : 𝓞 K) * ((ℓ ^ j : ℕ) : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this ⊢
      linear_combination this
    rw [← map_mul, this, map_sub, map_one, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero,
      sub_zero]
  letI : Algebra (Localization T) (𝓞 K ⧸ I) := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower (𝓞 K) (Localization T) (𝓞 K ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq, Ideal.Quotient.algebraMap_eq]
  haveI : Module.Flat (Localization T) (Localization T ⊗[𝓞 K] L) := Module.Flat.baseChange _ _ _
  haveI : Module.IsTorsionFree (Localization T) (Localization T ⊗[𝓞 K] L) := Module.Flat.isTorsionFree
  haveI : Module.Free (Localization T) (Localization T ⊗[𝓞 K] L) := Module.free_of_finite_type_torsion_free'
  exact Module.Free.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (Localization T) (𝓞 K ⧸ I) (𝓞 K ⧸ I) L)

end GlobalTheory.QuotientCardinalityFinrank

namespace GlobalTheory.QuotientCardinalityFinrank

theorem card_eq_pow_finrank (A M : Type) [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] : Nat.card M = Nat.card A ^ Module.finrank A M := by
  rw [Nat.card_congr (Module.finBasis A M).equivFun.toEquiv, Nat.card_fun]
  simp

theorem card_quot_int (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (n : ℕ)
    (hn : 2 ≤ n) :
    Nat.card (L ⧸ (Ideal.span {((n : ℕ) : ℤ)} • ⊤ : Submodule ℤ L)) = n ^ Module.finrank ℤ L := by
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {((n : ℕ) : ℤ)})).toEquiv]
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hA : Nat.card (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}) = n := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod n).toEquiv, Nat.card_zmod]
  haveI : Nontrivial (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}) := (Int.quotientSpanNatEquivZMod n).nontrivial
  rw [card_eq_pow_finrank (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}), Module.finrank_baseChange, hA]

theorem card_ringOfIntegers_quot (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Nat.card (𝓞 K ⧸ Ideal.span {((n : ℕ) : 𝓞 K)}) = n ^ Module.finrank ℚ K := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have : ((n : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((n : ℕ) : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp [Int.natAbs_pow]

theorem restrictScalars_span_smul_top (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] (n : ℕ) :
    (Ideal.span {((n : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L).restrictScalars ℤ =
      (Ideal.span {((n : ℕ) : ℤ)} • ⊤ : Submodule ℤ L) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.ideal_span_singleton_smul]
  ext x
  simp only [Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and, Nat.cast_smul_eq_nsmul]

theorem quot_equiv_pi_pos (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] [Module.Finite ℤ L] [Module.IsTorsionFree (𝓞 K) L] (r : ℕ)
    (hr : Module.finrank ℤ L = r * Module.finrank ℚ K) (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) (hj : 0 < j) :
    Nonempty ((Fin r → 𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ≃ₗ[𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}]
      L ⧸ (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
  set I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}
  haveI : Module.Finite (𝓞 K) L := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) L
  have hn : 2 ≤ ℓ ^ j := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ ≤ ℓ ^ j := Nat.le_self_pow hj.ne' ℓ
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hcardA := card_ringOfIntegers_quot K (ℓ ^ j)
  haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcardA]; positivity)
  haveI : Nontrivial (𝓞 K ⧸ I) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [hcardA]
    exact Nat.one_lt_pow hd.ne' (by omega)
  haveI := free_baseChange_quot K L ℓ hℓ j
  let e1 : ((𝓞 K ⧸ I) ⊗[𝓞 K] L) ≃ₗ[𝓞 K ⧸ I] L ⧸ (I • ⊤ : Submodule (𝓞 K) L) :=
    (TensorProduct.quotTensorEquivQuotSMul L I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  haveI : Module.Free (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) := Module.Free.of_equiv e1
  haveI : Module.Finite (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) := Module.Finite.equiv e1
  have hM := card_eq_pow_finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L))
  have hM2 : Nat.card (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) = (ℓ ^ j) ^ (r * Module.finrank ℚ K) := by
    rw [← hr, ← card_quot_int L (ℓ ^ j) hn, ← restrictScalars_span_smul_top K L (ℓ ^ j)]
    exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ _).toEquiv.symm
  have hM' : (ℓ ^ j) ^ (r * Module.finrank ℚ K) =
      (ℓ ^ j) ^ (Module.finrank ℚ K * Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L))) := by
    rw [← hM2, hM, hcardA, pow_mul]
  have hk : Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) = r := by
    have := Nat.pow_right_injective hn hM'
    have : Module.finrank ℚ K * Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) =
      Module.finrank ℚ K * r := by rw [← this]; ring
    exact (Nat.eq_of_mul_eq_mul_left hd this)
  exact ⟨(Module.finBasisOfFinrankEq (𝓞 K ⧸ I) _ hk).equivFun.symm⟩

theorem quot_equiv_pi (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] [Module.Finite ℤ L] [Module.IsTorsionFree (𝓞 K) L] (r : ℕ)
    (hr : Module.finrank ℤ L = r * Module.finrank ℚ K) (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) :
    Nonempty ((Fin r → 𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ≃ₗ[𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}]
      L ⧸ (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hI : Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)} = ⊤ := by simp
    haveI : Subsingleton (𝓞 K ⧸ Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)}) := Ideal.Quotient.subsingleton_iff.mpr hI
    haveI : Subsingleton (L ⧸ (Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
      rw [hI, Submodule.top_smul]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · exact quot_equiv_pi_pos K L r hr ℓ hℓ j hj

theorem isTorsionFree_of_free_int (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] : Module.IsTorsionFree (𝓞 K) L := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c y h => ?_
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  have hmem := Ideal.absNorm_mem (Ideal.span {c})
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
  have hne : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  have : (Ideal.absNorm (Ideal.span {c})) • y = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc', mul_smul, h, smul_zero]
  rw [← Nat.cast_smul_eq_nsmul ℤ] at this
  exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hne)

end GlobalTheory.QuotientCardinalityFinrank

namespace GlobalTheory.QuotientCardinalityFinrank

theorem torsion_points_free : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ j : ℕ, ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) → (Over.mk x ⟶ o.A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ o.A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g := by
  intro p _ D R _ b N S s o k _ _ x ℓ hℓ hℓp j
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, x ≫ s = spMap β :=
    ⟨(Spec.preimage (x ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, -⟩ := o.geom k x β hβ
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  haveI := isTorsionFree_of_free_int D.F D.La
  obtain ⟨e⟩ := quot_equiv_pi D.F D.La (D.m * D.n) D.rankLa ℓ hℓ j
  have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
  have hcop : (ℓ ^ j).Coprime p :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes hℓ (Fact.out : p.Prime)).mpr hℓp)
  set Sub := (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)} • ⊤ : Submodule (𝓞 D.F) D.La) with hSub
  have hmem : ∀ y : D.La, y ∈ Sub ↔ ∃ z, y = (ℓ ^ j) • z := by
    intro y
    rw [hSub, Submodule.ideal_span_singleton_smul]
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Nat.cast_smul_eq_nsmul]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  let φ : D.La →+ Additive (Over.mk x ⟶ o.A) :=
    { toFun := fun y => Additive.ofMul (I.ev (ℓ ^ j) y)
      map_zero' := by
        show Additive.ofMul (I.ev (ℓ ^ j) 0) = Additive.ofMul 1
        rw [(I.ker (ℓ ^ j) hpos hcop 0).mpr ⟨0, by simp⟩]
      map_add' := fun y y' => by
        show Additive.ofMul (I.ev (ℓ ^ j) (y + y')) = Additive.ofMul (I.ev (ℓ ^ j) y * I.ev (ℓ ^ j) y')
        rw [I.add] }
  have hle : Sub.toAddSubgroup ≤ φ.ker := by
    intro y hy
    obtain ⟨z, rfl⟩ := (hmem y).mp hy
    show Additive.ofMul (I.ev (ℓ ^ j) ((ℓ ^ j) • z)) = 0
    rw [(I.ker (ℓ ^ j) hpos hcop _).mpr ⟨z, rfl⟩]
    rfl
  let ψ : D.La ⧸ Sub →+ Additive (Over.mk x ⟶ o.A) := QuotientAddGroup.lift Sub.toAddSubgroup φ hle
  have hψ : ∀ y : D.La, ψ (Submodule.Quotient.mk y) = Additive.ofMul (I.ev (ℓ ^ j) y) := fun y => rfl
  refine ⟨fun a => Additive.toMul (ψ (e a)), ?_, ?_, ?_, ?_⟩
  · intro a a'
    simp only [map_add (f := _), toMul_add]
  · intro c a
    dsimp only
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective Sub (e a)
    rw [map_smul, ← hy, Module.Quotient.mk_smul_mk, hψ, hψ]
    exact I.lin (ℓ ^ j) (algebraMap (𝓞 D.F) D.O c) y
  · intro a a' h
    dsimp only at h
    apply e.injective
    rw [← sub_eq_zero, ← map_sub]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective Sub (e (a - a'))
    have h1 : ψ (e (a - a')) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]
      exact congrArg Additive.ofMul h
    rw [← hy, Submodule.Quotient.mk_eq_zero, hmem]
    rw [← hy, hψ] at h1
    exact (I.ker (ℓ ^ j) hpos hcop y).mp (congrArg Additive.toMul h1)
  · intro g hg
    obtain ⟨y, hy⟩ := (I.onto (ℓ ^ j) hpos hcop g).mp hg
    refine ⟨e.symm (Submodule.Quotient.mk y), ?_⟩
    dsimp only
    rw [LinearEquiv.apply_symm_apply, hψ]
    exact hy

end GlobalTheory.QuotientCardinalityFinrank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowLe
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.KerIdeal

theorem maximalIdeal_pow_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (π : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsMonHom π → IsIsogDeg π d →
    ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀),
    (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      (∃ z : Sp R' ⟶ Sp k, z ≫ (η[B]).left = (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ≫ π.left) ↔
        J ≤ RingHom.ker ψ) →
    ∃ M : ℕ, IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ^ M ≤ J := by
  intro k _ _ A B _ _ _ _ π d hA hB hπ hiso x₀ hx₀ J hJ
  have := hA.smooth
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := hiso.fin
  obtain ⟨s, rfl⟩ := hx₀
  have key : ∀ P : Ideal (A.left.presheaf.stalk ((η[A]).left.base s)), P.IsPrime → J ≤ P →
      P = IsLocalRing.maximalIdeal _ := by
    intro P hP hJP
    haveI := hP
    obtain ⟨z, hz⟩ := (hJ (A.left.presheaf.stalk ((η[A]).left.base s) ⧸ P) (Ideal.Quotient.mk P)).2
      (by rw [Ideal.mk_ker]; exact hJP)
    let q : Sp (A.left.presheaf.stalk ((η[A]).left.base s) ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
    set g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) with hg
    have hgq : g q = ⟨P, hP⟩ := by
      apply PrimeSpectrum.ext
      show Ideal.comap (Ideal.Quotient.mk P) ⊥ = P
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    set x₀ := (η[A]).left.base s with hx₀
    have hy : A.left.fromSpecStalk x₀ (g q) ⤳ x₀ := by
      have : A.left.fromSpecStalk x₀ (g q) ∈ Set.range (A.left.fromSpecStalk x₀) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h1 : π.left.base (A.left.fromSpecStalk x₀ (g q)) = (η[B]).left.base (z q) := by
      have := congrArg (fun m => m.base q) hz
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      exact this.symm
    have h2 : π.left.base x₀ = (η[B]).left.base s := by
      have e : (η[A] ≫ π).left = (η[B]).left := by rw [IsMonHom.one_hom]
      have := congrArg (fun m => m.base s) e
      simpa only [Over.comp_left, Scheme.Hom.comp_base, TopCat.comp_app] using this
    have hzs : z q = s := Subsingleton.elim _ _
    have hyx : A.left.fromSpecStalk x₀ (g q) = x₀ :=
      GlobalTheory.eq_of_specializes_of_isIntegralHom π.left hy (by rw [h1, h2, hzs])
    have hgc : g q = IsLocalRing.closedPoint _ := by
      apply (A.left.fromSpecStalk x₀).isEmbedding.injective
      rw [hyx, Scheme.fromSpecStalk_closedPoint]
    have := congrArg PrimeSpectrum.asIdeal (hgq.symm.trans hgc)
    exact this
  have hrad : IsLocalRing.maximalIdeal _ ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun P ⟨hJP, hP⟩ => (key P hP hJP).ge
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end GlobalTheory.KerIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepEqOfCongMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.DeepSame

theorem deep_eq_of_congMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ a = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, f a κ = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj ct₀ yy₀ hyy₀ a a' ν ν' ha ha' hcong κ
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hU : ((D.q ⁻¹ᵁ U₁ : D.X.M.Z.Opens) : Set D.X.M.Z).Nonempty :=
    GlobalTheory.Poinc.FinPts.preimage_nonempty D.gen hU₁
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have := D.X.normal
    intro x
    exact ⟨inferInstance, inferInstance⟩
  have hfa : f a κ ∈ D.X.M.O z₂ := hf a κ z₂ hz
  have hfa' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  have hb : f a κ - f a' κ ∈ D.X.M.O (ct₀.y (cPt p)) := by
    rw [ct₀.cen]; exact sub_mem hfa hfa'
  have key := GlobalTheory.Poinc.eq_zero_of_val_cen_eq_zero D.X.o₁ D.X.Ω₁ D.X.M hN (D.q ⁻¹ᵁ U₁) hU p ct₀.y
    (f a κ - f a' κ) hb ?_
  · exact sub_eq_zero.1 key
  intro y' hy'
  obtain ⟨hcen, hrange⟩ := hy'
  rw [ct₀.cen] at hcen
  have hr₁ : Set.range (gPt p ≫ (y' ≫ D.q)) ⊆ (U₁ : Set X₁.M.Z) := by
    rintro _ ⟨w, rfl⟩
    exact hrange ⟨w, rfl⟩
  obtain ⟨ct', hct'⟩ := hct (y' ≫ D.q) hr₁
  have hz₁ : (y' ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hcen]; rfl
  let ct₁ : UCTrait X₁ p z₁ :=
    { y := y' ≫ D.q, cen := hz₁, T := ct'.T, ι := ct'.ι, int := ct'.int,
      comm := by have hc := ct'.comm; rw [hct'] at hc; exact hc }
  obtain ⟨yy₁, hyy₁⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct₁
  obtain ⟨yy, hyy, hcomp⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct₁ yy₁ hyy₁ y' rfl
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct₁ y' rfl with cen := hcen }
  have hyy₂ : UIsLabW D.X w₂ ct₂ yy := hyy
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy hyy₀ hyy₂
  have h1 := he a ν ha
  have h2 := he a' ν' ha'
  obtain ⟨w, hw⟩ := hcong
  have hc : CongMod D.m (e ν) (e ν') := ⟨e w, by rw [hw, map_add (f := _), map_nsmul]⟩
  have hfin : ∀ δ : ℝ, 0 < δ → ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ ≤ 2 * δ := by
    intro δ hδ
    obtain ⟨S₀, hS₀⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a (e ν) κ h1 δ hδ
    obtain ⟨S₀', hS₀'⟩ := hsum ct₁ yy₁ hyy₁.uIsLab y' rfl hcen yy hyy.uIsLab hcomp a' (e ν') κ h2 δ hδ
    let S := (S₀ ∪ S₀').filter (fun μ => CongMod D.m μ (e ν))
    have A := hS₀ S (fun μ hμ => (Finset.mem_filter.1 hμ).2)
      (fun μ hμ hc' => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc'⟩)
    have B := hS₀' S
      (fun μ hμ => by
        obtain ⟨w₁', hw₁'⟩ := (Finset.mem_filter.1 hμ).2
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' + w₂', by rw [hw₁', hw₂', smul_add]; abel⟩)
      (fun μ hμ hc' => by
        refine Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, ?_⟩
        obtain ⟨w₁', hw₁'⟩ := hc'
        obtain ⟨w₂', hw₂'⟩ := hc
        exact ⟨w₁' - w₂', by rw [hw₁', hw₂', smul_sub]; abel⟩)
    calc ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖
        = ‖(D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ) -
            (D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ)‖ := by congr 1; abel
      _ ≤ ‖D.X.M.val (gPt p ≫ y') (f a κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ +
            ‖D.X.M.val (gPt p ≫ y') (f a' κ) - ∑ μ ∈ S, t ct₁ yy₁ μ κ‖ := norm_sub_le _ _
      _ ≤ δ + δ := add_le_add A B
      _ = 2 * δ := by ring
  have hxx : D.X.M.val (gPt p ≫ y') (f a κ) = D.X.M.val (gPt p ≫ y') (f a' κ) := by
    by_contra hne
    have hpos : 0 < ‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 hne)
    have := hfin (‖D.X.M.val (gPt p ≫ y') (f a κ) - D.X.M.val (gPt p ≫ y') (f a' κ)‖ / 4) (by positivity)
    linarith
  have hsp : ∀ w, (gPt p ≫ y') w ⤳ z₂ := GlobalTheory.ZH.RatModel.gPt_specializes hcen
  have hadd := GlobalTheory.ZH.RatModel.val_add hsp (sub_mem hfa hfa') hfa'
  rw [sub_add_cancel] at hadd
  rw [hadd] at hxx
  simpa using hxx

end GlobalTheory.UPoinc.DeepSame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfClassSumApprox
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GalLab

theorem eq_of_classSum_approx {X K : Type} [AddCommGroup X] [NormedAddCommGroup K] (m : ℕ) (τ : X → K) (ν ν' : X)
    (h : CongMod m ν ν') (u v : K)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν) →
      (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖u - ∑ μ ∈ S, τ μ‖ ≤ δ)
    (hv : ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset X, ∀ S : Finset X, (∀ μ ∈ S, CongMod m μ ν') →
      (∀ μ ∈ S₀, CongMod m μ ν' → μ ∈ S) → ‖v - ∑ μ ∈ S, τ μ‖ ≤ δ) : u = v := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ μ, CongMod m μ ν ↔ CongMod m μ ν' := fun μ =>
    ⟨fun ⟨x, hx⟩ => ⟨w + x, by rw [hx, hw, smul_add, add_assoc]⟩,
      fun ⟨x, hx⟩ => ⟨x - w, by rw [hx, hw, smul_sub]; abel⟩⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, h₀⟩ := hu (δ / 2) (half_pos hδ)
  obtain ⟨S₁, h₁⟩ := hv (δ / 2) (half_pos hδ)
  have a := h₀ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hc⟩
  have b := h₁ ((S₀ ∪ S₁).filter fun μ => CongMod m μ ν) (fun μ hμ => (key μ).1 (Finset.mem_filter.1 hμ).2)
    fun μ hμ hc => Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, (key μ).2 hc⟩
  have c := norm_sub_le_norm_sub_add_norm_sub u (∑ μ ∈ (S₀ ∪ S₁).filter fun μ => CongMod m μ ν, τ μ) v
  rw [norm_sub_rev] at b
  linarith

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (ct : UCTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), ct.T.P.D.toPre.X → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') → (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) → ∀ (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → IsProjOver D.X.M.s → ∀ (σ' : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), s ≫ D.q = D.q → (∀ (K : Type) [Field K] (y : Sp K ⟶ D.X.M.Z) (b : D.X.Ω₁), D.X.M.val (y ≫ s) b = D.X.M.val y (σ' b)) → s z₂ = z₂ → ∀ aσ : D.X.S.Gam ≃+ D.X.S.Gam, (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → UIsLab D.X (D.lift ct (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (aσ x)) → ∀ (ct₀ : UCTrait D.X p z₂) (yy₀ : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct₀.T.P.D.toPre.X), UIsLabW D.X w₂ ct₀ yy₀ → ∀ (a a' : D.X.S.Gam) (ν ν' : ct₀.T.P.D.toPre.X), yy₀ (aσ a) = QuotientAddGroup.mk ν → yy₀ a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → ∀ κ, σ' (f a κ) = f a' κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D p _ z₁ z₂ hz f t hf hsum w₁ w₂ htie hproj σ' s hs hval hsz aσ haσ ct₀ yy₀ hl₀
    a a' ν ν' ha ha' hνν' κ
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z :=
    fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  have hσ : σ' (f a κ) ∈ D.X.M.O z₂ := by
    letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
      ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
    have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ x =
      algebraMap X₁.Ω₁ D.X.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
    let φ : D.X.Ω₁ →ₐ[X₁.M.Z.presheaf.stalk z₁] D.X.Ω₁ :=
      { (σ' : D.X.Ω₁ →+* D.X.Ω₁) with commutes' := fun x => σ'.commutes (X₁.M.stalkHom z₁ x) }
    exact FinPts.mem_O_of_isIntegral hN D.gen halg
      ((FinPts.isIntegral_of_mem_O D.fin D.gen halg (hf a κ)).map φ) hz
  have hf' : f a' κ ∈ D.X.M.O z₂ := hf a' κ z₂ hz
  obtain ⟨U₁, hU₁, hct⟩ := GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open E H Dw hpq l Xo cf C X₁ p
  have hc₀ := ct₀.cen
  rw [← sub_eq_zero]
  refine eq_zero_of_val_cen_eq_zero _ _ D.X.M hN (D.q ⁻¹ᵁ U₁) (FinPts.preimage_nonempty D.gen hU₁) p ct₀.y _
    (by rw [hc₀]; exact sub_mem hσ hf') fun y hy => ?_
  obtain ⟨hy, hyU⟩ := hy
  rw [hc₀] at hy
  obtain ⟨ct₁, hct₁⟩ := hct (y ≫ D.q) (by
    rintro _ ⟨w, rfl⟩
    exact hyU ⟨w, rfl⟩)
  have hz₁ : (y ≫ D.q) (cPt p) = z₁ := by rw [← hz, ← hy]; rfl
  let ct : UCTrait X₁ p z₁ := { ct₁ with cen := ct₁.cen.trans hz₁ }
  have h : y ≫ D.q = ct.y := hct₁.symm
  have h' : (y ≫ s) ≫ D.q = ct.y := by rw [Category.assoc, hs, h]
  have hys : (y ≫ s) (cPt p) = z₂ := by
    show s (y (cPt p)) = z₂
    rw [hy, hsz]
  obtain ⟨yy₁, hl₁⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ ct
  obtain ⟨yy, hl, hco⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ y h
  obtain ⟨yy', hl', hco'⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ ct yy₁ hl₁ (y ≫ s) h'
  have hyy := haσ ct yy₁ hl₁.uIsLab y h h' yy yy' hl.uIsLab hco hl'.uIsLab hco'
  let ct₂ : UCTrait D.X p z₂ := { D.lift ct y h with cen := hy }
  obtain ⟨d, hd⟩ := exists_linearEquiv_labelled_of_uIsLabW E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ ct₀ ct₂ yy₀ yy
    hl₀ hl
  have hdν : CongMod D.m (d ν) (d ν') := by
    obtain ⟨w, hw⟩ := hνν'
    exact ⟨d w, by rw [hw, map_add (f := _), map_nsmul]⟩
  have e := eq_of_classSum_approx D.m (fun μ => t ct yy₁ μ κ) _ _ hdν _ _
    (hsum ct yy₁ hl₁.uIsLab (y ≫ s) h' hys yy' hl'.uIsLab hco' a (d ν) κ ((hyy a).trans (hd _ _ ha)))
    (hsum ct yy₁ hl₁.uIsLab y h hy yy hl.uIsLab hco a' (d ν') κ (hd _ _ ha'))
  rw [← Category.assoc, hval] at e
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ z₂ := RatModel.gPt_specializes hy
  have e' := map_sub (RatModel.valHomOf _ z₂ hsp) ⟨_, hσ⟩ ⟨_, hf'⟩
  exact e'.trans (sub_eq_zero.2 e)

end GlobalTheory.UPoinc.GalLab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.AtPoint

theorem gm_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  by_cases h : f (r z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val f (r z) U h, gm_val (r ≫ f) z U h]
    exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _
  · have h' : (r ≫ f) z ∉ U := h
    rw [gm, dite_eq_right h, gm, dite_eq_right h']
    simp

theorem val_stalkMap {X Y Y' Z : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)} {ε : Ix → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (g : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map (r.stalkMap z).hom.toMonoidHom (val t g (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ g) z J := by
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalkMap r g z _ _

end GlobalTheory.USep.EvG.AtPoint

open GlobalTheory.USep.EvG.AtPoint in
theorem GlobalTheory.USep.EvG.fromBase_tau_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ _ hk z J J₀ hJ hJ₀ a b
  obtain ⟨-, -, -, -, -, -, hlast⟩ := hFB
  have hJ' : Good D.P.L ((spMap ev) z) (fun ψ => J (spMap ev ≫ ψ)) := fun ψ => hJ (spMap ev ≫ ψ)
  have hJ₀' : Good M₀ ((spMap ev) z) (fun ψ => J₀ (spMap ev ≫ ψ)) := fun ψ => hJ₀ (spMap ev ≫ ψ)
  have E := congrArg (Units.map ((spMap ev).stalkMap z).hom.toMonoidHom) (hlast a b ((spMap ev) z) _ _ hJ' hJ₀')
  simp only [map_mul, map_inv, val_stalkMap, gm_stalkMap, Category.comp_id] at E
  have hg : ∀ x : D.X, gm (spMap ev ≫ UChart.cpt D x) z
      (((M₀.pull β).div D.P.L).U (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x)))
      (w.s (fun _ => J₀ (spMap ev ≫ UChart.cpt D x ≫ β), J (spMap ev ≫ UChart.cpt D x))) =
      GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c x).left) := by
    intro x
    show _ = gw w _ z _ _
    rw [Category.assoc]
    rfl
  rw [hg (a + b), hg a, hg b, hg 0, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp] at E
  obtain ⟨c, hc, hv⟩ := GlobalTheory.Poinc.Sep.val_spMap_mem k₀ (τ₁ a b) (ev.comp ib) hk z hJ₀
  refine ⟨c, hc, ?_⟩
  rw [E, Units.val_mul, hv]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.fromBase_tau_val | exact GlobalTheory.USep.EvG.fromBase_tau_val | (intros; apply GlobalTheory.USep.EvG.fromBase_tau_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG

theorem points_defOver : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (N : ℕ), 1 ≤ N → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N = 1 → ∀ a : D.X,
      DefOver k₀ (spMap ev ≫ b.left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) ∧
        DefOver k₀ (spMap ev ≫ (b * D.c a).left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a * b).left ≫ β) := by
  intro V₁ _ _ _ hV hunit D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hF K _ _ ev k₀ hk₀ hk N hN b hb a
  classical
  obtain ⟨-, -, hβ, -, hc, -, -⟩ := hF
  haveI : IsNoetherianRing V₁ := hV.1
  have hg : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ, hΦ⟩ :=
    GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (spMap ev) (spMap (ev.comp ib)) hg

  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → DefOver k₀ (x.left ≫ β) := by
    intro x hx
    have hNK : (N : K) ≠ 0 := by
      have := ((hunit N (by omega)).map ev).ne_zero
      simpa using this
    have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
    have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range
      fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} => (Φ y.1).left).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    have hσf : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap (ev.comp ib) := by
      have e1 : (σ.toRingHom).comp (ev.comp ib) = ev.comp ib := RingHom.ext fun u => hσ _ (hk u)
      have e0 : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap ((σ.toRingHom).comp (ev.comp ib)) := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e0, e1]
    let hh : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap (ev.comp ib)) := Over.homMk (spMap σ.toRingHom) hσf
    refine ⟨⟨Φ.symm (hh ≫ Φ x), ?_⟩, ?_⟩
    · rw [← map_pow, ← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one, map_one]
    · show (Φ (Φ.symm (hh ≫ Φ x))).left = _
      rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
      rfl

  have hsub : spMap k₀.subtype ≫ spMap ((ev.comp ib).codRestrict k₀ hk) = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  let j : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) :=
    Over.homMk (spMap k₀.subtype) hsub
  have hdesc : ∀ p : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left →
      ∃ p₀ : Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) ⟶ B₀, j ≫ p₀ = p := by
    intro p ⟨P₀, hP₀⟩
    have e : P₀ ≫ B₀.hom = spMap ((ev.comp ib).codRestrict k₀ hk) := spMap_subtype_cancel k₀ (by
      rw [← Category.assoc, hP₀, Over.w p, hsub]; rfl)
    exact ⟨Over.homMk P₀ e, Over.OverMorphism.ext hP₀⟩
  have hmul : ∀ p q : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left → DefOver k₀ q.left →
      DefOver k₀ (p * q).left := by
    intro p q hp hq
    obtain ⟨p₀, rfl⟩ := hdesc p hp
    obtain ⟨q₀, rfl⟩ := hdesc q hq
    rw [← MonObj.comp_mul]
    exact ⟨(p₀ * q₀).left, rfl⟩
  have hprod : ∀ y z : Over.mk (spMap ev) ⟶ D.P.A, DefOver k₀ (y.left ≫ β) → DefOver k₀ (z.left ≫ β) →
      DefOver k₀ ((y * z).left ≫ β) := by
    intro y z hy hz
    rw [← hΦ, map_mul]
    exact hmul _ _ (by rw [hΦ]; exact hy) (by rw [hΦ]; exact hz)

  let h : Over.mk (spMap ev) ⟶ 𝟙_ (Over (Sp V₁)) := Over.homMk (spMap ev) (Category.comp_id _)
  have hl : ∀ y : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, spMap ev ≫ y.left ≫ β = (h ≫ y).left ≫ β := by
    intro y
    rw [Over.comp_left, Category.assoc]
    rfl
  have h1 : DefOver k₀ (spMap ev ≫ b.left ≫ β) := by
    rw [hl]
    exact htor _ (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have h2 : DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) := by
    have e : spMap ev ≫ (D.c a).left ≫ β = spMap (ev.comp ib) ≫ c₀ a := by
      rw [show (D.c a).left ≫ β = spMap ib ≫ c₀ a from hc a, ← Category.assoc, hg]
    rw [e]
    exact defOver_comp k₀ (defOver_spMap k₀ _ hk) _
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h1) (by rw [← hl]; exact h2)
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h2) (by rw [← hl]; exact h1)

end GlobalTheory.USep.EvG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoints_projections_defined_over_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (N : ℕ), 1 ≤ N → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N = 1 → ∀ a : D.X,
      DefOver k₀ (spMap ev ≫ b.left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) ∧
        DefOver k₀ (spMap ev ≫ (b * D.c a).left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a * b).left ≫ β) := by
  first | exact @GlobalTheory.USep.EvG.points_defOver | exact GlobalTheory.USep.EvG.points_defOver | (intros; apply GlobalTheory.USep.EvG.points_defOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfNeConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfNeConj
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_not_and_not_of_sub_closed {A : Type} [AddCommGroup A] (P Q : A → Prop)
    (hP : ∀ a b, P a → P b → P (a - b)) (hQ : ∀ a b, Q a → Q b → Q (a - b)) {a b : A} (ha : ¬ P a) (hb : ¬ Q b) :
    ∃ c, ¬ P c ∧ ¬ Q c := by
  by_cases h1 : Q a
  · by_cases h2 : P b
    · refine ⟨a + b, fun h => ha ?_, fun h => hb ?_⟩
      · simpa using hP _ _ h h2
      · simpa using hQ _ _ h h1
    · exact ⟨b, h2, hb⟩
  · exact ⟨a, ha, h1⟩

theorem mem_map_bar_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E)) (x : 𝓞 E) :
    x ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ↔ H.bar x ∈ 𝔭 := by
  rw [Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) (fun a => ⟨H.bar a, bar_bar H a⟩)]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := bar_bar H a
    simpa [this] using ha
  · exact fun hx => ⟨_, hx, bar_bar H x⟩

theorem mem_of_smul_mem_of_not_mem {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O}
    (hI : I.IsMaximal) (N : Submodule O X) {c : O} (hc : c ∉ I) {x : X} (hx : c • x ∈ N ⊔ I • (⊤ : Submodule O X)) :
    x ∈ N ⊔ I • (⊤ : Submodule O X) := by
  obtain ⟨d, i, hi, hd⟩ := hI.exists_inv hc
  have : x = d • (c • x) + i • x := by rw [smul_smul, ← add_smul, hd, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))

theorem exists_improves_of_ne_conj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  intro E _ _ _ H D X _ _ y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ
  set 𝔭' := 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) with h𝔭'def
  have hmem : ∀ x, x ∈ 𝔭' ↔ H.bar x ∈ 𝔭 := mem_map_bar_iff H 𝔭
  have h𝔭' : 𝔭'.IsMaximal := by
    have : 𝔭' = 𝔭.comap (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.ext fun x => hmem x
    rw [this]
    exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨H.bar a, bar_bar H a⟩)
  have hn' : (n : 𝓞 E) ∈ 𝔭' := (hmem _).2 (by simpa using hn𝔭)
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one (m := 0) (zero_mem _) θ (fun t => by simp [hθ])
  have himg : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ)) = y ∘ₗ (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)) := by
      ext x; simp
    rw [this, LinearMap.range_comp]

  obtain ⟨ℓ₂, hℓ₂⟩ : ∃ ℓ₂, y (ζ ℓ₂) ∉ img D y Z' 𝔭 := by
    obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := SetLike.not_le_iff_exists.1 hZ
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.LowFilt.exists_linear_theta_factor D Z' θ s (fun h0 => hs (h0 ▸ zero_mem _)) hgen z
    have h0 : ζ ℓ - H.bar s • z = 0 := h.symm.eq_zero (sub_mem (hζZ ℓ) (Z.smul_mem _ hz)) fun x hx => by
      rw [ef_swap, map_sub, hζ ℓ ⟨x, hx⟩, hℓ ⟨x, hx⟩]; simp
    refine ⟨ℓ, fun hh => hz' ?_⟩
    rw [sub_eq_zero.1 h0, map_smul] at hh
    exact mem_of_smul_mem_of_not_mem h𝔭 _ hs' hh
  obtain ⟨ℓ', h1, h2⟩ := exists_not_and_not_of_sub_closed (fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => ℓ v₂ ∈ 𝔭')
    (fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭) (fun a b ha hb => sub_mem ha hb)
    (fun a b ha hb => by simpa only [map_sub] using sub_mem ha hb) hℓ₁ hℓ₂
  have he𝔭' : e ∈ 𝔭' := he _ h𝔭' hn' hb
  have he'𝔭 : e' ∈ 𝔭 := he' _ h𝔭 hn𝔭 hb.symm
  set ℓ := e • ℓ₀ + e' • ℓ' with hℓdef
  have hℓx : ∀ x, ℓ x = e * ℓ₀ x + e' * ℓ' x := fun x => rfl
  have hv𝔭 : ℓ v ∉ 𝔭 := fun hh => hℓ₀ (by
    have : ℓ₀ v = ℓ v - (e - 1) * ℓ₀ v - e' * ℓ' v := by rw [hℓx]; ring
    rw [this]
    exact sub_mem (sub_mem hh (𝔭.mul_mem_right _ he1)) (𝔭.mul_mem_right _ he'𝔭))
  have hv𝔭' : ℓ v₂ ∉ 𝔭' := fun hh => h1 (by
    have : ℓ' v₂ = ℓ v₂ - (e' - 1) * ℓ' v₂ - e * ℓ₀ v₂ := by rw [hℓx]; ring
    show ℓ' v₂ ∈ 𝔭'
    rw [this]
    exact sub_mem (sub_mem hh (𝔭'.mul_mem_right _ he1')) (𝔭'.mul_mem_right _ he𝔭'))
  have k𝔭 := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭 h𝔭 (v := v) hv hv𝔭
  have k𝔭' := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭' h𝔭' (v := v₂) hv₂ hv𝔭'
  refine ⟨_, hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => h2 ?_⟩
  · rw [himg, himg']
    by_cases q1 : 𝔮 = 𝔭
    · rw [q1]; exact k𝔭.2
    by_cases q2 : 𝔮 = 𝔭'
    · rw [q2]; exact k𝔭'.2
    exact range_le_of_mem _ _ _ _ fun x => by
      rw [hℓx]
      exact add_mem (𝔮.mul_mem_right _ (he _ h𝔮 hn𝔮 q1)) (𝔮.mul_mem_right _ (he' _ h𝔮 hn𝔮 q2))
  · rw [himg'] at hle
    have hu := hle k𝔭.1
    have b1 : H.bar e ∈ 𝔭 := (hmem _).1 he𝔭'
    have b2 : H.bar e' - 1 ∈ 𝔭 := by simpa using (hmem _).1 he1'
    have : y (ζ ℓ') = y (ζ ℓ) - H.bar e • y (ζ ℓ₀) - (H.bar e' - 1) • y (ζ ℓ') := by
      rw [hℓdef, map_add (f := _), hζs, hζs, map_add (f := _), map_smul, map_smul, sub_smul, one_smul]; abel
    show y (ζ ℓ') ∈ img D y Z' 𝔭
    rw [this]
    exact sub_mem (sub_mem hu (Submodule.mem_sup_right (Submodule.smul_mem_smul b1 trivial)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul b2 trivial))

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfNeConjStatement
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_ne_conj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  first | exact @GlobalTheory.LowFilt.exists_improves_of_ne_conj | exact GlobalTheory.LowFilt.exists_improves_of_ne_conj | (intros; apply GlobalTheory.LowFilt.exists_improves_of_ne_conj <;> assumption)
end
end
end
