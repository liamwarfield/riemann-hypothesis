module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

def TorsionFreeQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (r : ℕ),
      Module.rank R M = r → ∀ a : R, a ≠ 0 →
        Module.length R (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ≤
          (r : ℕ∞) * Module.length R (R ⧸ Ideal.span {a})

def KrullAkizukiQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
      [IsScalarTower R K L] (S : Subalgebra R L) (b : R), b ≠ 0 →
        IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})

end GroundTheory.Heights₂.Heights.Model
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem HeightOneIntersection.proof : HeightOneIntersection.Statement := by
  intro A _ _ _ _ K _ _ _
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf]
    intro p _
    exact ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, by rwa [one_smul]⟩
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    change x ∈ (⊥ : Subalgebra A K)
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := K) x
      (fun p hp h1 => by
        obtain ⟨s, hs, hsx⟩ := hx ⟨p, hp⟩ h1
        change s • x ∈ (⊥ : Subalgebra A K) at hsx
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
        refine ⟨a, s, hs, ?_⟩
        rw [Algebra.smul_def] at ha
        rw [ha, mul_comm])
    exact ⟨y, hy⟩

end GroundTheory.Heights₂.Heights.Model
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

theorem exists_ne_zero_smul_mem_of_span_eq_top (M : Submodule A V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ d : A, d ≠ 0 ∧ d • v ∈ M :=
  _root_.UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top M hM v

theorem mem_of_forall_mem_localizedIn (hHOI : HeightOneIntersection.Statement)
    [IsNoetherianRing A] [IsIntegrallyClosed A] (M : Submodule A V) [Module.Projective A M]
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V)
    (hv : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → v ∈ localizedIn p.asIdeal M) : v ∈ M := by
  obtain ⟨d, hd, hdv⟩ := exists_ne_zero_smul_mem_of_span_eq_top (K := K) M hM v
  obtain ⟨c, hc⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  set x : M := ⟨d • v, hdv⟩ with hx
  have hdK : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd

  have hdiv : ∀ y : M, ∃ a : A, c x y = d * a := by
    intro y
    have hq : algebraMap A K (c x y) / algebraMap A K d ∈
        Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
      rw [hHOI A K]
      simp only [Submodule.mem_iInf]
      intro p hp
      obtain ⟨s, hs, hsv⟩ := hv p hp
      refine ⟨s, hs, ?_⟩
      set x' : M := ⟨s • v, hsv⟩
      have hxx : d • x' = s • x := by
        ext; simp only [x', hx, SetLike.val_smul, smul_smul, mul_comm]
      have hcc : d * c x' y = s * c x y := by
        have := congrArg (fun z => c z y) hxx
        simpa [map_smul] using this
      refine Algebra.mem_bot.mpr ⟨c x' y, ?_⟩
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, ← hcc, map_mul,
        mul_div_right_comm, div_self hdK, one_mul]
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hq
    refine ⟨a, IsFractionRing.injective A K ?_⟩
    rw [map_mul, ha, mul_div_cancel₀ _ hdK]
  choose a ha using hdiv
  have hw : (∑ y ∈ (c x).support, a y • (y : V)) ∈ M :=
    M.sum_mem fun y _ => M.smul_mem (a y) y.2
  have hsum : d • v = d • ∑ y ∈ (c x).support, a y • (y : V) := by
    have h1 : ((Finsupp.linearCombination A id (c x) : M) : V) = d • v := by rw [hc x]
    rw [← h1, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Submodule.coe_smul, id, ha y, mul_smul]
  have hvw : v = ∑ y ∈ (c x).support, a y • (y : V) := by
    rw [← algebraMap_smul K d v, ← algebraMap_smul K d (∑ y ∈ (c x).support, a y • (y : V))]
      at hsum
    exact smul_right_injective V hdK hsum
  rw [hvw]
  exact hw

theorem LatticesAgree.proof (hHOI : HeightOneIntersection.Statement) : LatticesAgree.Statement := by
  intro A _ _ _ _ K _ _ _ V _ _ _ _ _ M N _ hMp _ hNp hM hN hMN
  have sub : ∀ (P Q : Submodule A V), Module.Projective A P →
      Submodule.span K (P : Set V) = ⊤ →
      (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 →
        localizedIn p.asIdeal Q = localizedIn p.asIdeal P) → Q ≤ P := by
    intro P Q hP hPs hQP v hvQ
    exact mem_of_forall_mem_localizedIn (K := K) hHOI P hPs v fun p hp =>
      hQP p hp ▸ ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hvQ⟩
  exact le_antisymm (sub N M hNp hN fun p hp => hMN p hp)
    (sub M N hMp hM fun p hp => (hMN p hp).symm)

end GroundTheory.Heights₂.Heights.Model
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharP
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.Model

theorem module_finite_of_semilinear {B R M N : Type*} [CommRing B] [CommRing R] [Algebra R B]
    [IsNoetherianRing R] [Module.Finite R B] [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] [Module R N] [IsScalarTower R B N] [Module.Finite B N]
    (σ : B →+* R) (hσ : Function.Surjective σ) (φ : M →+ N) (hφ : Function.Injective φ)
    (hφσ : ∀ (b : B) (m : M), φ (b • m) = σ b • φ m) : Module.Finite B M := by
  have : Module.Finite R N := Module.Finite.trans B N
  have : IsNoetherian R N := isNoetherian_of_isNoetherianRing_of_finite R N
  let P : Submodule R N :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, map_add φ x y⟩
      zero_mem' := ⟨0, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, hφσ b x⟩ }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
  have hsP : ∀ n ∈ s, ∃ m, φ m = n := fun n hn => by
    have : n ∈ P := hs ▸ Submodule.subset_span hn
    exact this
  choose! g hg using hsP
  classical
  refine ⟨⟨s.image g, ?_⟩⟩
  rw [eq_top_iff]
  rintro m -
  let Q : Submodule B M := Submodule.span B (s.image g : Set M)
  let Q' : Submodule R N :=
    { carrier := φ '' Q
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, Q.add_mem hx hy, map_add φ x y⟩
      zero_mem' := ⟨0, Q.zero_mem, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, hx, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, Q.smul_mem b hx, hφσ b x⟩ }
  have hsQ' : (s : Set N) ⊆ Q' := by
    intro n hn
    refine ⟨g n, Submodule.subset_span ?_, hg n hn⟩
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem g hn)
  have hPQ : P ≤ Q' := hs ▸ Submodule.span_le.mpr hsQ'
  obtain ⟨m', hm', he⟩ := hPQ (⟨m, rfl⟩ : φ m ∈ P)
  exact hφ he ▸ hm'

theorem mvPolynomial_finite_frobenius_range (p : ℕ) [Fact p.Prime] (s e : ℕ) :
    Module.Finite (iterateFrobenius (MvPolynomial (Fin s) (ZMod p)) p e).range
      (MvPolynomial (Fin s) (ZMod p)) := by
  set B := MvPolynomial (Fin s) (ZMod p)
  set R := (iterateFrobenius B p e).range
  have hpow : ∀ x : B, x ^ p ^ e ∈ R := fun x => ⟨x, by rw [iterateFrobenius_def]⟩
  have hint : Algebra.IsIntegral R B := ⟨fun x => by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero e (Fact.out : p.Prime).ne_zero)) ?_
    have : x ^ p ^ e = algebraMap R B ⟨x ^ p ^ e, hpow x⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap⟩
  have hft : Algebra.FiniteType R B := by
    refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
    rw [eq_top_iff]
    rintro f -
    induction f using MvPolynomial.induction_on with
    | C a =>
      have : MvPolynomial.C a = algebraMap R B ⟨MvPolynomial.C a, ⟨MvPolynomial.C a, by
        rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]⟩⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add f g hf hg => exact Subalgebra.add_mem _ hf hg
    | mul_X f i hf =>
      refine Subalgebra.mul_mem _ hf (Algebra.subset_adjoin ?_)
      simp
  exact Algebra.IsIntegral.finite

theorem finite_integralClosure_mvPolynomial (p : ℕ) [Fact p.Prime] (s : ℕ)
    (F : Type*) [Field F] [Algebra (MvPolynomial (Fin s) (ZMod p)) F]
    [IsFractionRing (MvPolynomial (Fin s) (ZMod p)) F]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra (MvPolynomial (Fin s) (ZMod p)) L]
    [IsScalarTower (MvPolynomial (Fin s) (ZMod p)) F L] :
    Module.Finite (MvPolynomial (Fin s) (ZMod p))
      (integralClosure (MvPolynomial (Fin s) (ZMod p)) L) := by
  set B := MvPolynomial (Fin s) (ZMod p)
  have hp : p.Prime := Fact.out
  have hinjBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective B F)
  have : CharP L p :=
    charP_of_injective_ringHom (f := (algebraMap B L).comp MvPolynomial.C)
      (hinjBL.comp (MvPolynomial.C_injective (Fin s) (ZMod p))) p
  set Ls := separableClosure F L
  have : ExpChar Ls p := ExpChar.prime hp
  have : IsScalarTower B Ls L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B F L, IsScalarTower.algebraMap_apply B F Ls,
      IsScalarTower.algebraMap_apply F Ls L]
  have : IsPurelyInseparable Ls L := separableClosure.isPurelyInseparable F L
  set e := IsPurelyInseparable.exponent Ls L
  let fr : L →+* Ls := IsPurelyInseparable.iterateFrobenius Ls L p (le_refl e)
  have hfr : ∀ y, algebraMap Ls L (fr y) = y ^ p ^ e := fun y =>
    IsPurelyInseparable.algebraMap_iterateFrobenius Ls p (le_refl e) y
  have hinjLs : Function.Injective (algebraMap Ls L) := (algebraMap Ls L).injective
  have : Algebra.IsSeparable F Ls := separableClosure.isSeparable F L
  have : Module.Finite B (integralClosure B Ls) :=
    IsIntegralClosure.finite B F Ls (integralClosure B Ls)
  have := mvPolynomial_finite_frobenius_range p s e
  have hint : ∀ y : integralClosure B L, IsIntegral B (fr y) := fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom B Ls L) hinjLs).mp (by
      rw [IsScalarTower.toAlgHom_apply, hfr]
      exact y.2.pow _)
  let φ : integralClosure B L →+ integralClosure B Ls :=
    { toFun := fun y => ⟨fr y, hint y⟩
      map_zero' := by ext; simp
      map_add' := fun y z => by ext; simp }
  refine module_finite_of_semilinear (iterateFrobenius B p e).rangeRestrict
    (iterateFrobenius B p e).rangeRestrict_surjective φ ?_ ?_
  · intro y z h
    have h' : fr y = fr z := congrArg Subtype.val h
    exact Subtype.ext (fr.injective h')
  · intro b y
    apply Subtype.ext
    apply hinjLs
    change algebraMap Ls L (fr (b • (y : L))) =
      algebraMap Ls L (((iterateFrobenius B p e b : B) • fr y))
    rw [hfr, Algebra.smul_def, Algebra.smul_def, map_mul, hfr, iterateFrobenius_def, mul_pow,
      ← map_pow, ← IsScalarTower.algebraMap_apply]

theorem finite_integralClosure_of_charP (p : ℕ) [Fact p.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [CharP A p]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by
  let : Algebra (ZMod p) A := ZMod.algebra A p
  have : Algebra.FiniteType (ZMod p) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) A
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) A
  set B := MvPolynomial (Fin s) (ZMod p)
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hgfin
  let : Algebra B K := ((algebraMap A K).comp (algebraMap B A)).toAlgebra
  let : Algebra B L := ((algebraMap A L).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))
    exact IsScalarTower.algebraMap_apply A K L _
  have hinjBK : Function.Injective (algebraMap B K) :=
    (IsFractionRing.injective A K).comp hginj
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK
  let : Algebra (FractionRing B) K := FractionRing.liftAlgebra B K
  let : Algebra (FractionRing B) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra
  have : IsScalarTower (FractionRing B) K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B (FractionRing B) L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing B) K L,
      ← IsScalarTower.algebraMap_apply B (FractionRing B) K,
      ← IsScalarTower.algebraMap_apply B K L]
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FiniteDimensional (FractionRing B) K := by
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B A).FG)
    let T : Set K := algebraMap A K '' t
    have hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x := by
      rintro _ ⟨a, -, rfl⟩
      have : IsIntegral B (algebraMap A K a) :=
        (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)
      exact this.tower_top
    have : Finite T := (t.finite_toSet.image _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing B) T = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T := by
        intro a
        have ha : a ∈ Submodule.span B (t : Set A) := ht ▸ Submodule.mem_top
        induction ha using Submodule.span_induction with
        | mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
        | smul b y _ hy =>
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply B (FractionRing B) K]
          exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional
  have : FiniteDimensional (FractionRing B) L := Module.Finite.trans K L
  have hB := finite_integralClosure_mvPolynomial p s (FractionRing B) L
  have hle : (integralClosure A L).toSubmodule.restrictScalars B ≤
      (integralClosure B L).toSubmodule := fun y hy => isIntegral_trans (R := B) (A := A) y hy
  have : IsNoetherian B (integralClosure B L).toSubmodule :=
    isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)
  have : IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B) :=
    isNoetherian_of_le hle
  have : Module.Finite B (integralClosure A L) :=
    Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)

end GroundTheory.Heights₂.Heights.Model
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem FiniteIntegralClosure.proof : FiniteIntegralClosure.Statement := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists A
  rcases CharP.char_is_prime_or_zero A p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_of_charP p A K L
  · have : CharZero A := CharP.charP_to_charZero A
    exact finite_integralClosure_of_charZero A K L

end GroundTheory.Heights₂.Heights.Model
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open IsLocalRing

theorem BlowUpChart.proof : BlowUpChart.Statement := by
  intro A _ _ _ _ K _ _ _ n x hx ⟨j, hj⟩
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A K)
  set f := (algebraMap A K).codRestrict V.toSubring hV with hf
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun k => V.valuation (algebraMap A K (x k))
  have hinj := IsFractionRing.injective A K
  have hxi : x i ≠ 0 := by
    intro h0
    apply hj
    have h1 := hi j
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (by rw [h1, map_zero])
  have hvi : 0 < V.valuation (algebraMap A K (x i)) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact fun h => hxi (hinj (by rw [h, map_zero]))
  have hle : ∀ y ∈ blowUpChart K x i, y ∈ V := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hvi]
      exact hi k
    | algebraMap r => exact hV r
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
  let φ : blowUpChart K x i →+* V :=
    { toFun := fun y => ⟨y.1, hle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ a : A, φ (algebraMap A (blowUpChart K x i) a) = f a := fun _ => rfl
  have hxm : x i ∈ maximalIdeal A := hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have hnu : ¬ IsUnit (f (x i)) := by
    rw [isUnit_map_iff f]
    exact hxm
  refine ⟨i, hxi, fun hu => hnu (hφ (x i) ▸ hu.map φ), (maximalIdeal V).comap φ,
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · rw [Ideal.mem_comap, hφ]
    exact hnu
  · ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ, mem_maximalIdeal, mem_nonunits_iff,
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f]

end GroundTheory.Heights₂.Heights.Model
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open Real

lemma div_le_padicValNat_factorial (N p : ℕ) (hp : p.Prime) :
    N / p ≤ padicValNat p N.factorial := by
  have := Fact.mk hp
  rcases lt_or_ge N p with h | h
  · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
  · rw [Nat.padicValNat_def, multiplicity_factorial (b := Nat.log p N + 1) (Nat.lt_succ_self _)]
    have h1 : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := by
      have := Nat.log_pos hp.one_lt h
      simp only [Finset.mem_Ico]; omega
    have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this

lemma prod_pow_div_dvd_factorial (N : ℕ) :
    (∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p)) ∣ N.factorial := by
  have : ((∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℤ) ∣ (N.factorial : ℤ) := by
    push_cast
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simp only [Function.onFun]
      exact_mod_cast Nat.isCoprime_iff_coprime.2 (Nat.coprime_pow_primes _ _ hp' hq' hpq)
    · intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      exact_mod_cast (pow_dvd_pow p (div_le_padicValNat_factorial N p hp')).trans
        (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  exact_mod_cast this

theorem MertensUpper.proof : MertensUpper.Statement := by
  refine ⟨Real.log 4, fun B hB => ?_⟩
  set N := ⌊B⌋₊ with hN
  set P := (Finset.Iic N).filter Nat.Prime with hP
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hB)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNB : (N : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hpos : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le

  have hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (prod_pow_div_dvd_factorial N)).trans
      (Nat.factorial_le_pow N)
  have hlog : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have hprod : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) ^ (N / p)) :=
      Finset.prod_pos fun p hp => pow_pos (by linarith [hpos p hp]) _
    have h := Real.log_le_log hprod
      (show ∏ p ∈ P, ((p : ℝ) ^ (N / p)) ≤ (N : ℝ) ^ N by exact_mod_cast hle)
    rw [Real.log_prod (fun p hp => (pow_pos (by linarith [hpos p hp]) _).ne'),
      Real.log_pow] at h
    simpa [Real.log_pow] using h

  have hfloor : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p :=
    fun p hp => mul_le_mul_of_nonneg_right
      (by rw [← Nat.floor_div_eq_div (K := ℝ)]; exact (Nat.sub_one_lt_floor _).le)
      (Real.log_nonneg (hpos p hp))

  have htheta : ∑ p ∈ P, Real.log p ≤ Real.log 4 * N := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le
    have hset : P = (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast, hP]
      ext p
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hset]; exact h
  have key : (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p ≤ N * Real.log N := by
    calc (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p
        = ∑ p ∈ P, ((N : ℝ) / p - 1) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p := Finset.sum_le_sum hfloor
      _ ≤ N * Real.log N := hlog
  have hS : ∑ p ∈ P, Real.log p / p ≤ Real.log N + Real.log 4 := by
    have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
      rw [mul_add]; linarith
    exact le_of_mul_le_mul_left this hNpos
  have hlogNB : Real.log N ≤ Real.log B := Real.log_le_log hNpos hNB
  linarith

end GroundTheory.Heights₂.Heights.Model
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem isFractionRing_of_subalgebra {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (B : Subalgebra A K) : IsFractionRing B K := by
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
  · have hy : (y : B) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    exact isUnit_iff_ne_zero.2 fun h => hy (Subtype.ext h)
  · obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) z
    have hs : algebraMap A B s ≠ 0 := fun h0 =>
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2 (congrArg Subtype.val h0)
    exact ⟨⟨algebraMap A B a, ⟨_, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, h⟩
  · simpa using Subtype.ext h


set_option maxHeartbeats 400000 in
theorem DominatingDVR.proof (hKA : KrullAkizuki.Statement) (hBU : BlowUpChart.Statement) :
    DominatingDVR.Statement := by
  intro A _ _ _ _ hAf K _ _ _

  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))
  have hx' : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A := hx
  have hx0 : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hAf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hx']
    exact Submodule.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  obtain ⟨i, hxi, hunit, -⟩ := hBU A K n x hx' hx0

  set B := blowUpChart K x i
  have : IsNoetherianRing B :=
    isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  have : IsFractionRing B K := isFractionRing_of_subalgebra B

  set xi : B := algebraMap A B (x i)
  have hspan : Ideal.span {xi} ≠ ⊤ := fun h => hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hspan
  have : q.IsPrime := hq.1.1
  have hxiq : xi ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hxi0 : xi ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by
    simpa [xi] using congrArg Subtype.val h))
  have hq1 : q.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hxi0)).trans (Ideal.height_mono hq.1.2))
  have hmq : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ q := by
    rw [← hx', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have e : algebraMap A B (x j) =
        ⟨algebraMap A K (x j) / algebraMap A K (x i), Algebra.subset_adjoin ⟨j, rfl⟩⟩ * xi := by
      apply Subtype.ext
      have : algebraMap A K (x i) ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by simpa using h))
      simp [xi, div_mul_cancel₀ _ this]
    exact e ▸ q.mul_mem_left _ hxiq

  set R := Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsLocalization.AtPrime R q := (inferInstance : IsLocalization q.primeCompl R)
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  have hdimR : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q R, hq1]
    rfl

  set C := integralClosure R K
  have : IsDedekindDomain C := hKA.2 R hdimR K
  have : IsFractionRing C K := isFractionRing_of_subalgebra C
  have hinj : Function.Injective (algebraMap R C) := fun a b h =>
    by
    have h' : ((algebraMap R C a : C) : K) = ((algebraMap R C b : C) : K) := congrArg _ h
    exact IsFractionRing.injective R K h'
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal R) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    have hF : IsField R := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hPc, Ideal.under_def, Ideal.comap_bot_of_injective _ hinj]
    have h0 := ringKrullDim_eq_zero_of_isField hF
    rw [hdimR] at h0
    exact one_ne_zero h0

  set V := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  letI : CommRing V := Subalgebra.toCommRing (R := C) (A := K) V
  have : IsDomain V := Subalgebra.isDomain (R := C) (A := K) V
  have : IsLocalization.AtPrime V P := (inferInstance : IsLocalization P.primeCompl V)
  have hV : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot V
  let φ : A →+* V :=
    (algebraMap C V).comp ((algebraMap R C).comp ((algebraMap B R).comp (algebraMap A B)))
  have hφ : ∀ a, (φ a : K) = algebraMap A K a := fun a => rfl
  refine ⟨Subalgebra.toSubring (R := C) V, hV, fun a => ?_, fun a => ?_⟩
  · show algebraMap A K a ∈ V
    exact hφ a ▸ (φ a).2
  show ¬ IsUnit (φ a) ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h ha => h (ha.map φ), fun ha hu => ?_⟩
  have hb : algebraMap A B a ∈ q := hmq (Ideal.mem_map_of_mem _ (by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]))
  have hr : algebraMap B R (algebraMap A B a) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R q _).mpr hb
  rw [← hPc, Ideal.mem_comap] at hr
  exact (IsLocalization.AtPrime.isUnit_to_map_iff V P _).mp hu hr

end GroundTheory.Heights₂.Heights.Model
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

theorem FiniteIntegralClosure.alg_iff :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
      (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
      Module.Finite A (integralClosure A L)) ↔
    (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
      [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
      [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :=
  ⟨fun h A K L _ _ _ _ _ _ _ _ _ _ _ => h A K L, fun h A _ _ _ K _ _ _ L _ _ _ _ _ => h A K L⟩

theorem finiteType_sections_of_isFiniteTypeOverZ {X : Scheme.{0}} (hX : IsFiniteTypeOverZ X)
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have := hX.1
  have h1 := (toSpecZ X).finiteType_appLE (isAffineOpen_top (Spec (.of ℤ))) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2
  have h3 := h1.comp h2
  rw [show ((toSpecZ X).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom =
    algebraMap ℤ Γ(X, U) from RingHom.ext_int _ _] at h3
  exact RingHom.finiteType_algebraMap.mp h3

theorem FiniteIntegralClosure.scheme_of_alg
    (h : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K]
      [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :
    ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        letI := hU
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) := by
  intro X _ hX L _ _ _ U hUa hU
  have := hU
  have := finiteType_sections_of_isFiniteTypeOverZ hX hUa
  have := functionField_isFractionRing_of_isAffineOpen X U hUa
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h Γ(X, U) X.functionField L

theorem genericSpecMap_closedPoint (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] :
    _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) =
      genericPoint Z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
      (IsLocalRing.closedPoint (CommRingCat.of L)) = IsLocalRing.closedPoint Z.functionField :=
    Spec_closedPoint
  exact (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
    (Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint (CommRingCat.of L))).trans
    (h ▸ Scheme.fromSpecStalk_closedPoint)

theorem genericSpecMap_app_iso (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] (U : Z.Opens) (hη : genericPoint Z ∈ U)
    (hmem : _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) ∈ U) :
    (_root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L).app U ≫
      ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      Z.presheaf.germ U (genericPoint Z) hη ≫ CommRingCat.ofHom (algebraMap Z.functionField L) := by
  have h := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (CommRingCat.ofHom (algebraMap Z.functionField L)) U hmem
  exact (Scheme.germ_stalkClosedPointTo _ U hmem).symm.trans h

theorem FiniteIntegralClosure.normalization_of_scheme
    (h : ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        letI := hU
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L)) :
    _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement := by
  intro Z _ f _ _ L _ _ _
  have e : f = toSpecZ Z := specZ_hom_ext _ _
  have hX : IsFiniteTypeOverZ Z := ⟨e ▸ ‹LocallyOfFiniteType f›, e ▸ ‹QuasiCompact f›⟩
  set g := _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L with hg
  refine { finite_app := fun U hU => ?_ }
  let := (g.app U).hom.toAlgebra
  rw [g.fromNormalization_app hU, CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (g.normalizationObjIso hU).inv).2
  refine RingHom.finite_algebraMap.2 ?_
  rcases isEmpty_or_nonempty U with hU0 | hU0
  · have hb : U = ⊥ := SetLike.coe_injective (by simpa using Set.isEmpty_coe_sort.mp hU0)
    subst hb
    have : Subsingleton (integralClosure Γ(Z, ⊥) Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ ⊥)) :=
      Module.subsingleton Γ(Z, ⊥) _
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU0)
  have hmem : g (IsLocalRing.closedPoint L) ∈ U := by
    rw [hg, genericSpecMap_closedPoint]; exact hη
  have key := genericSpecMap_app_iso Z L U hη hmem
  let : Algebra Γ(Z, U) L :=
    ((algebraMap Z.functionField L).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra
  let eR := ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ U) ≃ₐ[Γ(Z, U)] L :=
    AlgEquiv.ofRingEquiv (f := eR) fun x => congrArg (fun φ => φ.hom x) key
  have hfin := h Z hX L U hU hU0
  exact Module.Finite.equiv eA.mapIntegralClosure.symm.toLinearEquiv

theorem FiniteIntegralClosure.equiv :
    (_root_.GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement) ↔
    FiniteIntegralClosure.Statement := by
  constructor
  · rintro ⟨ha, -⟩
    have hb := FiniteIntegralClosure.alg_iff.mp ha
    exact ⟨hb, FiniteIntegralClosure.scheme_of_alg hb⟩
  · rintro ⟨hb, hs⟩
    exact ⟨FiniteIntegralClosure.alg_iff.mpr hb, FiniteIntegralClosure.normalization_of_scheme hs⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end
