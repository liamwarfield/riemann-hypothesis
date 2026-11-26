module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnIdempotentSplits
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnIdempotentSplits
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.IdemSplit

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G]
  (i : H ⟶ G) (r : G ⟶ H) (hir : i ≫ r = 𝟙 H) [he : IsMonHom (r ≫ i)]

include hir in
theorem sec_idem : i ≫ r ≫ i = i := by rw [reassoc_of% hir]

theorem one_comp : (η[G] ≫ r) ≫ i = η[G] := by
  rw [Category.assoc, IsMonHom.one_hom]

include hir in
theorem mul_comp : ((i ⊗ₘ i) ≫ μ[G] ≫ r) ≫ i = (i ⊗ₘ i) ≫ μ[G] := by
  rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
    sec_idem i r hir]

include hir in
theorem inv_comp : (i ≫ GrpObj.inv ≫ r) ≫ i = i ≫ GrpObj.inv := by
  rw [Category.assoc, Category.assoc, GrpObj.inv_hom, ← Category.assoc, sec_idem i r hir]

@[reducible] def grpObj : GrpObj H :=
  haveI : Mono i := (SplitMono.mk r hir).mono
  { one := η[G] ≫ r
    mul := (i ⊗ₘ i) ≫ μ[G] ≫ r
    one_mul := by
      rw [← cancel_mono i, Category.assoc, mul_comp i r hir, ← tensorHom_id,
        tensorHom_comp_tensorHom_assoc, one_comp, Category.id_comp, tensorHom_def'_assoc,
        MonObj.one_mul, leftUnitor_naturality]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, mul_comp i r hir, ← id_tensorHom,
        tensorHom_comp_tensorHom_assoc, one_comp, Category.id_comp, tensorHom_def_assoc,
        MonObj.mul_one, rightUnitor_naturality]
    mul_assoc := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (α_ H H H).hom, Category.assoc (H ◁ _),
        mul_comp i r hir, ← id_tensorHom, ← tensorHom_id,
        tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, mul_comp i r hir,
        Category.id_comp]
      have h1 : ((i ⊗ₘ i) ≫ μ[G]) ⊗ₘ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[G] ▷ G := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
      have h2 : i ⊗ₘ ((i ⊗ₘ i) ≫ μ[G]) = (i ⊗ₘ (i ⊗ₘ i)) ≫ G ◁ μ[G] := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc]
    inv := i ≫ GrpObj.inv ≫ r
    left_inv := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (toUnit H), mul_comp i r hir, one_comp,
        lift_map_assoc, inv_comp i r hir, Category.id_comp]
      have := GrpObj.left_inv G
      have h2 := congrArg (i ≫ ·) this
      simpa using h2
    right_inv := by
      rw [← cancel_mono i, Category.assoc, Category.assoc (toUnit H), mul_comp i r hir, one_comp,
        lift_map_assoc, inv_comp i r hir, Category.id_comp]
      have := GrpObj.right_inv G
      have h2 := congrArg (i ≫ ·) this
      simpa using h2 }

theorem isMonHom_sec : letI := grpObj i r hir; IsMonHom i :=
  letI := grpObj i r hir
  { one_hom := one_comp i r
    mul_hom := mul_comp i r hir }

theorem isMonHom_ret : letI := grpObj i r hir; IsMonHom r :=
  letI := grpObj i r hir
  { one_hom := rfl
    mul_hom := by
      haveI : Mono i := (SplitMono.mk r hir).mono
      change μ[G] ≫ r = (r ⊗ₘ r) ≫ (i ⊗ₘ i) ≫ μ[G] ≫ r
      rw [← cancel_mono i, Category.assoc, Category.assoc (r ⊗ₘ r), mul_comp i r hir,
        tensorHom_comp_tensorHom_assoc, IsMonHom.mul_hom] }

theorem isComm [BraidedCategory C] [IsCommMonObj G] : letI := grpObj i r hir; IsCommMonObj H :=
  letI := grpObj i r hir
  { mul_comm := by
      change (β_ H H).hom ≫ (i ⊗ₘ i) ≫ μ[G] ≫ r = (i ⊗ₘ i) ≫ μ[G] ≫ r
      rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc] }

end General

end GlobalTheory.SS.IdemSplit

namespace GlobalTheory.SS

theorem smConn_idempotent_splits : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], SmConn G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (G₁ : Over S) (_ : GrpObj G₁) (i : G₁ ⟶ G) (r : G ⟶ G₁), SmConn G₁ ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 G₁ ∧ r ≫ i = e := by
  intro S G _ hG e he hee
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  let i := equalizer.ι e (𝟙 G)
  let r : G ⟶ equalizer e (𝟙 G) := equalizer.lift e (by simp [hee])
  have hri : r ≫ i = e := equalizer.lift_ι _ _
  have hir : i ≫ r = 𝟙 _ := by
    rw [← cancel_mono i, Category.assoc, hri, Category.id_comp]
    simpa using equalizer.condition e (𝟙 G)
  haveI : IsMonHom (r ≫ i) := by rw [hri]; exact he
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hw := Over.w r
  exact ⟨_, IdemSplit.grpObj i r hir, i, r,
    ⟨IdemSplit.isComm i r hir, GlobalTheory.Retract.smooth hl hw, GlobalTheory.Retract.isSeparated hl hw,
      GlobalTheory.Retract.quasiCompact hl hw, GlobalTheory.Retract.geometricallyConnected hl hw⟩,
    IdemSplit.isMonHom_sec i r hir, IdemSplit.isMonHom_ret i r hir, hir, hri⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnIdempotentSplitsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_retract_of_smConn_idempotent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], SmConn G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (G₁ : Over S) (_ : GrpObj G₁) (i : G₁ ⟶ G) (r : G ⟶ G₁), SmConn G₁ ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 G₁ ∧ r ≫ i = e := by
  first | exact @GlobalTheory.SS.smConn_idempotent_splits | exact GlobalTheory.SS.smConn_idempotent_splits | (intros; apply GlobalTheory.SS.smConn_idempotent_splits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalizationOfLeClosure
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.CycAway
open NumberField

theorem isLocalization_of_le_closure {Ω : Type} [Field Ω] {n : ℕ} (h0 : (n : Ω) ≠ 0) (A : Type) [CommRing A]
    (T : Subring Ω) [Algebra A T] (hinj : Function.Injective (algebraMap A T)) (hinv : (n : Ω)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹})) :
    IsLocalization (Submonoid.powers (n : A)) T := by
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹}),
      ∃ m : ℕ, ∃ a, z * (n : Ω) ^ m = (algebraMap A T a : Ω) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | rfl
      · exact ⟨0, a, by simp⟩
      · exact ⟨1, 1, by simp [h0]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * n ^ k + b * n ^ m, ?_⟩
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, a, ha⟩ := hx
      refine ⟨m, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    simp only [map_pow, map_natCast]
    refine IsUnit.pow _ (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    simp [h0]
  · intro z
    obtain ⟨m, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨_, m, rfl⟩), Subtype.ext ?_⟩
    simp only [map_pow, map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem dedekind_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n a : ℕ} (hn : n.Prime)
    [IsCyclotomicExtension {n ^ a} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ a)) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) ∧ Algebra.FiniteType ℤ (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI := Fact.mk hn
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne_zero
  refine ⟨IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _, ?_⟩
  have h1 : Algebra.FiniteType ℤ (𝓞 K) := inferInstance
  have h2 : Algebra.FiniteType (𝓞 K) T :=
    have := IsLocalization.Away.finitePresentation (S := T) (n : 𝓞 K)
    inferInstance
  exact h1.trans h2

theorem exists_base : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n a : ℕ), n.Prime → ∃ (o : Subring Ω) (ze : oˣ), IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧ IsUnit (n : o) ∧ IsPrimitiveRoot (Units.map o.subtype.toMonoidHom ze) (n ^ a) ∧ o = Subring.closure {((ze : o) : Ω), (n : Ω)⁻¹} := by
  intro Ω _ _ _ n a hn
  haveI := Fact.mk hn
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  let K := CyclotomicField (n ^ a) ℚ
  haveI : IsCyclotomicExtension {n ^ a} ℚ K := CyclotomicField.isCyclotomicExtension (n ^ a) ℚ
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  let φ : K →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := K) (M := Ω)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec (n ^ a) ℚ K
  set ζ := IsCyclotomicExtension.zeta (n ^ a) ℚ K
  obtain ⟨hD, hF⟩ := dedekind_closure hn φ hζ
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  have hz : IsPrimitiveRoot (φ ζ) (n ^ a) := hζ.map_of_injective φ.injective
  let z : T := ⟨φ ζ, Subring.subset_closure (Or.inl rfl)⟩
  have hz' : IsPrimitiveRoot z (n ^ a) := IsPrimitiveRoot.of_map_of_injective (f := T.subtype) hz T.subtype_injective
  have hu : IsUnit z := hz'.isUnit (NeZero.ne _)
  refine ⟨T, hu.unit, hD, hF, ?_, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ⟨_, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext ?_)
    simp [h0]
  · rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz
  · rfl

end GlobalTheory.CycAway
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormSec
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormSec
open scoped Pointwise

theorem map_form {B B' J : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') (T : Finset (J →₀ ℕ))
    (c : (J →₀ ℕ) → B) (s : J → B) :
    ψ (∑ m ∈ T, c m * m.prod (fun i n => s i ^ n)) =
      ∑ m ∈ T, ψ (c m) * m.prod (fun i n => ψ (s i) ^ n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finsupp.prod, map_prod, map_pow]

theorem form_scale {B J : Type} [CommRing B] (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → B) (u : B) (s : J → B) :
    ∑ m ∈ T, c m * m.prod (fun i n => (u * s i) ^ n) =
      u ^ d * ∑ m ∈ T, c m * m.prod (fun i n => s i ^ n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hT m hm]
  ring

section Supp
variable {A X : Type} [CommRing A] [AddCommGroup X]

theorem supp_mul {x y : AddMonoidAlgebra A X} {S S' : Set X} (hx : (x.coeff.support : Set X) ⊆ S)
    (hy : (y.coeff.support : Set X) ⊆ S') : ((x * y).coeff.support : Set X) ⊆ S + S' := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset x y ha)
  exact Set.add_mem_add (hx hb) (hy hc)

theorem supp_one : ((1 : AddMonoidAlgebra A X).coeff.support : Set X) ⊆ 0 := by
  intro a ha
  have := AddMonoidAlgebra.support_coeff_one_subset (k := A) (G := X) ha
  simpa using this

theorem supp_pow {x : AddMonoidAlgebra A X} {S : Set X} (hx : (x.coeff.support : Set X) ⊆ S) (n : ℕ) :
    ((x ^ n).coeff.support : Set X) ⊆ n • S := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact supp_one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact supp_mul ih hx

theorem supp_prod {J : Type} {x : J → AddMonoidAlgebra A X} {S : Set X}
    (hx : ∀ i, ((x i).coeff.support : Set X) ⊆ S) (n : J → ℕ) (t : Finset J) :
    ((∏ i ∈ t, x i ^ n i).coeff.support : Set X) ⊆ (∑ i ∈ t, n i) • S := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zero_nsmul]; exact supp_one
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_nsmul]
    exact supp_mul (supp_pow (hx j) _) ih

theorem supp_form {B J : Type} [CommRing B] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → A) (s : J → B) (S : Set X)
    (hs : ∀ i α, ((Equiv.ofBijective _ hb).symm (s i)).coeff α ≠ 0 → α ∈ S) (α : X)
    (hα : ((Equiv.ofBijective _ hb).symm (∑ m ∈ T, f (c m) * m.prod (fun i n => s i ^ n))).coeff α ≠ 0) :
    ∃ β : Fin d → X, (∀ n, β n ∈ S) ∧ α = ∑ n, β n := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm.toRingHom _).coeff α ≠ 0 at hα
  rw [map_form, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hα
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have h2 : ((e.symm.toRingHom (f (c m))).coeff.support : Set X) ⊆ 0 := by
    change ((e.symm (f (c m))).coeff.support : Set X) ⊆ 0
    rw [h1, AddMonoidAlgebra.coeff_single]
    intro a ha
    simpa using Finsupp.support_single_subset ha
  have h3 := supp_mul h2 (supp_prod (x := fun i => e.symm.toRingHom (s i)) (S := S)
    (fun i a ha => hs i a (Finsupp.mem_support_iff.1 ha)) m m.support) (Finsupp.mem_support_iff.2 hne)
  rw [zero_add, hT m hm, Set.mem_nsmul] at h3
  obtain ⟨β, hβ⟩ := h3
  exact ⟨fun n => β n, fun n => (β n).2, by rw [← hβ, List.sum_ofFn]⟩

end Supp

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem valHom_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : Sp R ⟶ X)
    (hx : x ≫ p = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) :
    CrdCalc.valHom x U h (constFn p U a) = a := by
  have e : p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h = 𝟙 _ := by
    refine (Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).trans ?_
    generalize_proofs h₁
    revert h₁
    rw [hx]
    intro h₁
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact (Category.id_comp _).trans ((Sp R).presheaf.map_id _)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h) ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a = a
  rw [e, Category.id_comp, Iso.inv_hom_id]
  rfl

theorem deg_of_mem {k J : Type} [Field k] {d : ℕ} {Pf : MvPolynomial J k} (h : Pf.IsHomogeneous d) :
    ∀ m ∈ Pf.support, ∑ i ∈ m.support, m i = d := fun m hm => by
  have := h (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum] using this

def formSec {k : Type} [Field k] (Φ : FibPre k) {J : Type} (F : J → (Φ.H 1).Sec) {d : ℕ}
    (Pf : MvPolynomial J k) (h : Pf.IsHomogeneous d) : (Φ.H d).Sec where
  f l := ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) *
    m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)
  compat l l' := by
    let V : Φ.G.left.Opens := (Φ.H d).U l ⊓ (Φ.H d).U l'
    let r : Γ(Φ.G.left, (Φ.H d).U l) →+* Γ(Φ.G.left, V) := resG _ inf_le_left
    let r' : Γ(Φ.G.left, (Φ.H d).U l') →+* Γ(Φ.G.left, V) := resG _ inf_le_right
    let u : Γ(Φ.G.left, V)ˣ := pullU Φ.D.q.left (Φ.N₀.U l ⊓ Φ.N₀.U l') (Φ.N₀.g l l')
    have hF : ∀ i, r ((F i).f l) = (u : Γ(Φ.G.left, V)) * r' ((F i).f l') := fun i => by
      have := (F i).compat l l'
      change r ((F i).f l) = ((u ^ 1 : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' ((F i).f l') at this
      exact this.trans (congrArg (fun w : Γ(Φ.G.left, V)ˣ => (w : Γ(Φ.G.left, V)) * r' ((F i).f l')) (pow_one u))
    change r _ = ((u ^ d : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' _
    rw [map_form, map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [res_constFn, res_constFn]
    congr 2
    funext i n
    exact congrArg (· ^ n) (hF i)

theorem exists_formSec : (∀ (k : Type) [Field k] (Φ : FibPre k) (J : Type) (F : J → (Φ.H 1).Sec) (d : ℕ) (Pf : MvPolynomial J k), Pf.IsHomogeneous d → ∃ φ : (Φ.H d).Sec, (∀ l, φ.f l = ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) * m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)) ∧ (∀ α ∈ Φ.supp φ, ∃ β : Fin d → Φ.E.X, (∀ n, ∃ i, β n ∈ Φ.supp (F i)) ∧ α = ∑ n, β n) ∧ ∀ (x : Φ.Pt) (v : J → k), Crd (Φ.H 1) F x.left v → (MvPolynomial.eval v Pf = 0 ↔ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ)) := by
  intro k _ Φ J F d Pf h
  refine ⟨formSec Φ F Pf h, fun _ => rfl, ?_, ?_⟩
  · rintro α ⟨l, hl⟩
    refine supp_form _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) Pf.support d (deg_of_mem h)
      (fun m => constFn Φ.E.B.hom _ (Pf.coeff m)) (fun i => (F i).f l) {β | ∃ i, β ∈ Φ.supp (F i)}
      (fun i β hβ => ⟨i, l, hβ⟩) α ?_
    simp only [WtLin.app_constFn _ _ _ (Over.w Φ.D.q)]
    exact hl
  · rintro x v ⟨l, c, hl, hv⟩
    have hl' : ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l := hl
    have hc : Crd (Φ.H d) (fun _ : Unit => formSec Φ F Pf h) x.left (fun _ => MvPolynomial.eval v Pf) := by
      refine ⟨l, c ^ d, hl', fun _ => ?_⟩
      rw [CrdCalc.valR_eq _ _ hl']
      change _ = _ * CrdCalc.valHom x.left _ hl' (∑ m ∈ Pf.support, _)
      rw [map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h), MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [valHom_constFn _ _ (Over.w x)]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hv i, CrdCalc.valR_eq _ _ hl]
      rfl
    rw [← CrdCalc.crd_isUnit_iff () hc, isUnit_iff_ne_zero, not_not]

end GlobalTheory.ZH.FormSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingEquivPowerSeriesOfComplete
open IsLocalRing

namespace GlobalTheory.ArcAvoid

theorem exists_ringEquiv_powerSeries_of_complete {k O : Type*} [Field k] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ι : k →+* O)
    (hι : Function.Surjective ((residue O).comp ι)) :
    ∃ e : PowerSeries k ≃+* O, ∀ a, e (PowerSeries.C a) = ι a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ev, hev⟩ := exists_algHom_powerSeries_apply_X_of_isAdicComplete (maximalIdeal O)
    (π := π) (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π)
  let ψ : PowerSeries k →+* O := (ev : PowerSeries O →+* O).comp (PowerSeries.map ι)
  have hX : ψ PowerSeries.X = π := by simp [ψ, hev]
  have hC : ∀ a, ψ (PowerSeries.C a) = ι a := fun a => by
    simpa [ψ] using ev.commutes (ι a)
  have hmap : (Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ = maximalIdeal O := by
    rw [Ideal.map_span, Set.image_singleton, hX, hπ.maximalIdeal_eq]
  have hH : IsHausdorff ((Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ) O := by
    rw [hmap]; infer_instance
  have hs : Function.Surjective ψ := by
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span {PowerSeries.X}) ψ ?_
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hι (residue O y)
    refine ⟨PowerSeries.C a, ?_⟩
    rw [RingHom.comp_apply, hC, Ideal.Quotient.eq, hmap]
    exact Ideal.Quotient.eq.mp ha
  have hi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    rw [map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero, hX] at ha
    exact hπ.ne_zero (eq_zero_of_pow_eq_zero ha)
  exact ⟨RingEquiv.ofBijective ψ ⟨hi, hs⟩, hC⟩

theorem exists_ringHom_powerSeries_of_dvr {k V : Type*} [Field k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : k →+* V) (hι : Function.Surjective ((residue V).comp ι)) :
    ∃ φ : V →+* PowerSeries k, Function.Injective φ ∧ (∀ a, φ (ι a) = PowerSeries.C a) ∧
      ∀ v, v ∈ maximalIdeal V ↔ PowerSeries.constantCoeff (φ v) = 0 := by
  let O := AdicCompletion (maximalIdeal V) V
  obtain ⟨e, he⟩ := exists_ringEquiv_powerSeries_of_complete ((algebraMap V O).comp ι) (by
    intro y
    obtain ⟨z, rfl⟩ := (AdicCompletion.residueField_map_bijective V).2 y
    obtain ⟨a, rfl⟩ := hι z
    exact ⟨a, rfl⟩)
  refine ⟨(e.symm : O →+* PowerSeries k).comp (algebraMap V O),
    e.symm.injective.comp (algebraMap_adicCompletion_injective_of_dvr V), fun a => ?_, fun v => ?_⟩
  · exact e.symm_apply_eq.mpr (he a).symm
  · rw [mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (algebraMap V O),
      ← isUnit_map_iff e.symm, PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
    rfl


open Polynomial in
theorem surjective_residue_of_isAlgebraic {k V : Type*} [Field k] [IsAlgClosed k] [CommRing V]
    [IsDomain V] [IsLocalRing V] [Algebra k[X] V] [Algebra.IsAlgebraic k[X] V]
    [FaithfulSMul k[X] V] (hX : algebraMap k[X] V X ∈ maximalIdeal V) :
    Function.Surjective ((residue V).comp ((algebraMap k[X] V).comp C)) := by
  classical
  letI : Algebra k (ResidueField V) := ((residue V).comp ((algebraMap k[X] V).comp C)).toAlgebra
  have hc : (algebraMap k (ResidueField V)).comp (constantCoeff : k[X] →+* k) =
      (residue V).comp (algebraMap k[X] V) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [RingHom.algebraMap_toAlgebra]
    · simpa using ((residue_eq_zero_iff _).mpr hX).symm
  have : Algebra.IsAlgebraic k (ResidueField V) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := k[X]) x
    have h1 := aeval_primPart_eq_zero hp0 hp
    refine ⟨p.primPart.map constantCoeff, fun h => ?_, ?_⟩
    · refine Polynomial.not_isUnit_X (R := k) (p.isPrimitive_primPart X ?_)
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun q => q.coeff i) h
      simpa [X_dvd_iff] using this
    · rw [aeval_def, eval₂_map, hc, ← hom_eval₂, ← aeval_def, h1, map_zero]⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := ResidueField V)).2


open Polynomial in
theorem exists_injective_of_height_le_one {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) [hm : m.IsMaximal]
    (h1 : m.height ≤ 1) :
    ∃ φ : B →ₐ[k] PowerSeries k, Function.Injective φ ∧
      ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  rcases eq_or_ne m ⊥ with rfl | hne
  · letI : Field B := (Ring.isField_iff_maximal_bot.mpr hm).toField
    have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
    let e : k ≃ₐ[k] B :=
      .ofBijective (Algebra.ofId k B) IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(Algebra.ofId k (PowerSeries k)).comp e.symm, RingHom.injective _, fun b => ?_⟩
    simp [Algebra.ofId_apply]
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have hal : ∀ p : k[X], algebraMap k[X] B p = aeval t p := fun _ => rfl
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun a => by simp [hal]
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k k[X] B
  have hinj : Function.Injective (algebraMap k[X] B) := by
    refine transcendental_iff_injective.mp fun halg => hm.ne_top ?_
    exact m.eq_top_of_isUnit_mem htm (halg.isIntegral.isUnit ht0)
  obtain ⟨K', _, _, _, V, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one
    (O := k[X]) (K := FractionRing k[X]) hinj m h1 X X_ne_zero (by simpa [hal] using htm)
  letI : Algebra k[X] V := (φ.comp (algebraMap k[X] B)).toAlgebra
  letI : Algebra k[X] K' :=
    ((algebraMap (FractionRing k[X]) K').comp (algebraMap k[X] (FractionRing k[X]))).toAlgebra
  have : IsScalarTower k[X] (FractionRing k[X]) K' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k[X] V K' := .of_algebraMap_eq fun a => (hφ a).symm
  have : FaithfulSMul k[X] V := (faithfulSMul_iff_algebraMap_injective _ _).mpr (hφi.comp hinj)
  have halg : Algebra.IsAlgebraic k[X] K' :=
    (IsFractionRing.comap_isAlgebraic_iff (A := k[X]) (K := FractionRing k[X]) (C := K')).mpr
      inferInstance
  have : Algebra.IsAlgebraic k[X] V :=
    .of_injective (IsScalarTower.toAlgHom k[X] V K') Subtype.val_injective
  have hXV : algebraMap k[X] V X ∈ maximalIdeal V := by
    change algebraMap k[X] B X ∈ (maximalIdeal V).comap φ
    simpa [hal, hφm] using htm
  let W : Subalgebra k[X] K' :=
    { V.toSubring with algebraMap_mem' := fun r => (hφ r) ▸ (φ (algebraMap k[X] B r)).2 }
  have hVn : IsNoetherianRing V := (krullAkizuki (FractionRing k[X]) W).1
  have hnf : ¬ IsField V := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    rw [h] at hXV
    exact X_ne_zero ((FaithfulSMul.algebraMap_eq_zero_iff k[X] V).mp hXV)
  have hval : ValuationRing V := inferInstance
  have : IsDiscreteValuationRing V := ((IsDiscreteValuationRing.TFAE V hnf).out 2 1).mp hval
  obtain ⟨ψ, hψi, hψC, hψm⟩ :=
    exists_ringHom_powerSeries_of_dvr _ (surjective_residue_of_isAlgebraic hXV)
  refine ⟨{ ψ.comp φ with commutes' := fun a => ?_ }, hψi.comp hφi, fun b => ?_⟩
  · have := hψC a
    rw [IsScalarTower.algebraMap_apply k k[X] B]
    exact this
  · rw [← hφm]
    exact hψm (φ b)

theorem exists_algHom_powerSeries_ne_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B), m.IsMaximal → ∀ f : B, f ≠ 0 →
      ∃ φ : B →ₐ[k] PowerSeries k, φ f ≠ 0 ∧
        ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  intro k _ _ B _ _ _ _ m hm f hf
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨q, hqf, hqm, hht⟩ := exists_mem_height_map_le_one m (PrimeSpectrum.basicOpen f).isOpen
    ⟨⊥, hf, bot_le⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  obtain ⟨φ, hφi, hφm⟩ := exists_injective_of_height_le_one (k := k) _ hht
  refine ⟨φ.comp (Ideal.Quotient.mkₐ k q.asIdeal), fun h => hqf ?_, fun b => ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hφi (h.trans (map_zero φ).symm))
  · conv_lhs => rw [← hcomap]
    exact hφm _

end GlobalTheory.ArcAvoid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonHomExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.GenericHom

theorem mul_eq_of_generic {A B P : Type*} [Group A] [Group B] (j : P → A) (f : P → B)
    (hm : ∀ x y z, j x * j y = j z → f x * f y = f z)
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y : P)
    (h : j a * j x = j b * j y) : f a * f x = f b * f y := by
  obtain ⟨u, hu⟩ := hg [1, j x, j y, j a * j x]
  obtain ⟨c, hc⟩ := hu 1 (by simp)
  obtain ⟨p, hp⟩ := hu (j x) (by simp)
  obtain ⟨q, hq⟩ := hu (j y) (by simp)
  obtain ⟨r, hr⟩ := hu (j a * j x) (by simp)
  rw [_root_.one_mul] at hc
  have e1 := hm x c p (by rw [hc, hp])
  have e2 := hm y c q (by rw [hc, hq])
  have e3 := hm a p r (by rw [hp, hr, _root_.mul_assoc])
  have e4 := hm b q r (by rw [hq, hr, h, _root_.mul_assoc])
  apply mul_right_cancel (b := f c)
  rw [_root_.mul_assoc, _root_.mul_assoc, e1, e2, e3, e4]

theorem mul_four_eq_of_generic {A B P : Type*} [Group A] [Group B] (j : P → A) (f : P → B)
    (hm : ∀ x y z, j x * j y = j z → f x * f y = f z)
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y c z : P)
    (h : (j a * j x) * (j b * j y) = j c * j z) : (f a * f x) * (f b * f y) = f c * f z := by
  obtain ⟨u, hu⟩ := hg [1, j y, j b * j y, j x * (j b * j y), j c * j z, j z]
  obtain ⟨p₀, h₀⟩ := hu 1 (by simp)
  obtain ⟨p₁, h₁⟩ := hu (j y) (by simp)
  obtain ⟨p₂, h₂⟩ := hu (j b * j y) (by simp)
  obtain ⟨p₃, h₃⟩ := hu (j x * (j b * j y)) (by simp)
  obtain ⟨p₄, h₄⟩ := hu (j c * j z) (by simp)
  obtain ⟨p₅, h₅⟩ := hu (j z) (by simp)
  rw [_root_.one_mul] at h₀
  have e1 := hm y p₀ p₁ (by rw [h₀, h₁])
  have e2 := hm b p₁ p₂ (by rw [h₁, h₂, _root_.mul_assoc])
  have e3 := hm x p₂ p₃ (by rw [h₂, h₃]; simp only [_root_.mul_assoc])
  have e4 := hm a p₃ p₄ (by rw [h₃, h₄, ← h]; simp only [_root_.mul_assoc])
  have e5 := hm z p₀ p₅ (by rw [h₀, h₅])
  have e6 := hm c p₅ p₄ (by rw [h₅, h₄, _root_.mul_assoc])
  apply mul_right_cancel (b := f p₀)
  simp only [_root_.mul_assoc]
  rw [e1, e2, e3, e4, e5, e6]

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_point_mem (X : Over (Sp k)) [LocallyOfFiniteType X.hom] (W : Set X.left)
    (hW : IsLocallyClosed W) (hne : W.Nonempty) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, ∀ p, x.left p ∈ W := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hne hW
  exact ⟨Over.homMk (pointOfClosedPoint (K := k) X.hom c hc) (pointOfClosedPoint_comp (K := k) X.hom c hc),
    fun p => (congrArg (· ∈ W) (pointOfClosedPoint_apply (K := k) X.hom c hc p)).mpr hcW⟩

theorem hom_ext_points {X Y : Over (Sp k)}
    [Smooth X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := isNormalScheme_of_smooth (S := Spec (.of k)) X.hom
  have : IsReduced X.left := IsNormalScheme.isReduced
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := k) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  obtain ⟨p, hp⟩ := exists_point_mem X {x} hx.isLocallyClosed ⟨x, rfl⟩
  have h1 : p.left ≫ f.left = p.left ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (p.left (IsLocalRing.closedPoint k)) =
      g.left (p.left (IsLocalRing.closedPoint k)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint k)) h1
  have h3 : p.left (IsLocalRing.closedPoint k) = x := hp _
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))


omit [IsAlgClosed k] in
theorem exists_lift {U H Z : Over (Sp k)} (j : U ⟶ H) [IsOpenImmersion j.left] (x : Z ⟶ H)
    (hx : ∀ p, x.left p ∈ Set.range j.left) : ∃ y : Z ⟶ U, y ≫ j = x := by
  have hr : Set.range x.left ⊆ Set.range j.left := by rintro _ ⟨p, rfl⟩; exact hx p
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left x.left hr) ?_, Over.OverMorphism.ext
    (IsOpenImmersion.lift_fac j.left x.left hr)⟩
  rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w]

theorem exists_generic {U H : Over (Sp k)} [LocallyOfFiniteType H.hom] [IrreducibleSpace H.left]
    (j : U ⟶ H) [IsOpenImmersion j.left] [Nonempty U.left] (s : List (H ≅ H)) :
    ∃ u : 𝟙_ (Over (Sp k)) ⟶ H, ∀ φ ∈ s, ∃ p, p ≫ j = u ≫ φ.hom := by
  have key : ∃ W : Set H.left, IsOpen W ∧ W.Nonempty ∧
      ∀ φ ∈ s, ∀ w ∈ W, φ.hom.left w ∈ Set.range j.left := by
    induction s with
    | nil => exact ⟨Set.univ, isOpen_univ, Set.univ_nonempty, by simp⟩
    | cons φ s ih =>
      obtain ⟨W, h1, h2, h3⟩ := ih
      have ho : IsOpen (φ.hom.left ⁻¹' Set.range j.left) :=
        (IsOpenImmersion.isOpen_range j.left).preimage φ.hom.left.continuous
      have hn : (φ.hom.left ⁻¹' Set.range j.left).Nonempty := by
        obtain ⟨v⟩ := ‹Nonempty U.left›
        refine ⟨φ.inv.left (j.left v), v, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, φ.inv_hom_id]
        rfl
      refine ⟨W ∩ φ.hom.left ⁻¹' Set.range j.left, h1.inter ho,
        nonempty_preirreducible_inter h1 ho h2 hn, ?_⟩
      intro ψ hψ w hw
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hw.2
      · exact h3 ψ hψ w hw.1
  obtain ⟨W, h1, h2, h3⟩ := key
  obtain ⟨u, hu⟩ := exists_point_mem H W h1.isLocallyClosed h2
  exact ⟨u, fun φ hφ => exists_lift j _ fun p => h3 φ hφ _ (hu p)⟩


omit [IsAlgClosed k] in
theorem point_comp_mul {X G : Over (Sp k)} [GrpObj G] (x : 𝟙_ (Over (Sp k)) ⟶ X)
    (a : 𝟙_ (Over (Sp k)) ⟶ G) (g : X ⟶ G) : x ≫ ((toUnit X ≫ a) * g) = a * (x ≫ g) := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (𝟙 _), Category.id_comp]

theorem exists_monHom_extension : ∀ (k : Type) [Field k] [IsAlgClosed k] (H G U : Over (Sp k)) [GrpObj H] [GrpObj G], SmConn H → SmConn G → ∀ (j : U ⟶ H) (f : U ⟶ G), IsOpenImmersion j.left → Nonempty U.left → (∀ x y z : (𝟙_ (Over (Sp k)) ⟶ U), (x ≫ j) * (y ≫ j) = z ≫ j → (x ≫ f) * (y ≫ f) = z ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  intro k _ _ H G U _ _ ⟨hc, hs, _, _, hgc⟩ ⟨_, _, _, _, _⟩ j f hj hU hm
  have : IsIntegral H.left := isIntegral_of_smooth_of_geometricallyConnected H.hom
  have htr : ∀ (a x : 𝟙_ (Over (Sp k)) ⟶ H), x ≫ (transl a).hom = a * x := fun a x =>
    (point_comp_mul x a (𝟙 H)).trans (by rw [Category.comp_id])
  have hg : ∀ s : List (𝟙_ (Over (Sp k)) ⟶ H), ∃ u, ∀ h ∈ s,
      ∃ p : 𝟙_ (Over (Sp k)) ⟶ U, p ≫ j = h * u := by
    intro s
    obtain ⟨u, hu⟩ := exists_generic j (s.map transl)
    exact ⟨u, fun h hh => htr h u ▸ hu _ (List.mem_map_of_mem hh)⟩
  have hdec : ∀ h : 𝟙_ (Over (Sp k)) ⟶ H, ∃ a x : 𝟙_ (Over (Sp k)) ⟶ U,
      (a ≫ j) * (x ≫ j) = h := by
    intro h
    obtain ⟨u, hu⟩ := exists_generic j [Iso.refl H, asIso (ι[H]) ≪≫ transl h]
    obtain ⟨x, hx⟩ := hu (Iso.refl H) (by simp)
    obtain ⟨a, ha⟩ := hu (asIso (ι[H]) ≪≫ transl h) (by simp)
    refine ⟨a, x, ?_⟩
    rw [ha, hx, Iso.trans_hom, ← Category.assoc, htr, asIso_hom, Iso.refl_hom, Category.comp_id,
      ← Hom.inv_def, inv_mul_cancel_right]
  let J : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ H) := fun a => j ≫ (transl (a ≫ j)).hom
  let φ : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ G) := fun a => (toUnit U ≫ a ≫ f) * f
  have hJ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ J a = (a ≫ j) * (x ≫ j) := fun a x => by
    rw [← htr, Category.assoc]
  have hφ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ φ a = (a ≫ f) * (x ≫ f) := fun a x =>
    point_comp_mul x _ _
  have hJo : ∀ a, IsOpenImmersion (J a).left := fun a => by
    have : IsIso (transl (a ≫ j)).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (transl (a ≫ j)).hom))
    exact inferInstanceAs (IsOpenImmersion (j.left ≫ (transl (a ≫ j)).hom.left))
  have hcov : ∀ y : H.left, ∃ a, y ∈ Set.range (J a).left := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := hn
    have hcl : IsClosed (⋃ a, Set.range (J a).left)ᶜ :=
      (isOpen_iUnion fun a => IsOpenImmersion.isOpen_range (J a).left).isClosed_compl
    obtain ⟨h, hh⟩ := exists_point_mem H _ hcl.isLocallyClosed ⟨y, by simpa using hy⟩
    obtain ⟨a, x, e⟩ := hdec h
    rw [← hJ] at e
    subst e
    exact hh (IsLocalRing.closedPoint k) (Set.mem_iUnion.2 ⟨a, x.left (IsLocalRing.closedPoint k), rfl⟩)
  have hsU : Smooth U.hom := by rw [← Over.w j]; infer_instance
  let 𝒰 : H.left.OpenCover := Scheme.Cover.mkOfCovers (𝟙_ (Over (Sp k)) ⟶ U) (fun _ => U.left)
    (fun a => (J a).left) (fun y => hcov y) hJo
  have hcomp : ∀ a b, pullback.fst (J a).left (J b).left ≫ (φ a).left =
      pullback.snd (J a).left (J b).left ≫ (φ b).left := by
    intro a b
    let Z : Over (Sp k) := Over.mk (pullback.fst (J a).left (J b).left ≫ U.hom)
    have : Smooth Z.hom := inferInstanceAs (Smooth (pullback.fst (J a).left (J b).left ≫ U.hom))
    let p₁ : Z ⟶ U := Over.homMk (pullback.fst (J a).left (J b).left) rfl
    let p₂ : Z ⟶ U := Over.homMk (pullback.snd (J a).left (J b).left) (by
      show _ = pullback.fst (J a).left (J b).left ≫ U.hom
      have e := congrArg (· ≫ H.hom) (pullback.condition (f := (J a).left) (g := (J b).left))
      simp only [Category.assoc, Over.w] at e
      exact e.symm)
    have hp : p₁ ≫ J a = p₂ ≫ J b := Over.OverMorphism.ext pullback.condition
    have : p₁ ≫ φ a = p₂ ≫ φ b := hom_ext_points _ _ fun z => by
      rw [← Category.assoc, ← Category.assoc, hφ, hφ]
      refine mul_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ ?_
      show (a ≫ j) * ((z ≫ p₁) ≫ j) = (b ≫ j) * ((z ≫ p₂) ≫ j)
      rw [← hJ, ← hJ, Category.assoc, Category.assoc, hp]
    exact congrArg CommaMorphism.left this
  let F₀ : H.left ⟶ G.left := 𝒰.glueMorphisms (fun a => (φ a).left) hcomp
  have hF₀ : ∀ a, (J a).left ≫ F₀ = (φ a).left := fun a =>
    𝒰.ι_glueMorphisms (fun a => (φ a).left) hcomp a
  let F : H ⟶ G := Over.homMk F₀ (𝒰.hom_ext _ _ fun a => by
    show (J a).left ≫ F₀ ≫ G.hom = (J a).left ≫ H.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (hF₀ a)).trans
      ((Over.w (φ a)).trans (Over.w (J a)).symm)))
  have hF : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, ((a ≫ j) * (x ≫ j)) ≫ F = (a ≫ f) * (x ≫ f) := by
    intro a x
    have : J a ≫ F = φ a := Over.OverMorphism.ext (hF₀ a)
    rw [← hJ, Category.assoc, this, hφ]
  have hmul : ∀ h h' : 𝟙_ (Over (Sp k)) ⟶ H, (h * h') ≫ F = (h ≫ F) * (h' ≫ F) := by
    intro h h'
    obtain ⟨c, z, e⟩ := hdec (h * h')
    obtain ⟨a, x, rfl⟩ := hdec h
    obtain ⟨b, y, rfl⟩ := hdec h'
    rw [← e, hF, hF, hF]
    exact (mul_four_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ _ _ e.symm).symm
  refine ⟨F, ⟨?_, ?_⟩, hom_ext_points _ _ fun w => ?_⟩
  · have := hmul 1 1
    rw [_root_.one_mul] at this
    have h1 : (1 : 𝟙_ (Over (Sp k)) ⟶ H) ≫ F = 1 := left_eq_mul.1 this
    simpa [Hom.one_def] using h1
  · have : Smooth (H ⊗ H).hom := inferInstanceAs (Smooth (pullback.fst H.hom H.hom ≫ H.hom))
    refine hom_ext_points _ _ fun z => ?_
    have := hmul (z ≫ fst H H) (z ≫ snd H H)
    rw [Hom.mul_def, Hom.mul_def, lift_comp_fst_snd] at this
    rw [← Category.assoc, this, ← Category.assoc]
    congr 1
    ext <;> simp
  · obtain ⟨a, x, e⟩ := hdec (w ≫ j)
    rw [← Category.assoc, ← e, hF]
    exact hm _ _ _ e

end GlobalTheory.GenericHom
end
