module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTSlashInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Formalism.FormalDegreeBessel.StatementBF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem dvr_of_separated {S : Type*} [CommRing S] (π : S) (hn : ∀ n : ℕ, π ^ n ≠ 0)
    (hnu : ¬ IsUnit π) (hu : ∀ x, ¬ π ∣ x → IsUnit x) (hsep : ∀ x, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      exact hx (hsep x fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (h n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · have := Nat.find_min hex (m := m) (by omega)
        simpa using this
    obtain ⟨u, hxu⟩ := h1
    refine ⟨Nat.find hex, u, hu u ?_, hxu⟩
    rintro ⟨v, hv⟩
    exact Nat.find_spec hex ⟨v, by rw [pow_succ, mul_assoc, ← hv]; exact hxu⟩
  have : Nontrivial S := ⟨⟨π ^ 0, 0, hn 0⟩⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨a, u, hu', rfl⟩ := hfac x h.1
    obtain ⟨b, v, hv', rfl⟩ := hfac y h.2
    apply hn (a + b)
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ((hu'.mul hv').mul_left_eq_zero).1 this⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by simpa using hn 1
  have hprime : Prime π := by
    refine ⟨hπ0, hnu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    exact hnu (isUnit_of_dvd_unit hab ((hu a h.1).mul (hu b h.2)))
  refine ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hprime.irreducible, fun {x} hx => ?_⟩, hprime.irreducible⟩
  obtain ⟨n, u, hu', rfl⟩ := hfac x hx
  exact ⟨n, hu'.unit, rfl⟩

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0)
    (hmax : (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a}).IsMaximal) :
    ∃ _ : IsDomain (AdicCompletion (Ideal.span {a}) R),
      IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R) ∧
        Irreducible (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  have fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton _
  have hc := AdicCompletion.isAdicComplete_self (Ideal.span {a}) fg
  rw [Ideal.map_span, Set.image_singleton] at hc
  have hnu : ¬ IsUnit (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := fun h =>
    hmax.ne_top (Ideal.span_singleton_eq_top.2 h)
  have := isLocalRing_of_isAdicComplete_maximal
    (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
  refine dvr_of_separated _ (fun n hn => ?_) hnu (fun x hx => ?_) (fun x hx => ?_)
  · rw [← map_pow] at hn
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hn
    rw [AlgHom.commutes, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ] at h2
    have h3 : a ^ n * a ∣ a ^ n * 1 := by simpa using h2
    exact hnu ((isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n ha)).1 h3)).map _)
  · by_contra hxu
    have : x ∈ IsLocalRing.maximalIdeal _ := hxu
    rw [← IsLocalRing.eq_maximalIdeal hmax, Ideal.mem_span_singleton] at this
    exact hx this
  · refine hc.toIsHausdorff.haus' x fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx n

theorem completed_laurent_isDVR (p : ℕ) [Fact p.Prime] :
    ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  have hp : (p : Lau p) ≠ 0 := by
    have h : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [← map_natCast (HahnSeries.C : ℤ_[p] →+* Lau p)]
    exact HahnSeries.C_ne_zero h
  obtain ⟨e⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have := adicCompletion_dvr (p : Lau p) hp (by rw [map_natCast]; exact hmax)
  rw [map_natCast] at this
  exact this

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatementStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_laurent_isDVR_statement : ∀ (p : ℕ) [Fact p.Prime], ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  first | exact @GlobalTheory.K5.completed_laurent_isDVR | exact GlobalTheory.K5.completed_laurent_isDVR | (intros; apply GlobalTheory.K5.completed_laurent_isDVR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspForm
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem map_mapGL_rat (σ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ σ) =
      Matrix.SpecialLinearGroup.mapGL ℝ σ := by
  ext i j
  simp

theorem isZeroAt_sum {c : OnePoint ℝ} {k : ℤ} {ι : Type} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  refine Finset.sum_induction F (fun G => c.IsZeroAt G k) (fun a b ha hb => ha.add hb) ?_ h
  intro g _
  show IsZeroAtImInfty ((0 : ℍ → ℂ) ∣[k] g)
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

theorem heckeT_cuspForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k,
    ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  intro N l q k σ hN hq hql hσ f
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hql
    · exact h
  have hq0 : 0 < q := hq.pos
  have hinv := GlobalTheory.T.heckeT_slash_eq_of_slash_eq N l q k σ (⇑f) hN hq hql hσ
    (fun γ hγ => by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩)
  have hhol := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k σ (⇑f) hq0 (CuspFormClass.holo f)).2.2
  refine ⟨{ toFun := GlobalTheory.Hk.heckeT k q σ ⇑f
            slash_action_eq' := ?_
            holo' := hhol
            zero_at_cusps' := ?_ }, rfl⟩
  · rintro A ⟨γ, hγ, rfl⟩
    exact hinv γ hγ
  · intro c hc
    show c.IsZeroAt (GlobalTheory.Hk.heckeT k q σ ⇑f) k
    rw [GlobalTheory.Hk.heckeT, GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0, GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag q k _ hq0, ModularForm.SL_slash,
      ← SlashAction.slash_mul]
    refine OnePoint.IsZeroAt.add (isZeroAt_sum _ _ fun j _ => ?_) ?_
    · exact GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
    · have h := GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k (Matrix.SpecialLinearGroup.mapGL ℚ σ *
        Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
          (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne')) hN hl
        (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
      rw [map_mul, map_mapGL_rat] at h
      exact h

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspFormStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_cuspForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  first | exact @GlobalTheory.Hk.heckeT_cuspForm | exact GlobalTheory.Hk.heckeT_cuspForm | (intros; apply GlobalTheory.Hk.heckeT_cuspForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
open TensorProduct Coalgebra AddMonoidAlgebra

namespace GlobalTheory

section Units

variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]

variable [IsDomain A]

variable [Module.Free ℤ X]

end Units

section Coordinates

variable {X : Type*} [Zero X] {N : Type*} [AddCommGroup N]

theorem coboundary_apply_zero_left (g : X →₀ N) (x : X) :
    (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) (0, x) = g x := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← hf, ← hg]; abel
  | single y m =>
    simp only [Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply, Prod.mk.injEq]
    by_cases h : y = 0
    · subst h; simp
    · simp [h]

theorem finsupp_two_cocycle_eq_coboundary (f : X × X →₀ N)
    (hf : f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
      f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) = 0)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) :
    g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) = f := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  have key : ∀ (f : X × X →₀ N) (q : X × X),
      (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) +
      ((s f).mapDomain (fun y => ((0 : X), y)) - (s f).mapDomain (fun y => (y, y)) +
        (s f).mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) q = f q := by
    intro f q
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add (f := _), Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
      rw [← hf, ← hg]; abel
    | single p m =>
      obtain ⟨y, z⟩ := p
      by_cases h : y = 0
      · subst h
        have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
          ext x; simp [hs, Finsupp.single_apply]
        simp [this, Finsupp.single_apply]
      · have : s (Finsupp.single (y, z) m) = 0 := by
          ext x; simp [hs, h]
        simp [this, Finsupp.single_apply, h]
  have e : g = s f := Finsupp.ext hg
  ext q
  rw [← key f q, hf, e]
  simp

end Coordinates

section Ring

variable {X : Type*} [Zero X] {A : Type*} [Ring A]

theorem addMonoidAlgebra_coboundary_eq_iff (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by
  refine ⟨fun h x => ?_, fun h => coeff_injective
    (finsupp_two_cocycle_eq_coboundary f.coeff (congrArg coeff hf) g.coeff h)⟩
  rw [← h]
  exact (coboundary_apply_zero_left g.coeff x).symm

theorem addMonoidAlgebra_existsUnique_coboundary (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0) :
    ∃! g : A[X], mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f := by
  simp only [addMonoidAlgebra_coboundary_eq_iff f hf]
  exact ⟨ofCoeff (f.coeff.comapDomain (fun x => ((0 : X), x)) (Prod.mk_right_injective 0).injOn),
    fun _ => rfl, fun g hg => coeff_injective (Finsupp.ext hg)⟩

end Ring

section Tensor

variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {X : Type*} [AddMonoid X]

end Tensor

universe u v w

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassUnionBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassUnionBounds
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mass_eq_sum_ite_union (g : ℕ) [Fact g.Prime] (N : ℕ) (A : (ZMod g)[X] → Prop) :
    mass g N A = ∑ f ∈ sqSet g N, if A f then ((torusCard g f : ℝ))⁻¹ else 0 := by
  unfold mass
  rw [Finset.sum_filter]

theorem mass_union_bounds : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ), (∀ A B : (ZMod g)[X] → Prop, (∀ f ∈ sqSet g N, A f → B f) → mass g N A ≤ mass g N B) ∧ (∀ A, 0 ≤ mass g N A) ∧ (∀ (κ : Type) (s : Finset κ) (A : (ZMod g)[X] → Prop) (B : κ → (ZMod g)[X] → Prop), (∀ f ∈ sqSet g N, A f → ∃ i ∈ s, B i f) → mass g N A ≤ ∑ i ∈ s, mass g N (B i)) ∧ ∀ A : (ZMod g)[X] → Prop, mass g N A + mass g N (fun f => ¬ A f) = mass g N fun _ => True := by
  intro g _ N
  have hw : ∀ f : (ZMod g)[X], (0 : ℝ) ≤ ((torusCard g f : ℝ))⁻¹ := fun f => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B h
    simp only [mass_eq_sum_ite_union]
    refine Finset.sum_le_sum fun f hf => ?_
    by_cases hA : A f
    · rw [if_pos hA, if_pos (h f hf hA)]
    · rw [if_neg hA]
      split_ifs
      · exact hw f
      · exact le_rfl
  · intro A
    exact Finset.sum_nonneg fun f _ => hw f
  · intro κ s A B h
    simp only [mass_eq_sum_ite_union]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun f hf => ?_
    have hn : ∀ i ∈ s, (0 : ℝ) ≤ if B i f then ((torusCard g f : ℝ))⁻¹ else 0 := by
      intro i _
      split_ifs
      · exact hw f
      · exact le_rfl
    by_cases hA : A f
    · obtain ⟨i, hi, hB⟩ := h f hf hA
      rw [if_pos hA]
      have := Finset.single_le_sum hn hi
      simpa only [if_pos hB] using this
    · rw [if_neg hA]
      exact Finset.sum_nonneg hn
  · intro A
    rw [mass_eq_sum_ite_union, mass_eq_sum_ite_union, mass_eq_sum_ite_union, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hA : A f <;> simp [hA]

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassUnionBoundsStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_union_bounds : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ), (∀ A B : (ZMod g)[X] → Prop, (∀ f ∈ sqSet g N, A f → B f) → mass g N A ≤ mass g N B) ∧ (∀ A, 0 ≤ mass g N A) ∧ (∀ (κ : Type) (s : Finset κ) (A : (ZMod g)[X] → Prop) (B : κ → (ZMod g)[X] → Prop), (∀ f ∈ sqSet g N, A f → ∃ i ∈ s, B i f) → mass g N A ≤ ∑ i ∈ s, mass g N (B i)) ∧ ∀ A : (ZMod g)[X] → Prop, mass g N A + mass g N (fun f => ¬ A f) = mass g N fun _ => True := by
  first | exact @GlobalTheory.BadShare.mass_union_bounds | exact GlobalTheory.BadShare.mass_union_bounds | (intros; apply GlobalTheory.BadShare.mass_union_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularForm
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma isBoundedAt_finsetSum_heckeT {c : OnePoint ℝ} {k : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    simp only [Finset.sum_empty]
    rw [SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem heckeT_modularForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  intro N l q k σ hN hq hql hσ f
  have hq0 : 0 < q := hq.pos
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hql
    · exact h
  have hinv : ∀ γ ∈ lev N l, (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := fun γ hγ =>
    f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  refine ⟨{ toFun := heckeT k q σ ⇑f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ lev N l), rfl⟩
    exact GlobalTheory.T.heckeT_slash_eq_of_slash_eq N l q k σ ⇑f hN hq hql hσ hinv A hA
  · exact (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k σ ⇑f hq0 f.holo').2.2
  · intro c hc
    have hsum := GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0
    have hv := GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag q k ((⇑f) ∣[k] σ) hq0
    show c.IsBoundedAt (heckeT k q σ ⇑f) k
    unfold heckeT
    rw [hsum, hv]
    refine OnePoint.IsBoundedAt.add (isBoundedAt_finsetSum_heckeT _ _ fun j _ => ?_) ?_
    · exact GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
    · set D := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
          (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne') with hD
      have e : ((⇑f ∣[k] σ) ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) D)
          = ⇑f ∣[k] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)
              (Matrix.SpecialLinearGroup.mapGL ℚ σ * D) := by
        rw [map_mul, SlashAction.slash_mul, SL_slash]
        congr 2
        ext i j
        simp [Matrix.SpecialLinearGroup.mapGL]
      rw [e]
      refine GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl ?_ f c hc
      simp [hD, Matrix.det_fin_two_of]
      exact_mod_cast hq0
end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularFormStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_modularForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  first | exact @GlobalTheory.Hk.heckeT_modularForm | exact GlobalTheory.Hk.heckeT_modularForm | (intros; apply GlobalTheory.Hk.heckeT_modularForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMul
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem degType_pos (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : ∀ d ∈ degType g f, 0 < d := by
  intro d hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hd
  exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP).natDegree_pos

theorem degType_sum (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) (hf : f ≠ 0) :
    (degType g f).sum = f.natDegree := by
  unfold degType
  rw [← natDegree_multiset_prod _ (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f)]
  exact natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))

theorem prod_pow_sub_one_le (g : ℕ) (s : Multiset ℕ) :
    (s.map fun d => g ^ d - 1).prod ≤ g ^ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add]
    exact Nat.mul_le_mul (Nat.sub_le _ _) ih

theorem ne_zero_natDegree_of_mem_sqSet (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X])
    (hf : f ∈ sqSet g N) : f ≠ 0 ∧ f.natDegree = N := by
  unfold sqSet at hf
  rw [Finset.mem_filter, Finset.mem_image] at hf
  obtain ⟨⟨c, -, rfl⟩, -⟩ := hf
  have h : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
  refine ⟨(monic_X_pow_add h).ne_zero, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

theorem torusCard_bounds_mul : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  intro g hg
  refine ⟨fun N f hf => ?_, fun h f hh hf => ?_, fun P hP => ?_⟩
  · obtain ⟨h0, hN⟩ := ne_zero_natDegree_of_mem_sqSet g N f hf
    have hs : (degType g f).sum = N := (degType_sum g f h0).trans hN
    refine ⟨?_, ?_, hs, degType_pos g f⟩
    · unfold torusCard
      apply Multiset.prod_pos
      intro a ha
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.1 ha
      exact Nat.sub_pos_of_lt (Nat.one_lt_pow (degType_pos g f d hd).ne' hg.out.one_lt)
    · rw [← hs]
      exact prod_pow_sub_one_le g _
  · have hd : degType g (h * f) = degType g h + degType g f := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hh hf, Multiset.map_add (f := _)]
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_add (f := _), Multiset.prod_add]
  · have hd : degType g P = {P.natDegree} := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP, Multiset.map_singleton]
      congr 1
      exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (normalize_associated P))
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_singleton, Multiset.prod_singleton]

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMulStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  first | exact @GlobalTheory.BadShare.torusCard_bounds_mul | exact GlobalTheory.BadShare.torusCard_bounds_mul | (intros; apply GlobalTheory.BadShare.torusCard_bounds_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

private lemma centralBinom_le_pow_mul_four_pow_mul_prod_large_primes (m : ℕ) (hm : 2 < m) :
    m.centralBinom ≤ (2 * m) ^ (Nat.sqrt (2 * m) + 1) * 4 ^ (2 * m / 3) *
      ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p := by
  set s := Nat.sqrt (2 * m) with hs
  have hone : ∀ (P : Prop) [Decidable P] (p : ℕ), (P → 1 ≤ p) → 1 ≤ (if P then p else 1) := by
    intro P _ p h
    split_ifs with hP
    exacts [h hP, le_rfl]
  have key : ∀ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p ≤
      (if p ≤ s then 2 * m else 1) * (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := by
    intro p _
    have hB : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) :=
      hone _ _ fun h => h.1.one_lt.le
    have hC : 1 ≤ (if p.Prime ∧ m < p then p else 1) := hone _ _ fun h => h.1.one_lt.le
    have hBC : 1 ≤ (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) *
        (if p.Prime ∧ m < p then p else 1) := le_trans (by norm_num) (Nat.mul_le_mul hB hC)
    by_cases h1 : p ≤ s
    · rw [if_pos h1]
      have h2 : p ^ m.centralBinom.factorization p ≤ 2 * m := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.pow_factorization_choose_le (by omega)
      calc p ^ m.centralBinom.factorization p ≤ 2 * m * 1 * 1 := by simpa using h2
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hB) hC
    · rw [if_neg h1, one_mul]
      have hsq : 2 * m < p ^ 2 :=
        calc 2 * m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' (2 * m)
          _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hv : m.centralBinom.factorization p ≤ 1 := by
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.factorization_choose_le_one hsq
      by_cases hp : p.Prime
      · by_cases h3 : p ≤ 2 * m / 3
        · have h4 : ¬ m < p := by omega
          rw [if_pos ⟨hp, h3⟩, if_neg (fun h => h4 h.2), mul_one]
          calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
            _ = p := pow_one p
        · by_cases h5 : m < p
          · rw [if_neg (fun h => h3 h.2), if_pos ⟨hp, h5⟩, one_mul]
            calc p ^ m.centralBinom.factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hv
              _ = p := pow_one p
          · have h0 : m.centralBinom.factorization p = 0 :=
              Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm (by omega) (by omega)
            rw [h0, pow_zero]
            exact hBC
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
        exact hBC
  calc m.centralBinom
      = ∏ p ∈ Finset.range (2 * m + 1), p ^ m.centralBinom.factorization p :=
        (Nat.prod_pow_factorization_centralBinom m).symm
    _ ≤ ∏ p ∈ Finset.range (2 * m + 1), ((if p ≤ s then 2 * m else 1) *
          (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1) * (if p.Prime ∧ m < p then p else 1)) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) key
    _ = (∏ p ∈ Finset.range (2 * m + 1), (if p ≤ s then 2 * m else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ p ≤ 2 * m / 3 then p else 1)) *
          (∏ p ∈ Finset.range (2 * m + 1), (if p.Prime ∧ m < p then p else 1)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ _ := by
        gcongr ?_ * ?_ * ?_
        · rw [← Finset.prod_filter, Finset.prod_const]
          apply Nat.pow_le_pow_right (by omega)
          calc ((Finset.range (2 * m + 1)).filter (fun p => p ≤ s)).card
              ≤ (Finset.range (s + 1)).card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
                omega
            _ = s + 1 := Finset.card_range _
        · rw [← Finset.prod_filter]
          calc ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ p ≤ 2 * m / 3), p
              = primorial (2 * m / 3) := by
                unfold primorial
                congr 1
                ext p
                simp only [Finset.mem_filter, Finset.mem_range]
                constructor
                · rintro ⟨_, h2, h3⟩
                  exact ⟨by omega, h2⟩
                · rintro ⟨h1, h2⟩
                  exact ⟨by omega, h2, by omega⟩
            _ ≤ 4 ^ (2 * m / 3) := primorial_le_four_pow _
        · rw [← Finset.prod_filter]

theorem _root_.GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between :
    ∀ N : ℕ, 100000 ≤ N → 1 / (10 * Real.log N) ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N),
        (1 : ℝ) / p := by
  intro N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hS
  set m := N / 2 with hm
  set s := Nat.sqrt (2 * m) with hs
  set k := S.card with hk
  set q := 2 * m / 3 with hq
  have hm3 : 2 < m := by omega
  have hT : ∏ p ∈ (Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p), p ≤
      N ^ 3 * N ^ k := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)) (· ∈ S), mul_comm]
    apply Nat.mul_le_mul
    · have hsub : ((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
          (fun x => x ∉ S) ⊆ Finset.Icc (N - 2) N := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
        have h5 : ¬ (x + 3 ≤ N) := fun h5 => h4 (by
          rw [hS]
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, h2, by omega, h5⟩)
        rw [Finset.mem_Icc]
        omega
      calc _ ≤ N ^ (((Finset.range (2 * m + 1)).filter (fun p => p.Prime ∧ m < p)).filter
            (fun x => x ∉ S)).card :=
            Finset.prod_le_pow_card _ _ _ (fun x hx => (Finset.mem_Icc.mp (hsub hx)).2)
        _ ≤ N ^ 3 := by
            apply Nat.pow_le_pow_right (by omega)
            calc _ ≤ (Finset.Icc (N - 2) N).card := Finset.card_le_card hsub
              _ = 3 := by rw [Nat.card_Icc]; omega
    · calc _ ≤ ∏ x ∈ S, x := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
            · intro x hx
              exact (Finset.mem_filter.mp hx).2
            · intro x hx _
              rw [hS] at hx
              exact (Finset.mem_filter.mp hx).2.1.one_lt.le
        _ ≤ N ^ k := Finset.prod_le_pow_card _ _ _ (fun x hx => by
            rw [hS] at hx
            have := (Finset.mem_filter.mp hx).1
            rw [Finset.mem_range] at this
            omega)
  have hnat : 4 ^ m < N ^ (s + 5 + k) * 4 ^ q := by
    calc 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m (by omega)
      _ ≤ N * ((2 * m) ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) :=
          Nat.mul_le_mul (by omega)
            (le_trans (centralBinom_le_pow_mul_four_pow_mul_prod_large_primes m hm3)
              (Nat.mul_le_mul_left _ hT))
      _ ≤ N * (N ^ (s + 1) * 4 ^ q * (N ^ 3 * N ^ k)) := by
          gcongr
          omega
      _ = N ^ (s + 5 + k) * 4 ^ q := by ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hreal : (m : ℝ) * Real.log 4 < (s + 5 + k) * Real.log N + q * Real.log 4 := by
    have h' : (4 : ℝ) ^ m < (N : ℝ) ^ (s + 5 + k) * (4 : ℝ) ^ q := by exact_mod_cast hnat
    have h2 := Real.log_lt_log (by positivity) h'
    rw [Real.log_mul (pow_pos hN0 _).ne' (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow] at h2
    push_cast at h2
    linarith
  have hq3 : (3 : ℝ) * q ≤ 2 * m := by exact_mod_cast (by omega : 3 * q ≤ 2 * m)
  have hmN : (N : ℝ) ≤ 2 * m + 1 := by exact_mod_cast (by omega : N ≤ 2 * m + 1)
  have hs2 : (s : ℝ) ^ 2 ≤ N := by
    have : s ^ 2 ≤ N := le_trans (Nat.sqrt_le' (2 * m)) (by omega)
    exact_mod_cast this
  set t := Real.sqrt N with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = N := Real.sq_sqrt hN0.le
  have hNbig : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hst : (s : ℝ) ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have htlow : (316 : ℝ) ≤ t := by nlinarith
  have hL : Real.log N ≤ 7.72 + t / 50 := by
    have h1 := Real.log_le_sub_one_of_pos (x := t / 100) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    have h2 : Real.log t = Real.log N / 2 := by rw [ht, Real.log_sqrt hN0.le]
    have h3 : Real.log 100 < 4.86 := by
      have : Real.log 100 < Real.log (2 ^ 7) := Real.log_lt_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at this
      push_cast at this
      linarith [Real.log_two_lt_d9]
    linarith
  have hL4 : 1.386 < Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9]
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hsum : (k : ℝ) * (1 / N) ≤ ∑ p ∈ S, (1 : ℝ) / p := by
    rw [hk, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [hS] at hp
    obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_range] at h1
    apply one_div_le_one_div_of_le (by exact_mod_cast h2.pos)
    exact_mod_cast (by omega : p ≤ N)
  have hA : ((m : ℝ) - q) * 1.386 ≤ (m : ℝ) * Real.log 4 - q * Real.log 4 := by
    nlinarith
  have hB : ((s : ℝ) + 5) * Real.log N ≤ (t + 5) * (7.72 + t / 50) :=
    mul_le_mul (by linarith) hL hLpos.le (by positivity)
  have hkey : (N : ℝ) ≤ k * (10 * Real.log N) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htlow) ht0]
  calc 1 / (10 * Real.log N) ≤ k * (1 / N) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hN0]
        linarith
    _ ≤ _ := hsum

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mem_sqSet_iff (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X]) :
    f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold sqSet
  rw [Finset.mem_filter, Finset.mem_image, ← and_assoc (a := f.Monic)]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, -, rfl⟩
    have hd : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hd, ?_⟩
    apply natDegree_eq_of_degree_eq_some
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]
    exact hm.as_sum.symm

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (f : (ZMod g)[X]), f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  first | exact @GlobalTheory.BadShare.mem_sqSet_iff | exact GlobalTheory.BadShare.mem_sqSet_iff | (intros; apply GlobalTheory.BadShare.mem_sqSet_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowPadicValEqOneOfPrimePow
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem pow_padicVal_eq_one_of_primePow {k : Type} [Field k] {n l : ℕ} (hn : 0 < n) (hl : l.Prime) {y : k}
    (h1 : y ^ n = 1) {a : ℕ} (h2 : y ^ (l ^ a) = 1) : y ^ (l ^ padicValNat l n) = 1 := by
  have := Fact.mk hl
  have d1 : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one h1
  have d2 : orderOf y ∣ l ^ a := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl).1 d2
  rw [hi] at d1
  have hle : i ≤ padicValNat l n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn.ne').1 d1
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hi]
  exact pow_dvd_pow l hle

theorem primePowRoots_finite_ncard (k : Type) [Field k] (n l : ℕ) (hn : 0 < n) (hl : l.Prime) :
    {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
      {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n := by
  have hm : 0 < l ^ padicValNat l n := pow_pos hl.pos _
  have hsub : {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} ⊆
      ((nthRoots (l ^ padicValNat l n) (1 : k)).toFinset : Set k) := by
    rintro y ⟨h1, a, h2⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hm]
    exact pow_padicVal_eq_one_of_primePow hn hl h1 h2
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)

theorem samePart_roots_finite_ncard :
    ∀ (k : Type) [Field k] (n l : ℕ), 0 < n → l.Prime →
      ({y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
        {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n) ∧
      ∀ z : k, {x : k | x ^ n = 1 ∧ SamePart l x z}.Finite ∧
        {x : k | x ^ n = 1 ∧ SamePart l x z}.ncard ≤ l ^ padicValNat l n := by
  intro k _ n l hn hl
  obtain ⟨hf, hc⟩ := primePowRoots_finite_ncard k n l hn hl
  refine ⟨⟨hf, hc⟩, fun z => ?_⟩
  rcases Set.eq_empty_or_nonempty {x : k | x ^ n = 1 ∧ SamePart l x z} with he | ⟨x₀, hx₀, hb⟩
  · rw [he]; simp
  have hsub : {x : k | x ^ n = 1 ∧ SamePart l x z} ⊆
      (fun y => y * x₀) '' {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} := by
    rintro x ⟨hx, ha⟩
    have hs : SamePart l x x₀ := Eq.trans ha (Eq.symm hb)
    obtain ⟨a, ha⟩ := (samePart_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx⟩)
      (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx₀⟩)).1 hs
    have h0 : x₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hx₀
      exact zero_ne_one hx₀
    refine ⟨x / x₀, ⟨?_, a, ?_⟩, div_mul_cancel₀ x h0⟩
    · rw [div_pow, hx, hx₀, div_one]
    · rw [div_pow, ha, div_self (pow_ne_zero _ h0)]
  refine ⟨(hf.image _).subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans hc)

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BesselJUnitaryEquivariant
open Matrix MeasureTheory Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.BesselUnitary

def partner (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

lemma gram_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = partner k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk partner
  split_ifs <;> simp only [Fin.ext_iff] at * <;> first | rfl | omega

lemma gram_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner k r i)]
  · rw [gram_apply, gram_apply, Matrix.one_apply, if_pos rfl]
    unfold partner
    split_ifs <;> simp only [Fin.ext_iff] at * <;> first | omega | (simp; done) | (split_ifs <;> first | omega | simp)
  · intro b _ hb
    rw [gram_apply k r i b, if_neg hb, zero_mul]
  · simp

end GlobalTheory.BesselUnitary

namespace GlobalTheory

open BesselUnitary

end GlobalTheory
end
end
