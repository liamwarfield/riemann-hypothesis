module

public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PhibOLComplete
noncomputable section

namespace Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.LiftingTheory

section PhiB

variable {O : Type} [CommRing O]

end PhiB

section PhiBW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end PhiBW

section PhiBC

theorem phib_smodeq {M : Type} [CommRing M] (c x y : M) (k : ℕ) :
    x ≡ y [SMOD ((Ideal.span {c}) ^ k • ⊤ : Submodule M M)] ↔ c ^ k ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem phib_complete {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ϖ : R)
    [IsAdicComplete (Ideal.span {ϖ}) R] {ι : Type} [Fintype ι] (b : Module.Basis ι R M) :
    IsAdicComplete (Ideal.span {algebraMap R M ϖ}) M := by
  have key : ∀ (x : M) (k : ℕ), (algebraMap R M ϖ) ^ k ∣ x ↔ ∀ j, ϖ ^ k ∣ b.equivFun x j := by
    intro x k
    constructor
    · rintro ⟨z, rfl⟩ j
      refine ⟨b.equivFun z j, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, map_smul]
      rfl
    · intro h
      choose d hd using h
      refine ⟨b.equivFun.symm d, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      funext j
      rw [hd j]
      rfl
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.equivFun.injective
    rw [map_zero]
    funext j
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) R)
    intro k
    rw [phib_smodeq, sub_zero]
    have h := hx k
    rw [phib_smodeq, sub_zero] at h
    exact (key x k).1 h j
  · intro f hf
    have hc : ∀ j, ∃ L : R, ∀ k,
        b.equivFun (f k) j ≡ L [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule R R)] := by
      intro j
      apply IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) R)
      intro m k hmk
      rw [phib_smodeq]
      have h := hf hmk
      rw [phib_smodeq] at h
      have h' := (key _ m).1 h j
      rwa [map_sub] at h'
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun k => ?_⟩
    rw [phib_smodeq, key]
    intro j
    rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply]
    exact (phib_smodeq _ _ _ _).1 (hL j k)

theorem phib_OL_complete {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
  have h1 : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 :=
    inferInstanceAs (IsIntegralClosure ↥(integralClosure ℤ_[l] ↥LL.1) ℤ_[l] ↥LL.1)
  have h3 : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  have h4 : Module.IsTorsionFree ℤ_[l] ↥(OL LL) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (zl_inj_O LL)
  have h5 : Module.Free ℤ_[l] ↥(OL LL) := Module.free_of_finite_type_torsion_free'
  have h6 : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have h7 := phib_complete ((l : ℕ) : ℤ_[l]) (Module.finBasis ℤ_[l] ↥(OL LL))
  rwa [map_natCast] at h7

end PhiBC

section PhiI1

variable {O : Type} [CommRing O]

end PhiI1

section PhiI2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end PhiI2

section PhiI3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

end PhiI3

end Formalism.MainNotions.N.Ln34.FrobeniusSpanLemma

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA
noncomputable section

namespace Formalism.MainNotions.N.Ln34.CyclotomicLifting

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finite_roots_l : {x : Om l | x ^ (l ^ 1) = 1}.Finite := by
  classical
  have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  refine Set.Finite.subset (Polynomial.nthRoots (l ^ 1) (1 : Om l)).toFinset.finite_toSet ?_
  intro x hx
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hl]
  exact hx

theorem fd_Ks (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(Ks K 1) := by
  have h0 : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.finite_of_finrank_pos (Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K)
  have : Finite {x : Om l | x ^ (l ^ 1) = 1} := finite_roots_l.to_subtype
  have h1 : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => by
      have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
      apply IsIntegral.of_pow hl
      rw [show x ^ (l ^ 1) = 1 from hx]
      exact isIntegral_one)
  unfold Ks
  infer_instance

def cycL (K : FinExt l) : FinExt l := ⟨Ks K 1, fd_Ks K⟩

theorem cycL_val (K : FinExt l) : (cycL K).1 = Ks K 1 := rfl

theorem max_unramified_le_cyclotomic (K : FinExt l) : K0 K ≤ K0 (cycL K) :=
  le_inf (le_sup_left : K0 K ≤ Ks K 1) inf_le_right

theorem Ks_cycL (K : FinExt l) : Ks (cycL K) 1 = Ks K 1 := by
  apply le_antisymm
  · exact sup_le (inf_le_left : K0 (cycL K) ≤ (cycL K).1) le_sup_right
  · exact sup_le_sup_right (max_unramified_le_cyclotomic K) _

theorem cyclotomic_degree_max_unramified (K : FinExt l) : (K0 K).relfinrank (Ks K 1) = l - 1 := by
  have hp : 0 < finrank ℚ_[l] ↥(K0 K) := Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have h1 := IntermediateField.finrank_bot_mul_relfinrank (le_sup_left : K0 K ≤ Ks K 1)
  have h2 := Formalism.MainNotions.N.PreambleDegrees.finrank_Ks K one_pos
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  exact Nat.eq_of_mul_eq_mul_left hp (h1.trans h2)

theorem max_unramified_cyclotomic_eq (K : FinExt l) : K0 (cycL K) = K0 K := by
  have h1 := cyclotomic_degree_max_unramified K
  have h2 := cyclotomic_degree_max_unramified (cycL K)
  rw [Ks_cycL] at h2
  have hm := IntermediateField.relfinrank_mul_relfinrank (max_unramified_le_cyclotomic K)
    (inf_le_left : K0 (cycL K) ≤ (cycL K).1)
  rw [cycL_val, h1, h2] at hm
  have hpos : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have h3 : (K0 K).relfinrank (K0 (cycL K)) = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [hm, one_mul])
  exact le_antisymm (IntermediateField.relfinrank_eq_one_iff.1 h3) (max_unramified_le_cyclotomic K)

theorem finrank_eq_relfinrank (K : FinExt l) :
    finrank ↥(K0 K) ↥K.1 = (K0 K).relfinrank K.1 := by
  have hle : K0 K ≤ K.1 := inf_le_left
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact LinearEquiv.finrank_eq
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem finrank_cycL (K : FinExt l) : finrank ↥(K0 (cycL K)) ↥(cycL K).1 = l - 1 := by
  rw [finrank_eq_relfinrank, cycL_val, ← Ks_cycL K, cyclotomic_degree_max_unramified]

end Formalism.MainNotions.N.Ln34.CyclotomicLifting

end
end
