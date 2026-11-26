module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensional
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace GlobalTheory.LocalH1Finiteness

theorem matRep_apply' {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (g : ↥(GK K)) (v : Fin k → ↥LL.1) (a : Fin k) :
    matRep M g v a = ∑ b, M g a b * v b := rfl

theorem finite_continuous_cocycles_matRep (hK : Formalism.GaloisCohomology.LocalFinitenessK) {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hM : Continuous fun g => M g)
    (hi : ∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) :
    Module.Finite ↥LL.1 (continuousCocycles (matRep M)) := by
  have := LL.2
  have := K.2
  let φ : Formalism.GaloisCohomology.GK l K.1 →* ↥(GK K) :=
    (IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom
  have hφ : Continuous φ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1).2
  have hφs : Function.Surjective φ := (IntermediateField.fixingSubgroupEquiv K.1).symm.surjective
  have hc : ReciprocityTheory.Gal.ContAction (matRep M) := by
    refine continuous_pi fun a => ?_
    simp only [matRep_apply']
    refine continuous_finsetSum _ fun b _ =>
      Continuous.mul ?_ ((continuous_apply b).comp continuous_snd)
    exact (hM.comp continuous_fst).matrix_elem a b
  have hn : ∀ g v, ‖matRep M g v‖ ≤ ‖v‖ := fun g v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_
    rw [matRep_apply']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v) fun b _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hi g a b)).trans (norm_le_pi_norm v b)
  exact finite_cocycles_of_compact_cover (l := l) (matRep M) hc hn φ hφ hφs
    (fun r N _ _ _ _ _ rho hr hrho => (hK l K.1 K.2 r N rho hr hrho).2.1)

theorem finite_H1fV_matRep : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1),
    Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) →
    Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  intro hK l _ P K LL k M hM hi
  have h1 := finite_continuous_cocycles_matRep hK K LL M hM hi
  set_option synthInstance.maxHeartbeats 200000 in
  have h2 : Module.Finite ↥LL.1 (finiteCocycles (P.PD K) (matRep M)) :=
    Module.Finite.of_injective (Submodule.inclusion (fun _ hx => hx.1 :
      finiteCocycles (P.PD K) (matRep M) ≤ continuousCocycles (matRep M))) (Submodule.inclusion_injective _)
  exact Module.Finite.quotient _ _

end GlobalTheory.LocalH1Finiteness
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensionalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_h1f_finite_dimensional : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (k : ℕ) (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), Continuous (fun g => M g) → (∀ g a b, ‖((M g a b : ↥LL.1) : Om l)‖ ≤ 1) → Module.Finite ↥LL.1 (FiniteCohomology (P.PD K) (matRep M)) := by
  first | exact @GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep | exact GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep | (intros; apply GlobalTheory.LocalH1Finiteness.finite_H1fV_matRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLe
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLe
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem cocycle_bound_length_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ LL _ O _ _ V _ _ _ _ ρ L Z hZ
  set M := Z ⊓ (B1 ρ).restrictScalars O with hM
  set K := (latticeCoboundaries L).comap M.subtype with hK

  let χ : V →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ (cob ρ).restrictScalars O
  have hχ : L.T ≤ LinearMap.ker χ := by
    intro t ht
    simp only [LinearMap.mem_ker, χ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨t, ht, rfl⟩
  let ψ : ↥(Representation.invariants (repD L)) →ₗ[O] (G → V) ⧸ latticeCoboundaries L :=
    (L.T.liftQ χ hχ) ∘ₗ (Representation.invariants (repD L)).subtype
  let ι : M →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ M.subtype
  have hKι : K ≤ LinearMap.ker ι := by
    intro x hx
    simpa [ι, K, Submodule.Quotient.mk_eq_zero] using hx
  let f : (M ⧸ K) →ₗ[O] (G → V) ⧸ latticeCoboundaries L := K.liftQ ι hKι
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K x
    simp only [LinearMap.mem_ker, f, Submodule.liftQ_apply, ι, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, K, Submodule.mem_comap,
      Submodule.coe_subtype]
    exact hx
  have hrange : LinearMap.range f ≤ LinearMap.range ψ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨⟨c, hcM⟩, rfl⟩ := Submodule.Quotient.mk_surjective K x
    obtain ⟨hcZ, hcB⟩ := hcM
    obtain ⟨v, hv⟩ := hcB
    have hinv : L.T.mkQ v ∈ Representation.invariants (repD L) := by
      intro g
      change (Submodule.Quotient.mk ((ρ g) v) : V ⧸ L.T) = Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      have := hZ c hcZ g
      rw [← hv] at this
      simpa [cob] using this
    refine ⟨⟨_, hinv⟩, ?_⟩
    simp [ψ, f, ι, χ, hv]
  calc Module.length O (M ⧸ K) ≤ Module.length O (LinearMap.range ψ) :=
        Module.length_le_of_injective ((Submodule.inclusion hrange).comp f.rangeRestrict) (by
          intro a b hab
          apply hfinj
          have := congrArg Subtype.val hab
          simpa using this)
    _ ≤ _ := Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthIntegralCocyclesRationalCoboundariesLeStatement
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_integral_cocycles_rational_coboundaries_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  first | exact @GlobalTheory.cocycle_bound_length_le | exact GlobalTheory.cocycle_bound_length_le | (intros; apply GlobalTheory.cocycle_bound_length_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulLeFinrankOfEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLe
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLe
open Pointwise

namespace GlobalTheory

theorem length_le_of_forall_fg_length_le (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞)
    (h : ∀ N : Submodule O M, N.FG → Module.length O N ≤ b) : Module.length O M ≤ b := by
  rw [Module.length_eq_height]
  refine Order.height_le_iff'.2 fun p _ => ?_
  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hx
  set N : Submodule O M := Submodule.span O (Set.range x) with hN
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range x)
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  let q : LTSeries (Submodule O N) :=
    { length := p.length
      toFun := fun i => (p i).comap N.subtype
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (p.step i).le) ?_
        intro heq
        have h1 : (⟨x i, hxN i⟩ : N) ∈ (p i.succ).comap N.subtype := hx1 i
        rw [← heq] at h1
        exact hx2 i h1 }
  have h2 : (q.length : ℕ∞) ≤ Order.height (⊤ : Submodule O N) :=
    Order.length_le_height le_top
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height (⊤ : Submodule O N) := h2
    _ = Module.length O N := (Module.length_eq_height (R := O) (M := N)).symm
    _ ≤ b := h N hNfg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLeStatement
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_le_of_forall_fg_submodule_length_le : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞), (∀ N : Submodule O M, N.FG → Module.length O N ≤ b) → Module.length O M ≤ b := by
  first | exact @GlobalTheory.length_le_of_forall_fg_length_le | exact GlobalTheory.length_le_of_forall_fg_length_le | (intros; apply GlobalTheory.length_le_of_forall_fg_length_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMul
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMul
open Pointwise

namespace GlobalTheory

theorem length_quot_smul_range_finite_free : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O M _ _ _ _ _ _ a
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMulStatement
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_scalar_mul : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  first | exact @GlobalTheory.length_quot_smul_range_finite_free | exact GlobalTheory.length_quot_smul_range_finite_free | (intros; apply GlobalTheory.length_quot_smul_range_finite_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulLeFinrankOfEmbedding
open Pointwise

namespace GlobalTheory

theorem length_quotient_smul_range_le_finrank_mul : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] (W M : Type) [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] [FiniteDimensional K W] [AddCommGroup M] [Module O M] (f : M →ₗ[O] W), Function.Injective f → ∀ a : O, Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) ≤ (Module.finrank K W : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O K _ _ _ _ _ _ W M _ _ _ _ _ _ _ f hf a
  set R := LinearMap.range (a • (LinearMap.id : M →ₗ[O] M)) with hR
  refine GlobalTheory.T.length_le_of_forall_fg_submodule_length_le O (M ⧸ R) _ ?_
  intro N hN
  obtain ⟨s, hs⟩ := hN
  set g := Function.surjInv (Submodule.mkQ_surjective R) with hg
  have hgs : ∀ q, R.mkQ (g q) = q := Function.surjInv_eq (Submodule.mkQ_surjective R)
  let N' : Submodule O M := Submodule.span O (g '' (s : Set (M ⧸ R)))
  have hmap : N'.map R.mkQ = N := by
    rw [Submodule.map_span, ← hs, ← Set.image_comp]
    congr 1
    ext q
    simp [hgs]
  haveI : Module.Finite O N' := Module.Finite.iff_fg.mpr (Submodule.fg_span (s.finite_toSet.image g))
  let e : N' →ₗ[O] W := f ∘ₗ N'.subtype
  have he : Function.Injective e := hf.comp N'.injective_subtype
  haveI : Module.IsTorsionFree K W := inferInstance
  haveI : Module.IsTorsionFree O W :=
    Module.IsTorsionFree.comap (S := K) (algebraMap O K)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have hinj := IsFractionRing.injective O K
        have : r = 0 := hinj (by simpa using h0)
        subst this
        exact (not_isRegular_zero (R := O)) hr))
      (fun r m => algebraMap_smul K r m)
  haveI : Module.IsTorsionFree O N' := Function.Injective.moduleIsTorsionFree e he e.map_smul
  haveI : Module.Free O N' := Module.free_of_finite_type_torsion_free'
  have hrank : Module.finrank O N' ≤ Module.finrank K W := by
    let b := Module.finBasis O N'
    have h1 : LinearIndependent O (e ∘ b) := b.linearIndependent.map' e (LinearMap.ker_eq_bot.mpr he)
    have h2 : LinearIndependent K (e ∘ b) := (LinearIndependent.iff_fractionRing O K).mp h1
    simpa using h2.fintype_card_le_finrank
  let p : N' →ₗ[O] N := (R.mkQ ∘ₗ N'.subtype).codRestrict N (by
    intro x
    rw [← hmap]
    exact ⟨x, x.2, rfl⟩)
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let R' := LinearMap.range (a • (LinearMap.id : N' →ₗ[O] N'))
  have hker : R' ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    have : R.mkQ (a • (x : M)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, by simp⟩
    simpa [p] using this
  let q : (N' ⧸ R') →ₗ[O] N := R'.liftQ p hker
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨R'.mkQ x, by simp [q]⟩
  calc Module.length O N ≤ Module.length O (N' ⧸ R') := Module.length_le_of_surjective q hq
    _ = (Module.finrank O N' : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := GlobalTheory.T.length_quotient_scalar_mul O N' a
    _ ≤ _ := by
      gcongr

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulLeFinrankOfEmbeddingStatement
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_smul_le_finrank_of_embedding : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] (W M : Type) [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] [FiniteDimensional K W] [AddCommGroup M] [Module O M] (f : M →ₗ[O] W), Function.Injective f → ∀ a : O, Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) ≤ (Module.finrank K W : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  first | exact @GlobalTheory.length_quotient_smul_range_le_finrank_mul | exact GlobalTheory.length_quotient_smul_range_le_finrank_mul | (intros; apply GlobalTheory.length_quotient_smul_range_le_finrank_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLength
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLength
open Pointwise

namespace GlobalTheory

theorem length_quotient_span_pow_le (O : Type) [CommRing O] (p : O) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    exact bot_le
  | succ n ih =>
    set S : Submodule O O := Ideal.span {p ^ (n + 1)} with hS
    set T : Submodule O O := Ideal.span {p ^ n} with hT
    have hST : S ≤ T := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p n.le_succ)
    let v : O ⧸ S := S.mkQ (p ^ n)
    have hker : (Ideal.span {p} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O (O ⧸ S) v) := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      simp only [v, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      rw [Submodule.Quotient.mk_eq_zero, hS, Ideal.mem_span_singleton']
      exact ⟨c, by ring⟩
    let ψ : (O ⧸ (Ideal.span {p} : Submodule O O)) →ₗ[O] O ⧸ S :=
      (Ideal.span {p} : Submodule O O).liftQ (LinearMap.toSpanSingleton O (O ⧸ S) v) hker
    let N : Submodule O (O ⧸ S) := LinearMap.range ψ
    have hN : N = T.map S.mkQ := by
      simp only [N, ψ, Submodule.range_liftQ, hT, Ideal.span, Submodule.map_span, Set.image_singleton]
      rw [← LinearMap.span_singleton_eq_range]
    have h1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have hle : Module.length O N ≤ Module.length O (O ⧸ Ideal.span {p}) :=
      Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
    have heq : Module.length O ((O ⧸ S) ⧸ N) = Module.length O (O ⧸ Ideal.span {p ^ n}) := by
      rw [hN]
      exact (Submodule.quotientQuotientEquivQuotient S T hST).length_eq
    change Module.length O (O ⧸ S) ≤ _
    rw [h1, heq]
    calc Module.length O N + Module.length O (O ⧸ Ideal.span {p ^ n})
        ≤ Module.length O (O ⧸ Ideal.span {p}) + (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
          add_le_add hle ih
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
          push_cast; ring

theorem main : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ),
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
  fun O _ p n => length_quotient_span_pow_le O p n

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLengthStatement
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_span_pow_le_mul_length : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ), Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  first | exact @GlobalTheory.main | exact GlobalTheory.main | (intros; apply GlobalTheory.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediate
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediate
open Pointwise

namespace GlobalTheory

theorem length_quotient_tower_of_le {R : Type} [CommRing R] {X : Type} [AddCommGroup X] [Module R X]
    (Y W : Submodule R X) (hYW : Y ≤ W) :
    Module.length R (X ⧸ Y) =
      Module.length R (W ⧸ Y.comap W.subtype) + Module.length R (X ⧸ W) := by
  have hf : Function.Injective ((Y.comap W.subtype).mapQ Y W.subtype le_rfl) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp
  refine Module.length_eq_add_of_exact ((Y.comap W.subtype).mapQ Y W.subtype le_rfl)
    (Submodule.factor hYW) hf (Submodule.factor_surjective hYW) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    constructor
    · intro h
      have hx : x ∈ W := by
        simpa [Submodule.Quotient.mk_eq_zero] using h
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    · rintro ⟨w, hw⟩
      rw [← hw]
      induction w using Submodule.Quotient.induction_on with
      | H z => simp [Submodule.Quotient.mk_eq_zero]

theorem length_quotient_smul_sup_le : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A]
    (Z B B' : Submodule O A) (a : O), B ≤ B' →
    Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤
      Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id :
        (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) +
      Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  intro O A _ _ _ Z B B' a hBB'
  set N : Submodule O Z := (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype with hN
  set C : Submodule O Z := B'.comap Z.subtype with hC
  set K : Submodule O Z := N ⊔ C with hK
  rw [length_quotient_tower_of_le N K le_sup_left, add_comm]
  refine add_le_add ?_ ?_
  ·
    let f : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ K) := Submodule.factor (le_sup_right : C ≤ K)
    have hf : LinearMap.range (a • (LinearMap.id : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ C))) ≤ LinearMap.ker f := by
      rintro y ⟨q, rfl⟩
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
        change a • (Submodule.Quotient.mk z : ↥Z ⧸ K) = 0
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        refine Submodule.mem_sup_left ?_
        show ((a • z : Z) : A) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
        exact Submodule.mem_sup_left ⟨z, z.2, by simp⟩
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk z), rfl⟩
  ·
    let ι : ↥(Z ⊓ B') →ₗ[O] K :=
      LinearMap.codRestrict K (LinearMap.codRestrict Z (Z ⊓ B').subtype (fun x => x.2.1))
        (fun x => Submodule.mem_sup_right (show _ ∈ C from x.2.2))
    let φ : ↥(Z ⊓ B') →ₗ[O] (↥K ⧸ N.comap K.subtype) := (N.comap K.subtype).mkQ ∘ₗ ι
    have hφ : B.comap (Z ⊓ B').subtype ≤ LinearMap.ker φ := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      show ((x : A)) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
      exact Submodule.mem_sup_right hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ φ hφ) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H k =>
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp k.2
      refine ⟨Submodule.Quotient.mk ⟨(z : A), z.2, hz⟩, ?_⟩
      rw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]
      have : ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) = -y := by
        ext
        simp only [ι, ← hyz, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_add]
        change (z : A) - ((y : A) + (z : A)) = -(y : A)
        abel
      show ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) ∈ N
      rw [this]
      exact N.neg_mem hy

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediateStatement
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_smul_sup_le_intermediate : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (Z B B' : Submodule O A) (a : O), B ≤ B' → Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤ Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id : (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) + Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  first | exact @GlobalTheory.length_quotient_smul_sup_le | exact GlobalTheory.length_quotient_smul_sup_le | (intros; apply GlobalTheory.length_quotient_smul_sup_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissible
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem length_H1fT_modPow_le : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ), Module.Finite LL (FiniteCohomology PD ρ) → ∀ n : ℕ, Module.length O (↥(latticeFiniteCocycles PD L) ⧸ ((latticeFiniteCocycles PD L).map ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : (G → V) →ₗ[O] (G → V))) ⊔ latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype) ≤ (n : ℕ∞) * (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * lenOl PD (O := O) + Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ _ _ _ V _ _ _ _ _ _ ρ _ _ _ L hfin n
  set Z := latticeFiniteCocycles PD L with hZdef
  set B' : Submodule O (G → V) := (B1 ρ).restrictScalars O with hB'
  set a : O := ((PD.p : ℕ) : O) ^ n with ha
  have hBB : latticeCoboundaries L ≤ B' := by
    rintro c ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hZT : ∀ c ∈ Z, ∀ g, c g ∈ L.T := by
    intro c hc g
    exact (Submodule.mem_pi.mp hc.1.2) g (Set.mem_univ g)
  have hZf : ∀ c ∈ Z, c ∈ finiteCocycles PD ρ := fun c hc => hc.2
  have h1 := GlobalTheory.T.length_quotient_smul_sup_le_intermediate O (G → V) Z (latticeCoboundaries L) B' a hBB
  have h2 := GlobalTheory.T.length_integral_cocycles_rational_coboundaries_le L Z hZT

  let ψ0 : ↥Z →ₗ[O] ↥(finiteCocycles PD ρ) :=
    { toFun := fun c => ⟨c.1, hZf c.1 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r c => rfl }
  let ψ : ↥Z →ₗ[O] FiniteCohomology PD ρ :=
    (((B1 ρ).comap (finiteCocycles PD ρ).subtype).mkQ.restrictScalars O).comp ψ0
  have hker : LinearMap.ker ψ = B'.comap Z.subtype := by
    ext c
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  let f := (B'.comap Z.subtype).liftQ ψ hker.ge
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have h3 := GlobalTheory.T.length_quotient_smul_le_finrank_of_embedding O LL (FiniteCohomology PD ρ) _ f hf a
  have h4 := GlobalTheory.T.length_quotient_span_pow_le_mul_length O ((PD.p : ℕ) : O) n
  have hl : lenOl PD (O := O) = Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) := rfl
  calc _ ≤ _ := h1
    _ ≤ (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) +
          Module.length O ↥(Representation.invariants (repD L)) := add_le_add h3 h2
    _ ≤ (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * ((n : ℕ∞) * lenOl PD (O := O)) +
          Module.length O ↥(Representation.invariants (repD L)) := by
        rw [hl]; gcongr
    _ = _ := by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissibleStatement
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_data_crystalline_admissible : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ), Module.Finite LL (FiniteCohomology PD ρ) → ∀ n : ℕ, Module.length O (↥(latticeFiniteCocycles PD L) ⧸ ((latticeFiniteCocycles PD L).map ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : (G → V) →ₗ[O] (G → V))) ⊔ latticeCoboundaries L).comap (latticeFiniteCocycles PD L).subtype) ≤ (n : ℕ∞) * (finrank LL (FiniteCohomology PD ρ) : ℕ∞) * lenOl PD (O := O) + Module.length O ↥(Representation.invariants (repD L)) := by
  first | exact @GlobalTheory.length_H1fT_modPow_le | exact GlobalTheory.length_H1fT_modPow_le | (intros; apply GlobalTheory.length_H1fT_modPow_le <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Pass

theorem ambient_h1f_of_local_finiteness : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (i : D.nd.Loc)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i),
    Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) →
    EmbeddingTypes.H1fFiniteRankTorsion (D := D) i ρ π dc := by
  intro hLF D i ρ π dc hc _ w hw _ C L2 _ n
  obtain ⟨⟨_, hdvr, hfr⟩, -⟩ := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  haveI := hdvr
  haveI := hfr
  have hcont := GlobalTheory.T.twistedDual_continuous_integral_over_enlarged_coeff D i w hw C.LL C.le ρ π hc
  have hfin := GlobalTheory.T.local_h1f_finite_dimensional hLF (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL D.R.r
    (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) hcont.1 hcont.2
  exact GlobalTheory.T.period_data_crystalline_admissible (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) L2 hfin n

end GlobalTheory.Pass
