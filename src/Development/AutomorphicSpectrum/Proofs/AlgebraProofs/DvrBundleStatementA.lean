module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPair
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChain
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparison

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementA
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairCocycle
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairCocycle
namespace GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem pairCocycle : PairCocycle.Statement :=
  PairCocycle.proof GlobalTheory.T.flag_independence GlobalTheory.T.vertical_divisors_commute IntNumAddFirst.full

end GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairCocycleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_cocycle : GroundTheory.Heights₂.Heights.NumbersDVR.PairCocycle.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle | exact GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle | (intros; apply GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementA
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.Cocycle

section Generic

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
  [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]

theorem sameGeneric_self (E : ChartBundle O (mseg x) N V) : SameGeneric O x E E :=
  fun _ _ => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
    fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩

theorem sameGeneric_flip {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') :
    SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

theorem sameGeneric_comp {E E' E'' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E')
    (h' : SameGeneric O x E' E'') : SameGeneric O x E E'' := by
  have step : ∀ {A B C : ChartBundle O (mseg x) N V} (s : ∀ k, ι k),
      (∀ v ∈ A.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B.lat s) →
      (∀ v ∈ B.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ C.lat s) →
      ∀ v ∈ A.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ C.lat s := by
    intro A B C s hAB hBC v hv
    obtain ⟨c, hc, hcv⟩ := hAB v hv
    obtain ⟨c', hc', hcv'⟩ := hBC _ hcv
    exact ⟨c' * c, mul_ne_zero hc' hc, by rwa [map_mul, mul_smul]⟩
  exact fun s hs => ⟨step s (h s hs).1 (h' s hs).1, step s (h' s hs).2 (h s hs).2⟩

end Generic

theorem length_classList {K : Type} {q m : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ}
    (hQ : Q.IsHomogeneous m) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = m := by
  have h := hQ (mem_support_iff.1 hμ)
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset, ← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Ba.Statement.{0,0,0} O Ω ι := by
  intro O _ _ _ Ω _ _ K _ ι _
  classical
  intro x d N V _ _ E E' E'' hM h1 h2 k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h13 : SameGeneric O x E E'' := sameGeneric_comp h1 h2
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hMB, hbir, hEB⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hM N 2 V ![E, E', E''] (by
      intro j
      fin_cases j
      · exact sameGeneric_self E
      · exact h1
      · exact h13)
  have hM' : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hMB).2
  have p0 : IsPull O x z E (EB 0) := (hEB 0).1
  have p1 : IsPull O x z E' (EB 1) := (hEB 1).1
  have p2 : IsPull O x z E'' (EB 2) := (hEB 2).1
  have fr : ∀ j, IsFlagFrame (joinCoord x z) (EB j) w (b j) := fun j => (hEB j).2
  have tri : ∀ i j : Fin N, i < j → w.repr (w i) j = 0 := by
    intro i j hij
    simp [Module.Basis.repr_self, Finsupp.single_apply, ne_of_lt hij]
  have pair : ∀ i j, SameGeneric O (joinCoord x z) (EB i) (EB j) →
      SameGenericFibre ϖ (EB i) (EB j) ∧ ∃ f g : Fin N → MRing (Sum.elim ι ι') O,
        IsFlagPair ϖ (joinCoord x z) (EB i) (EB j) w w (b i) (b j) f g := fun i j hs =>
    GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hM' N V (EB i) (EB j) hs
      w w (b i) (b j) (fr i) (fr j) tri
  have s01 := (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1).2.1 h1
  have s12 := (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E' E'' K' ι' z (EB 1) (EB 2) p1 p2).2.1 h2
  have s02 := (GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E'' K' ι' z (EB 0) (EB 2) p0 p2).2.1 h13
  obtain ⟨g01, f01, d01, c01⟩ := pair 0 1 s01
  obtain ⟨g12, f12, d12, c12⟩ := pair 1 2 s12
  obtain ⟨-, f02, d02, c02⟩ := pair 0 2 s02
  obtain ⟨-, f10, d10, c10⟩ := pair 1 0 (sameGeneric_flip s01)
  have num : ∀ {A B : ChartBundle O (mseg x) N V} (i j : Fin 3) (f g : Fin N → MRing (Sum.elim ι ι') O),
      SameGeneric O x A B → IsPull O x z A (EB i) → IsPull O x z B (EB j) →
      IsFlagPair ϖ (joinCoord x z) (EB i) (EB j) w w (b i) (b j) f g →
      ck O x d N A B k L Q = ∑ μ ∈ Q.support, Q.coeff μ *
        pairNum (pointIdeal O (joinCoord x z)) (b i) (b j) f g (psumExpansion N k)
          (classList (fun j => pullDeg (K' := K') (L j)) μ) := by
    intro A B i j f g hs pi pj hf
    exact (GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V A B hs K' ι' z hMB hbir (EB i) (EB j) pi pj
      w w (b i) (b j) f g hf).1 k hk1 hk2 q L Q hQ
  have coc := fun μ (hμ : μ ∈ Q.support) =>
    GlobalTheory.T.pair_cocycle O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hM' N V (EB 0) (EB 1) (EB 2)
      g01 g12 w w w (b 0) (b 1) (b 2) f01 d01 f12 d12 f02 d02 c01 c12 c02 k (psumExpansion N k)
      (psumExpansion N k) (psumExpansion N k) (isPairExpansion_psum N k) (isPairExpansion_psum N k)
      (isPairExpansion_psum N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)
      (by rw [length_classList _ hQ hμ]; omega)
  refine ⟨?_, ?_⟩
  · rw [num 0 2 f02 d02 h13 p0 p2 c02, num 0 1 f01 d01 h1 p0 p1 c01,
      num 1 2 f12 d12 h2 p1 p2 c12, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [(coc μ hμ).1, mul_add]
  · rw [num 1 0 f10 d10 (sameGeneric_flip h1) p1 p0 c10, num 0 1 f01 d01 h1 p0 p1 c01,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [(coc μ hμ).2 f10 d10 (psumExpansion N k) c10 (isPairExpansion_psum N k), mul_neg]

end GlobalTheory.CompanionTheory.Ar.Num.Cocycle
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementAStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_bundle_statement_a : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Ba.Statement.{0,0,0} O Ω ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.Cocycle.main | exact GlobalTheory.CompanionTheory.Ar.Num.Cocycle.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.Cocycle.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementD
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatement
namespace GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.proof GlobalTheory.T.flag_independence

end GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | exact GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementD
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.Constants

theorem cycEval_natCast_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Ideal (MRing ι O) → ℤ) (P : Ideal (MRing ι O)) (c : MRing ι O) (n : ℕ) :
    cycEval F (fun W => (n : ℤ) * divCycle P c W) = (n : ℤ) * cycEval F (divCycle P c) := by
  unfold cycEval
  have hfin : (Function.support fun W => divCycle P c W * F W).Finite :=
    (ScalarQuotient.divCycle_support_finite P c).subset fun W hW => by
      rw [Function.mem_support] at hW ⊢
      exact fun h0 => hW (by rw [h0, zero_mul])
  rw [mul_finsum' _ _ hfin]
  exact finsum_congr fun W => by ring

theorem length_classList {K : Type} {q : ℕ} (cls : Fin q → K → ℤ) {Q : MvPolynomial (Fin q) ℤ} {e : ℕ}
    (hQ : Q.IsHomogeneous e) {μ : Fin q →₀ ℕ} (hμ : μ ∈ Q.support) :
    (classList cls μ).length = e := by
  have h := hQ (MvPolynomial.mem_support_iff.mp hμ)
  have h2 : Finsupp.degree μ = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact h
  rw [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  simpa [Finsupp.sum, Finsupp.degree_apply] using h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Bd.Statement.{0,0,0} O Ω ι := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' g hg hmod hlat k hk1 hk2 q L Q hQ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg hϖ
  have hsame : SameGeneric O x E E' := fun s hs =>
    ⟨fun v hv => ⟨_, hg, (hlat s hs _).2 ⟨v, hv, rfl⟩⟩, fun v hv => by
      obtain ⟨e, he, rfl⟩ := (hlat s hs v).1 hv
      exact ⟨_, hg, E.stable s _ (Subalgebra.algebraMap_mem _ _) _
        (E.stable s _ (Subalgebra.algebraMap_mem _ _) _ he)⟩⟩
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hJ, hbir, hall⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hmod N 1 V ![E, E'] (by
      intro j
      fin_cases j
      · exact fun s hs => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
          fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
      · exact hsame)
  have p0 : IsPull O x z E (EB 0) := (hall 0).1
  have p1 : IsPull O x z E' (EB 1) := (hall 1).1
  have hpull := GlobalTheory.T.chart_bundle_base_extension_unique O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) p0 p1
  have hsameJ := hpull.2.1 hsame
  have hscJ := hpull.2.2 _ hlat
  have hmodJ : IsModelOver (pointIdeal O (joinCoord x z)) d :=
    ((BundleExamples.isModelOver_iff O _ d).1 hJ).2
  obtain ⟨-, f, f', hpair⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hmodJ N V
    (EB 0) (EB 1) hsameJ w w (b 0) (b 1) (hall 0).2 (hall 1).2 (fun i j hij => by
      simp [Module.Basis.repr_self, hij.ne])
  have hnum := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hmod N V E E' hsame K' ι' z hJ hbir (EB 0) (EB 1) p0 p1
    w w (b 0) (b 1) f f' hpair
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have hroot := hnum.2 (k - 1) (psum (Fin N) ℤ (k - 1)) (psum_isSymmetric _ _ _)
    (isHomogeneous_psum N (k - 1)) (by omega) q L Q hQ'
  have hP : (pointIdeal O (joinCoord x z)).IsPrime := hmodJ.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing (Sum.elim ι ι') O) ∉ pointIdeal O (joinCoord x z) := by
    intro a ha hmem
    have h1 : a ∈ (pointIdeal O (joinCoord x z)).comap (C : O →+* MRing (Sum.elim ι ι') O) := hmem
    rw [hmodJ.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  have hdiv : ∀ (v : Oˣ) (m : ℕ),
      rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ((v : O) * ϖ ^ m) =
        (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ := by
    intro v m
    rw [hroot _ (mul_ne_zero v.ne_zero (pow_ne_zero _ hϖ.ne_zero)), hroot _ hϖ.ne_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [ScalarQuotient.divCycle_const _ hC hϖ.ne_zero v m, cycEval_natCast_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [hnum.1 k hk1 hk2 q L Q hQ, hdiv, hroot _ hϖ.ne_zero, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [GlobalTheory.T.scalar_quotient_statement O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) d hmodJ N V (EB 0) (EB 1) n u
      hscJ w w (b 0) (b 1) f f' hpair k (psumExpansion N k) (isPairExpansion_psum N k) _
      (by rw [length_classList _ hQ hμ]; omega)]
    ring
  · intro m n' h w' hw' hm hEq
    obtain ⟨W, rfl⟩ := hw'
    by_cases h0 : h = 0
    · subst h0
      have hn' : n' = 0 := by
        by_contra hne
        rw [zero_pow hne, mul_zero] at hEq
        exact pow_ne_zero m hg hEq
      subst hn'
      have hnm : n * m = 0 := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) W _ _ ?_
        rw [pow_zero, mul_one] at hEq ⊢
        rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, hEq]
      have hn0 : n = 0 := by
        rcases Nat.mul_eq_zero.mp hnm with h | h
        · exact h
        · omega
      subst hn0
      rw [hdiv u 0]
      simp
    · obtain ⟨a, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      have hnm : n * m = a * n' := by
        refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u ^ m) (W * v ^ n') _ _ ?_
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        rw [pow_mul, pow_mul, ← mul_pow, hEq, mul_pow, mul_assoc]
      have hnm' : (n : ℤ) * m = a * n' := by exact_mod_cast hnm
      rw [hdiv u n, hdiv v a]
      linear_combination rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q ϖ * hnm'

end GlobalTheory.CompanionTheory.Ar.Num.Constants
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementDStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_bundle_statement_d : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.Bd.Statement.{0,0,0} O Ω ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.Constants.main | exact GlobalTheory.CompanionTheory.Ar.Num.Constants.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.Constants.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegree
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

private theorem ae_fibre_encard_eq {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n)))
    (hss : IsScaleStable S) (hsc : IsSigmaCompact S) (δ : ℕ)
    (hgen : ∀ᵐ (π : Fin (e + 1) → Fin n → ℂ), ∀ᵐ (w : EuclideanSpace ℂ (Fin (e + 1))),
      cntOver S π w = (δ : ℝ≥0∞)) :
    ∀ᵐ (π : Fin (e + 1) → Fin n → ℂ), (fibrePts S π).encard = δ := by
  let T : ℝ≥0∞ → ℝ≥0∞ := fun x => if x = (δ : ℝ≥0∞) then 0 else 1
  have hT : Measurable T := Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
  have hcross := GlobalTheory.T.ball_average_fibre_count n e S hss hsc T hT
  have hlhs : ∫⁻ (π : Fin (e + 1) → Fin n → ℂ), matGauss π *
      ∫⁻ (w : EuclideanSpace ℂ (Fin (e + 1))) in Metric.ball 0 1, T (cntOver S π w) = 0 := by
    have hae : (fun π : Fin (e + 1) → Fin n → ℂ => matGauss π *
        ∫⁻ (w : EuclideanSpace ℂ (Fin (e + 1))) in Metric.ball 0 1, T (cntOver S π w))
        =ᵐ[volume] fun _ => 0 := by
      filter_upwards [hgen] with π hπ
      have hz : (fun w => T (cntOver S π w))
          =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1)] fun _ => 0 := by
        filter_upwards [ae_restrict_of_ae hπ] with w hw
        simp only [T, hw, if_true]
      rw [lintegral_congr_ae hz, lintegral_zero, mul_zero]
    rw [lintegral_congr_ae hae, lintegral_zero]
  rw [hlhs] at hcross
  have hball : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hrhs : ∫⁻ (π : Fin (e + 1) → Fin n → ℂ), matGauss π * T (cntOver S π (firstCoordVec (e + 1))) = 0 :=
    (mul_eq_zero.mp hcross.symm).resolve_left hball
  have hp : Measurable (fun π : Fin (e + 1) → Fin n → ℂ => (π, firstCoordVec (e + 1))) :=
    measurable_id.prodMk measurable_const
  have hmeasc := Measurable.comp
    (g := fun p : (Fin (e + 1) → Fin n → ℂ) × EuclideanSpace ℂ (Fin (e + 1)) => cntOver S p.1 p.2)
    (f := fun π : Fin (e + 1) → Fin n → ℂ => (π, firstCoordVec (e + 1))) (GlobalTheory.T.measurable_fibre_count_over n (e + 1) S hsc) hp
  have hmg : Measurable (matGauss : (Fin (e + 1) → Fin n → ℂ) → ℝ≥0∞) := by
    unfold matGauss
    fun_prop
  have hz := (lintegral_eq_zero_iff (hmg.mul (hT.comp hmeasc))).mp hrhs
  filter_upwards [hz] with π hπ
  have hg : matGauss π ≠ 0 := by
    unfold matGauss
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hT0 : T (cntOver S π (firstCoordVec (e + 1))) = 0 :=
    (mul_eq_zero.mp hπ).resolve_left hg
  have hc : cntOver S π (firstCoordVec (e + 1)) = (δ : ℝ≥0∞) := by
    by_contra hne
    simp only [T, hne, if_false, one_ne_zero] at hT0
  have hc' : (((fibrePts S π).encard : ℕ∞) : ℝ≥0∞) = ((δ : ℕ∞) : ℝ≥0∞) := by
    rw [ENat.toENNReal_coe]
    exact hc
  exact ENat.toENNReal_inj.mp hc'

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
    ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, (fibrePts (coneSet h W) π).encard = δ := by
  intro n e δ h W f hW hf hd
  apply ae_fibre_encard_eq (coneSet h W) (isScaleStable_coneSet h hW)
    (by simpa using isSigmaCompact_cone_inter h W (A := Set.univ) isOpen_univ) δ
  filter_upwards [GroundTheory.Heights₂.Heights.ConeFibreDegree.full n e δ h W f hW hf hd] with π hπ
  filter_upwards [hπ] with w hw
  show ((fibreCount h W π w : ℕ∞) : ℝ≥0∞) = _
  rw [hw]
  rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AeFibrePointsCardEqDegreeStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_fibre_points_card_eq_degree : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
    ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, (fibrePts (coneSet h W) π).encard = δ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree | exact GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericLinearEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericLinearEquiv
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.CkTransport

theorem mseg_restrict {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    {Ω : Type} [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    mseg x (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.restrictChart s) ≠ 0 := by
  unfold mseg at hs ⊢
  rw [Finset.prod_ne_zero_iff] at hs ⊢
  intro k _
  exact hs (Sum.inl k) (Finset.mem_univ _)

theorem pull_transport (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V] {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁]
    (e : V ≃ₗ[Ω] V₁) (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁)
    (h : ∀ s, mseg x s ≠ 0 → ∀ v, e v ∈ F.lat s ↔ v ∈ E.lat s)
    (EB : ChartBundle O (mseg (joinCoord x z)) N V) (FB : ChartBundle O (mseg (joinCoord x z)) N V₁)
    (hE : IsPull O x z E EB) (hF : IsPull O x z F FB) :
    ∀ s, mseg (joinCoord x z) s ≠ 0 → ∀ v, e v ∈ FB.lat s ↔ v ∈ EB.lat s := by
  intro s hs v
  have hr := h _ (mseg_restrict x z s hs)
  have key : FB.lat s = (EB.lat s).map (e : V →+ V₁) := by
    rw [hE s hs, hF s hs, AddMonoidHom.map_closure]
    congr 1
    ext u
    constructor
    · rintro ⟨a, ha, t, ht, rfl⟩
      refine ⟨a • e.symm t, ⟨a, ha, e.symm t, (hr _).1 (by simpa using ht), rfl⟩, ?_⟩
      simp
    · rintro ⟨_, ⟨a, ha, t, ht, rfl⟩, rfl⟩
      exact ⟨a, ha, e t, (hr _).2 ht, by simp⟩
  rw [key]
  constructor
  · rintro ⟨u, hu, huv⟩
    have : u = v := e.injective huv
    exact this ▸ hu
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem frame_transport {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} (y : (Σ k, ι k) → Ω) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module Ω V] {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁]
    (e : V ≃ₗ[Ω] V₁) (E : ChartBundle O (segreVec y) N V) (F : ChartBundle O (segreVec y) N V₁)
    (h : ∀ s, segreVec y s ≠ 0 → ∀ v, e v ∈ F.lat s ↔ v ∈ E.lat s)
    (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ) (hw : IsFlagFrame y E w b) :
    IsFlagFrame y F (w.map e) b := by
  refine ⟨fun c hc i => ?_⟩
  rw [← hw.graded c hc i]
  ext u
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨e.symm v, (h c hc _).1 (by simpa using hv), ?_, ?_⟩
    · simpa using h1
    · simpa using h2
  · rintro ⟨v, hv, h1, h2⟩
    refine ⟨e v, (h c hc _).2 hv, ?_, ?_⟩
    · simpa using h1
    · simpa using h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (e : V ≃ₗ[Ω] V₁) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), SameGeneric O x E E' → (∀ s, mseg x s ≠ 0 → ∀ v, (e v ∈ F.lat s ↔ v ∈ E.lat s) ∧ (e v ∈ F'.lat s ↔ v ∈ E'.lat s)) → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = ck O x d N E E' k L Q) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N F G L Q a = rootNum O x d N E G L Q a) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hW N V _ _ V₁ _ _ e E E' F F' hEE' he
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hFF' : SameGeneric O x F F' := by
    intro s hs
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨c, hc, h⟩ := (hEE' s hs).1 (e.symm v) ((he s hs _).1.1 (by simpa using hv))
      exact ⟨c, hc, by simpa using (he s hs _).2.2 h⟩
    · obtain ⟨c, hc, h⟩ := (hEE' s hs).2 (e.symm v) ((he s hs _).2.1 (by simpa using hv))
      exact ⟨c, hc, by simpa using (he s hs _).1.2 h⟩
  have hEE : SameGeneric O x E E := fun s _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hW', hfn, hj⟩ :=
    GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hW N 1 V ![E, E'] (by
      intro j
      fin_cases j
      · exact hEE
      · exact hEE')
  have hp0 : IsPull O x z E (EB 0) := (hj 0).1
  have hp1 : IsPull O x z E' (EB 1) := (hj 1).1
  have hB : SameGeneric O (joinCoord x z) (EB 0) (EB 1) :=
    (GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve O Ω K ι x N V E E' K' ι' z (EB 0) (EB 1) hp0 hp1).2.1 hEE'
  obtain ⟨-, f, g, hfp⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d
    ((GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O _ d).1 hW').2 N V (EB 0) (EB 1) hB w w (b 0) (b 1) (hj 0).2 (hj 1).2
    (fun i j hij => by simp [Finsupp.single_apply, hij.ne])
  obtain ⟨FB, hF⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V₁ F).1 K' ι' z
  obtain ⟨FB', hF'⟩ := (GlobalTheory.CompanionTheory.Ar.Num.PullExists.main O Ω K ι x N V₁ F').1 K' ι' z
  have hfpF : IsFlagPair ϖ (joinCoord x z) FB FB' (w.map e) (w.map e) (b 0) (b 1) f g := by
    refine ⟨frame_transport _ e (EB 0) FB
        (pull_transport O x z e E F (fun s hs v => (he s hs v).1) _ _ hp0 hF) w _ hfp.flag,
      frame_transport _ e (EB 1) FB'
        (pull_transport O x z e E' F' (fun s hs v => (he s hs v).2) _ _ hp1 hF') w _ hfp.flag',
      fun i j hij => ?_, hfp.vertical, fun i => ?_⟩
    · rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg hij.ne]
    · have := hfp.generic i
      rw [Module.Basis.repr_self] at this ⊢
      exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hW N V E E' hEE' K' ι' z hW' hfn (EB 0) (EB 1)
    hp0 hp1 w w (b 0) (b 1) f g hfp
  obtain ⟨h3, h4⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hW N V₁ F F' hFF' K' ι' z hW' hfn FB FB'
    hF hF' (w.map e) (w.map e) (b 0) (b 1) f g hfpF
  refine ⟨fun k hk hkd q L Q hQ => ?_, fun c G hG hc hcd q L Q hQ a ha => ?_⟩
  · rw [h1 k hk hkd q L Q hQ, h3 k hk hkd q L Q hQ]
  · rw [h2 c G hG hc hcd q L Q hQ a ha, h4 c G hG hc hcd q L Q hQ a ha]

end GlobalTheory.CompanionTheory.Ar.Num.CkTransport
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericLinearEquivStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_generic_linear_equiv : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (e : V ≃ₗ[Ω] V₁) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), SameGeneric O x E E' → (∀ s, mseg x s ≠ 0 → ∀ v, (e v ∈ F.lat s ↔ v ∈ E.lat s) ∧ (e v ∈ F'.lat s ↔ v ∈ E'.lat s)) → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = ck O x d N E E' k L Q) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N F G L Q a = rootNum O x d N E G L Q a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CkTransport.main | exact GlobalTheory.CompanionTheory.Ar.Num.CkTransport.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CkTransport.main <;> assumption)
end
end
