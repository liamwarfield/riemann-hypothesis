module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DescentRelationsFromModels

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Statements.AlgebraStatements.RelationsStatement
namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

def RelationsStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (Fin (r τ) → Ω), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (Fin (s τ) → Ω), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UniformizerModelPermModuleLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UniformizerModelPermModuleLattice
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.CkRelations

noncomputable def allOne (q : ℕ) : Fin q →₀ ℕ := ∑ j, Finsupp.single j 1

theorem toMultiset_allOne (q : ℕ) : (allOne q).toMultiset = Finset.univ.val := by
  ext j
  simp [allOne, Finsupp.count_toMultiset, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem degree_allOne (q : ℕ) : (allOne q).degree = q := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [allOne, map_sum]

theorem isHomogeneous_allOne (q n : ℕ) (h : q = n) :
    (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).IsHomogeneous n :=
  isHomogeneous_monomial _ ((degree_allOne q).trans h)

theorem classList_allOne {K : Type} (Q : List (K → ℤ)) :
    (classList Q.get (allOne Q.length)).Perm Q := by
  rw [← Multiset.coe_eq_coe, classList, Multiset.coe_toList, toMultiset_allOne, Fin.univ_val_map,
    List.ofFn_get]

theorem sum_allOne (q : ℕ) (F : (Fin q →₀ ℕ) → ℤ) :
    ∑ μ ∈ (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).support,
      (monomial (allOne q) (1 : ℤ) : MvPolynomial (Fin q) ℤ).coeff μ * F μ = F (allOne q) := by
  classical
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]

theorem classNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ)
    {Q Q' : List (K → ℤ)} (h : Q.Perm Q') (W : Ideal (MRing ι O)) :
    classNum cls H Q W = classNum cls H Q' W := by
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have : LeftCommutative (diffStep (K := K)) := ⟨fun a b f => by
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring⟩
  simp only [vNumL, vNum, intNum, mixedDiff, List.ofFn_get]
  rw [(h.append_left _).foldr_eq]

theorem key (hC : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (ϖ : O) (hϖ : Irreducible ϖ) (d : ℕ)
    (hM : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V)
    (hE : SameGeneric O x E E') (T : LocPair ι O (Fin N)) (b b' : Module.Basis (Fin N) Ω V)
    (hT : IsFlagPair ϖ x E E' b b' T.x T.x' T.f T.g) (k : ℕ) (hk : 1 ≤ k) (Q : List (K → ℤ))
    (hQ : Q.length + k = d + 1) :
    ck O x d N E E' k Q.get (monomial (allOne Q.length) 1) = T.ck (pointIdeal O x) k Q ∧
    ∀ a : O, a ≠ 0 →
      (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) Q.get (monomial (allOne Q.length) 1) a =
        laNum (pointIdeal O x) a T.x k Q := by
  obtain ⟨hK, hW⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
  obtain ⟨h1, h2⟩ := hC O ϖ hϖ Ω K ι x d hK hW N V E E'
    ((BundleExamples.sameGeneric_iff hϖ x E E').mp hE) b b' T.x T.x' T.f T.g hT
  refine ⟨?_, fun a ha => ?_⟩
  · refine (h1 k hk (by omega) _ (isPairExpansion_psum N k) _ Q.get _
      (isHomogeneous_allOne _ _ (by omega))).trans ?_
    rw [sum_allOne Q.length
      (fun μ => pairNum (pointIdeal O x) T.x T.x' T.f T.g (psumExpansion N k) (classList Q.get μ))]
    simp only [LocPair.ck, pairNum, classNum_perm _ _ (classList_allOne Q)]
  · have h3 := h2 (k - 1) _ (psum_isSymmetric _ _ (k - 1)) (isHomogeneous_psum N (k - 1)) (by omega)
      _ Q.get _ (isHomogeneous_allOne _ _ (by omega)) a ha
    rw [sum_allOne Q.length
      (fun μ => cycEval (fun W => classNum T.x (psum (Fin N) ℤ (k - 1)) (classList Q.get μ) W)
        (divCycle (pointIdeal O x) (C a)))] at h3
    simp only [classNum_perm _ _ (classList_allOne Q)] at h3
    unfold laNum
    exact congrArg _ h3

theorem main_of (hC : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement) : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → CkRelations O x d p φ Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (VL τ), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (VO τ), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM Sg r s p hp φ VL VO _ _ _ _ Lie W Om OmHT hS hR lie om hF
    k hk Q hQ
  obtain ⟨h, h1, h2⟩ := hR k hk (by omega) Q.length Q.get _
    (isHomogeneous_allOne _ _ (by omega))
  have hL := fun τ => (hF τ).1.elim fun b hb => hb.elim fun b' hb' =>
    key hC O Ω K ι x ϖ hϖ d hM _ _ _ _ (hS τ).1 (lie τ) b b' hb' k hk Q hQ
  have hO := fun τ => (hF τ).2.elim fun b hb => hb.elim fun b' hb' =>
    key hC O Ω K ι x ϖ hϖ d hM _ _ _ _ (hS τ).2 (om τ) b b' hb' k hk Q hQ
  refine ⟨h, fun τ => ?_, fun τ => ?_⟩
  · rw [← (hL τ).1, ← (hO τ).1, ← (hL τ).2 _ hp, h1 τ]
    push_cast
    ring
  · rw [← (hL (φ τ)).2 _ hp, h2 τ]
    push_cast
    ring

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → CkRelations O x d p φ Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (VL τ), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (VO τ), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om :=
  main_of GlobalTheory.T.chern_class_on_flag_pair

end GlobalTheory.CompanionTheory.CkRelations
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UniformizerModelPermModuleLatticeStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_model_perm_module_lattice : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {Sg : Type} {r s : Sg → ℕ} (p : ℕ), (p : O) ≠ 0 → ∀ (φ : Equiv.Perm Sg) {VL VO : Sg → Type} [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)] (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)), (∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ)) → CkRelations O x d p φ Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (VL τ), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (VO τ), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om := by
  first | exact @GlobalTheory.CompanionTheory.CkRelations.main | exact GlobalTheory.CompanionTheory.CkRelations.main | (intros; apply GlobalTheory.CompanionTheory.CkRelations.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHolds
namespace GlobalTheory.CompanionTheory.Ar.Num.TopRel

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem relations : GlobalTheory.CompanionTheory.Ar.Num.RelationsStatement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ ϖ hϖ d hmod hfn F _ _ _ n Sg _ r s p hp w χ φ D hD Lie W Om OmHT hB lie om hflag
  have hck := GlobalTheory.T.lattice_family_ckRelations O Ω K ι x d hmod hfn p hp w χ φ D hD Lie W Om OmHT hB
  have hp0 : (p : O) ≠ 0 := hD.char.1
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, he⟩ := hD.char.2.1
    have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
    rw [zero_pow h1] at he
    exact hp0 (by
      rcases mul_eq_zero.mp he.symm with h | h
      · exact absurd h hu.ne_zero
      · exact h)
  have hsame : ∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ) := by
    intro τ
    constructor
    · intro c hc
      obtain ⟨h1, h2, -, -⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h1, h2]
      refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
      · simpa using hinc.1 hv
      · exact hinc.2.1 hv
    · intro c hc
      obtain ⟨-, -, h3, h4⟩ := hB τ c hc
      have hinc := ((hD.base c hc).incl τ)
      rw [h3, h4]
      refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
      · exact hinc.2.2.2 hv
      · simpa using hinc.2.2.1 hv
  exact GlobalTheory.T.uniformizer_model_perm_module_lattice O Ω K ι x ϖ hϖ d hmod p hp0 φ (VL := fun τ => Fin (r τ) → Ω)
    (VO := fun τ => Fin (s τ) → Ω) Lie W Om OmHT hsame hck lie om hflag

end GlobalTheory.CompanionTheory.Ar.Num.TopRel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_relations_statement_holds : GlobalTheory.CompanionTheory.Ar.Num.RelationsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations | exact GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations <;> assumption)
end
