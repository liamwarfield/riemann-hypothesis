module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLatticeStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LaurentPolynomialCharacterIsMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LaurentPolynomialCharacterIsMonomial
noncomputable section

namespace GlobalTheory.RegSS

def monomialChar (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : ℕ) (a : Fin s → ℤ) :
    (Fin s → Fˣ) →* Ω where
  toFun t := algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, map_mul]

theorem characterMonomial : CharacterMonomial := by
  classical
  intro F Ω _ _ _ s f S c hf
  by_contra hno

  have hdiff : ∀ a, monomialChar F Ω s a ≠ f := by
    intro a hEq
    refine hno ⟨a, fun t => ?_⟩
    rw [← hEq]
    rfl

  let l : ((Fin s → Fˣ) →* Ω) →₀ Ω :=
    Finsupp.single f 1 - ∑ a ∈ S, Finsupp.single (monomialChar F Ω s a) (c a)
  have hvanish : Finsupp.linearCombination Ω
      (fun φ : (Fin s → Fˣ) →* Ω => (φ : (Fin s → Fˣ) → Ω)) l = 0 := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [l, map_sub, map_sum, Finsupp.linearCombination_single, one_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hf t]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = c a * algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
    rw [Algebra.smul_def, mul_comm]
  have hl0 : l = 0 := (linearIndependent_iff.mp (linearIndependent_monoidHom _ Ω)) l hvanish
  have hlf : l f = 1 := by
    simp only [l, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne' (hdiff a), sub_zero]
  rw [hl0, Finsupp.zero_apply] at hlf
  exact zero_ne_one hlf

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LaurentPolynomialCharacterIsMonomialStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentPolynomial_character_isMonomial : GlobalTheory.RegSS.CharacterMonomial := by
  first | exact @GlobalTheory.RegSS.characterMonomial | exact GlobalTheory.RegSS.characterMonomial | (intros; apply GlobalTheory.RegSS.characterMonomial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFieldsBaseChangeIsFieldIff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFieldsBaseChangeIsFieldIff
open GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem isField_pi_fin_iff {k : ℕ} (A : Fin k → Type) [∀ i, CommRing (A i)]
    [∀ i, Nontrivial (A i)] : IsField (∀ i, A i) ↔ k = 1 ∧ ∀ i, IsField (A i) := by
  constructor
  · intro h

    have hk : k = 1 := by
      rcases Nat.lt_trichotomy k 1 with hlt | heq | hgt
      · obtain ⟨a, b, hab⟩ := h.exists_pair_ne
        have hk0 : k = 0 := by omega
        subst hk0
        exact absurd (funext fun i => i.elim0) hab
      · exact heq
      · let i₀ : Fin k := ⟨0, by omega⟩
        let i₁ : Fin k := ⟨1, hgt⟩
        have hne : i₁ ≠ i₀ := by
          intro hij
          have := congrArg Fin.val hij
          simp [i₀, i₁] at this
        have hx : (Pi.single i₀ (1 : A i₀) : ∀ i, A i) ≠ 0 := by
          intro hx
          have := congrFun hx i₀
          simp at this
        obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
        have := congrFun hy i₁
        rw [Pi.mul_apply, Pi.single_eq_of_ne hne, zero_mul, Pi.one_apply] at this
        exact absurd this zero_ne_one
    refine ⟨hk, ?_⟩
    subst hk
    intro i
    have hdef : IsField (A default) := (RingEquiv.piUnique A).symm.toMulEquiv.isField h
    exact (Unique.eq_default i).symm ▸ hdef
  · rintro ⟨rfl, h⟩
    exact (RingEquiv.piUnique A).toMulEquiv.isField (h default)

theorem tensorFieldIff : TensorFieldIff := by
  intro F E _ _ _ _ P _ _ k K _ _ ⟨e⟩

  let φ : P ⊗[F] E ≃ₐ[F] ∀ i, K i ⊗[F] E :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      ((Algebra.TensorProduct.comm F _ E).trans
        ((Algebra.TensorProduct.piRight F F E K).trans
          (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F E (K i))))

  have : ∀ i, Nontrivial (K i ⊗[F] E) := fun i =>
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right (R := F) (M := K i) (N := E)
      (Algebra.linearMap F (K i)) (algebraMap F (K i)).injective
  rw [φ.toRingEquiv.toMulEquiv.isField_congr]
  exact isField_pi_fin_iff _

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFieldsBaseChangeIsFieldIffStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_fields_baseChange_isField_iff : GlobalTheory.RegSS.TensorFieldIff := by
  first | exact @GlobalTheory.RegSS.tensorFieldIff | exact GlobalTheory.RegSS.tensorFieldIff | (intros; apply GlobalTheory.RegSS.tensorFieldIff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleCentralizerPointsOfCommutantAdj
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleCentralizerPointsOfCommutantAdj
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

private lemma cT_mul_mul_eq_iff_mul_adj_eq_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J g : Matrix n n A} (hJ : IsUnit J.det) :
    cT s g * J * g = J ↔ g * adj s J g = 1 := by
  rw [mul_eq_one_comm, adj]
  constructor
  · intro h
    calc J⁻¹ * cT s g * J * g = J⁻¹ * (cT s g * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have key : J * (J⁻¹ * cT s g * J * g) = J := by rw [h, Matrix.mul_one]
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul] using key

theorem pointsCentraliser_of_commutant_of_adjoint :
    PointsCommutant → PointsAdjoint → PointsCentraliser := by
  intro hC hA F E _ _ _ _ n _ _ σ J γ hreg hAlg hPlus R _ _
  obtain ⟨hinj, hcomm⟩ := hC F E n σ J γ hreg hAlg hPlus R
  refine ⟨hinj, fun u => hA F E n σ J γ hreg R u, fun g => ?_⟩
  have hJ : IsUnit (J.map (inclE (F := F) R)).det := by
    have h := hreg.nondeg.map (inclE (F := F) R)
    rw [RingHom.map_det] at h
    exact h
  have hb : ((bc (inclE (F := F) R) γ : GL n (E ⊗[F] R)) : Matrix n n (E ⊗[F] R)) =
      (γ : Matrix n n E).map (inclE (F := F) R) := rfl
  simp only [centPts, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  unfold UPts UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    Units.ext_iff, Units.val_mul, hb]
  rw [cT_mul_mul_eq_iff_mul_adj_eq_one _ hJ]
  constructor
  · rintro ⟨hunit, hc⟩
    have hc' := congrArg Units.val hc.eq
    simp only [Units.val_mul, hb] at hc'
    obtain ⟨u, hu⟩ := (hcomm g).1 hc'
    have h1 : u * lConj σ J (γ : Matrix n n E) R u = 1 := by
      apply hinj
      rw [map_mul, hA F E n σ J γ hreg R u, hu, map_one, hunit]
    exact ⟨Units.mkOfMulEqOne u _ h1, h1, hu⟩
  · rintro ⟨u, hu, hg⟩
    have hu' : (u : LPts σ J (γ : Matrix n n E) R) * lConj σ J (γ : Matrix n n E) R u = 1 := hu
    refine ⟨?_, ?_⟩
    · rw [← hg, ← hA F E n σ J γ hreg R, ← map_mul, hu', map_one]
    · change g * _ = _ * g
      apply Units.ext
      simpa only [Units.val_mul, hb] using (hcomm g).2 ⟨u, hg⟩

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleCentralizerPointsOfCommutantAdjStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint : GlobalTheory.RegSS.PointsCommutant → GlobalTheory.RegSS.PointsAdjoint → GlobalTheory.RegSS.PointsCentraliser := by
  first | exact @GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | exact GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | (intros; apply GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatrices
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS.CptQuot

theorem continuous_adj {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ) (J : Matrix n n A) :
    Continuous (adj σ J) := by
  unfold adj
  have hc : Continuous (fun l : Matrix n n A => cT σ l) := by
    unfold Formalism.UG.cT
    exact (continuous_id.matrix_map hσ).matrix_transpose
  exact (continuous_const.matrix_mul hc).matrix_mul continuous_const

theorem exists_isCompact {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    {J : Matrix n n A} (hJ : IsUnit J.det) (γ : GL n A) {D : Set (Matrix n n A)}
    (hD : IsCompact D) :
    ∃ K : Set (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)), IsCompact K ∧
      ∀ g : (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)),
        ((g : GL n A) : Matrix n n A) ∈ D → g ∈ K := by
  have hca := continuous_adj σ hσ J
  let C : Set (Matrix n n A) := D ∩ {M | M * adj σ J M = 1 ∧ adj σ J M * M = 1 ∧
    M * (γ : Matrix n n A) = (γ : Matrix n n A) * M}
  have hCc : IsCompact C := by
    refine hD.inter_right ?_
    exact (isClosed_eq (continuous_id.matrix_mul hca) continuous_const).inter
      ((isClosed_eq (hca.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const)
          (continuous_const.matrix_mul continuous_id)))
  let u : C → GL n A := fun M => ⟨M.1, adj σ J M.1, M.2.2.1, M.2.2.2.1⟩
  have hu : ∀ M : C, u M ∈ (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := by
    intro M
    refine Subgroup.mem_inf.2 ⟨(mem_UJ_iff_adj_mul σ hJ (u M)).2 M.2.2.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact M.2.2.2.2.symm
  let f : C → (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := fun M => ⟨u M, hu M⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, hca.comp continuous_subtype_val⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro g hg
  have hg' := Subgroup.mem_inf.1 g.2
  have h1 := (mem_UJ_iff_mul_adj σ hJ (g : GL n A)).1 hg'.1
  have h2 := (mem_UJ_iff_adj_mul σ hJ (g : GL n A)).1 hg'.1
  have h3 : ((g : GL n A) : Matrix n n A) * γ = γ * (g : GL n A) := by
    have hc := congrArg Units.val (Subgroup.mem_centralizer_iff.1 hg'.2 γ (Set.mem_singleton γ))
    rw [Units.val_mul, Units.val_mul] at hc
    exact hc.symm
  refine ⟨⟨_, hg, h1, h2, h3⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rfl

theorem compactOfMatBounded (hL : TensorLattice) : CompactOfMatBounded := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hM
  have := quad_finite hreg.quad
  obtain ⟨hTR, -, hT2, -⟩ := hL F E
  obtain ⟨D, hD, hDg⟩ := hM
  let : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  have : IsTopologicalRing (E ⊗[F] AdeleRing (𝓞 F) F) := hTR
  have : T2Space (E ⊗[F] AdeleRing (𝓞 F) F) := hT2
  have hD' : IsCompact D := hD
  have hσ' : Continuous (sigR σ (AdeleRing (𝓞 F) F)) := continuous_sigR σ (AdeleRing (𝓞 F) F)
  have hJ' : IsUnit (J.map (inclE (F := F) (AdeleRing (𝓞 F) F))).det :=
    isUnit_det_map (inclE (F := F) (AdeleRing (𝓞 F) F)) hreg.nondeg
  have key : ∃ K : Set (centPts σ J γ (AdeleRing (𝓞 F) F)), IsCompact K ∧
      ∀ g : centPts σ J γ (AdeleRing (𝓞 F) F),
        ((g : GL n (E ⊗[F] AdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) ∈ D →
          g ∈ K :=
    exists_isCompact (sigR σ (AdeleRing (𝓞 F) F)) hσ' hJ'
      (bc (inclE (F := F) (AdeleRing (𝓞 F) F)) γ) hD'
  obtain ⟨K, hK, hKD⟩ := key
  have hδc : ∀ δ ∈ centRat σ J γ,
      bc (inclE (F := F) (AdeleRing (𝓞 F) F)) δ ∈ centPts σ J γ (AdeleRing (𝓞 F) F) := by
    intro δ hδ
    have hδ' := Subgroup.mem_inf.1 (show δ ∈ UJ (σ : E →+* E) J ⊓ Subgroup.centralizer {γ} from hδ)
    have hadj := (mem_UJ_iff_adj_mul (σ : E →+* E) hreg.nondeg δ).1 hδ'.1
    have hcomm := Subgroup.mem_centralizer_iff.1 hδ'.2 γ (Set.mem_singleton γ)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show _ ∈ UJ (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
      rw [mem_UJ_iff_adj_mul _ hJ']
      show adj (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
          ((δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F))) *
          (δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F)) = 1
      rw [adj_map (σ : E →+* E) (sigR σ (AdeleRing (𝓞 F) F)) (inclE (F := F) (AdeleRing (𝓞 F) F))
        (fun x => inclE_conj σ (AdeleRing (𝓞 F) F) x) hreg.nondeg, ← Matrix.map_mul, hadj,
        Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul, hcomm]
  refine ⟨?_⟩
  have himg : (QuotientGroup.mk '' K : Set (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
      ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
        (centPts σ J γ (AdeleRing (𝓞 F) F)))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨δ, hδ, hgδ⟩ := hDg g g.2
    refine ⟨g * ⟨_, hδc δ hδ⟩, hKD _ hgδ, ?_⟩
    exact QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hδ, rfl⟩))
  rw [← himg]
  exact hK.image QuotientGroup.continuous_mk

end GlobalTheory.RegSS.CptQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatricesStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_quotient_compact_of_bounded_matrices : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.CompactOfMatBounded := by
  first | exact @GlobalTheory.RegSS.CptQuot.compactOfMatBounded | exact GlobalTheory.RegSS.CptQuot.compactOfMatBounded | (intros; apply GlobalTheory.RegSS.CptQuot.compactOfMatBounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparate
noncomputable section

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem nonempty_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [Nontrivial A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m).toLinearMap (Ideal.Quotient.mkₐ_surjective F m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

theorem exists_eq_tmul_add_tmul {F E P : Type} [Field F] [CommRing E] [Algebra F E] [CommRing P]
    [Algebra F P] (b : Module.Basis (Fin 2) F E) (x : P ⊗[F] (E ⊗[F] F)) :
    ∃ p q : P, x = p ⊗ₜ (b 0 ⊗ₜ (1 : F)) + q ⊗ₜ (b 1 ⊗ₜ (1 : F)) := by
  induction x with
  | tmul p y =>
    obtain ⟨e, rfl⟩ := (TensorProduct.rid F E).symm.surjective y
    refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
    have hs := b.sum_repr e
    rw [Fin.sum_univ_two] at hs
    rw [TensorProduct.rid_symm_apply, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, hs]
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩

theorem separatingPoints : SeparatingPoints := by
  intro F E _ _ _ _ σ hσ P _ _ _ k K _ _ ⟨e⟩
  haveI := quad_finite hσ
  haveI := quad_nontrivial hσ
  obtain ⟨b, d, hb0, hb1, hd, hbb⟩ := quad_exists_basis hσ
  let pr : ∀ i, P →ₐ[F] K i := fun i => (Pi.evalAlgHom F K i).comp e.toAlgHom
  have hpr : ∀ i p, pr i p = e p i := fun _ _ => rfl
  haveI : ∀ i, Module.Finite F (K i) := fun i =>
    Module.Finite.of_surjective (pr i).toLinearMap fun y => by
      obtain ⟨p, hp⟩ := e.surjective (Pi.single i y)
      exact ⟨p, by simp [hpr, hp]⟩
  let χ : ∀ i, K i ⊗[F] E →ₐ[F] AlgebraicClosure F := fun i =>
    (nonempty_algHom_algebraicClosure F (K i ⊗[F] E)).some
  let π : ∀ i, P ⊗[F] (E ⊗[F] F) →ₐ[F] K i ⊗[F] E := fun i =>
    Algebra.TensorProduct.map (pr i) (Algebra.TensorProduct.rid F F E).toAlgHom
  have hπ : ∀ i p (y : E), π i (p ⊗ₜ (y ⊗ₜ (1 : F))) = e p i ⊗ₜ y := fun i p y => by
    simp [π, hpr]
  have hc : ∀ (p : P) (y : E), tConj3 P σ F (p ⊗ₜ (y ⊗ₜ (1 : F))) = p ⊗ₜ (σ y ⊗ₜ (1 : F)) :=
    fun p y => by simp [tConj3]
  refine ⟨fun i => (χ i).comp (π i), fun x hx => ?_, fun i hi x hx => ?_⟩
  · obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
    have key : ∀ i, e p i = 0 ∧ e q i = 0 := fun i => by
      obtain ⟨h1, h2⟩ := hx i
      have hm : (e q i ⊗ₜ[F] b 1 : K i ⊗[F] E) = (e q i ⊗ₜ[F] 1) * (1 ⊗ₜ[F] b 1) := by simp
      simp only [AlgHom.comp_apply, map_add (f := _), hc, hπ, hb0, hb1, map_one, TensorProduct.tmul_neg,
        map_neg] at h1 h2
      rw [hm, map_mul] at h1 h2
      have hδ : χ i (1 ⊗ₜ[F] b 1) ≠ 0 := fun h0 => by
        have : χ i (1 ⊗ₜ[F] b 1) * χ i (1 ⊗ₜ[F] b 1) = algebraMap F _ d := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hbb, mul_one,
            ← Algebra.TensorProduct.algebraMap_apply', AlgHom.commutes]
        rw [h0, zero_mul] at this
        exact hd ((map_eq_zero _).1 this.symm)
      have inj : ∀ y : K i, χ i (y ⊗ₜ[F] 1) = 0 → y = 0 := fun y hy =>
        (map_eq_zero ((χ i).comp Algebra.TensorProduct.includeLeft : K i →ₐ[F] _)).1 hy
      refine ⟨inj _ (by linear_combination (h1 + h2) / 2), inj _ ?_⟩
      exact (mul_eq_zero.1 (by linear_combination (h1 - h2) / 2)).resolve_right hδ
    have hp : p = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).1)
    have hq : q = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).2)
    simp [hp, hq]
  · have h0 : π i x = 0 := by
      by_contra h0
      obtain ⟨y, hy⟩ := hi.mul_inv_cancel h0
      have := congrArg (χ i) hy
      rw [map_mul, show χ i (π i x) = 0 from hx, zero_mul, map_one] at this
      exact zero_ne_one this
    have h1 : π i (tConj3 P σ F x) = tConj (K i) σ (π i x) := by
      obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
      simp only [map_add (f := _), hc, hπ, tConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgHom.comp_apply, h1, h0, map_zero, map_zero]

end GlobalTheory.RegSS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparateStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_factor_points_separate : GlobalTheory.RegSS.SeparatingPoints := by
  first | exact @GlobalTheory.RegSS.separatingPoints | exact GlobalTheory.RegSS.separatingPoints | (intros; apply GlobalTheory.RegSS.separatingPoints <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamily
noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.IdemTorus

section Lin

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι]
  [DecidableEq ι]

def idemLin (p : ι → Matrix n n A) (c : ι → A) : Matrix n n A := 1 + ∑ k, (c k - 1) • p k

theorem idemLin_mul_idem {p : ι → Matrix n n A} (hi : ∀ k, p k * p k = p k)
    (ho : ∀ k l, k ≠ l → p k * p l = 0) (c : ι → A) (k : ι) :
    idemLin p c * p k = c k • p k := by
  unfold idemLin
  rw [add_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, hi, sub_smul, one_smul]; abel
  · intro l _ hl; rw [smul_mul_assoc, ho l k hl, smul_zero]
  · simp

theorem idemLin_mul {p : ι → Matrix n n A} (hi : ∀ k, p k * p k = p k)
    (ho : ∀ k l, k ≠ l → p k * p l = 0) (c c' : ι → A) :
    idemLin p (c * c') = idemLin p c * idemLin p c' := by
  have h : idemLin p c * idemLin p c' = idemLin p c + ∑ k, (c' k - 1) • (idemLin p c * p k) := by
    conv_lhs => rw [show idemLin p c' = 1 + ∑ k, (c' k - 1) • p k from rfl]
    rw [mul_add, mul_one, Finset.mul_sum]
    simp_rw [mul_smul_comm]
  rw [h]
  simp_rw [idemLin_mul_idem hi ho, smul_smul]
  unfold idemLin
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul]; congr 1; simp only [Pi.mul_apply]; ring

theorem idemLin_one (p : ι → Matrix n n A) : idemLin p 1 = 1 := by
  simp [idemLin]

theorem idemLin_commute (p : ι → Matrix n n A) (x : Matrix n n A) (h : ∀ k, Commute x (p k))
    (c : ι → A) : Commute x (idemLin p c) :=
  (Commute.one_right x).add_right (Commute.sum_right _ _ _ fun k _ => (h k).smul_right _)

theorem idemLin_map {B : Type} [CommRing B] (g : A →+* B) (p : ι → Matrix n n A) (c : ι → A) :
    (idemLin p c).map g = idemLin (fun k => (p k).map g) (fun k => g (c k)) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [idemLin, Matrix.sum_apply, Matrix.one_apply, map_sum, apply_ite]

theorem adj_sum (σ : A →+* A) (J : Matrix n n A) (M : ι → Matrix n n A) :
    adj σ J (∑ k, M k) = ∑ k, adj σ J (M k) := by
  have : cT σ (∑ k, M k) = ∑ k, cT σ (M k) := by
    ext i j; simp [cT, Matrix.sum_apply, map_sum]
  simp only [adj, this, Finset.mul_sum, Finset.sum_mul]

theorem adj_idemLin (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det) (p : ι → Matrix n n A)
    (c : ι → A) : adj σ J (idemLin p c) = idemLin (fun k => adj σ J (p k)) (fun k => σ (c k)) := by
  unfold idemLin
  rw [adj_add, adj_one σ hJ, adj_sum]
  simp_rw [adj_smul, map_sub, map_one]

theorem idemLin_swap {s : ℕ} (p : Fin s ⊕ Fin s → Matrix n n A) (c : Fin s ⊕ Fin s → A) :
    idemLin (fun k => p k.swap) c = idemLin p (fun k => c k.swap) := by
  unfold idemLin
  congr 1
  have := Equiv.sum_comp (Equiv.sumComm (Fin s) (Fin s)) (fun k => (c k.swap - 1) • p k)
  simpa [Sum.swap_swap] using this

end Lin

end GlobalTheory.RegSS.IdemTorus

namespace GlobalTheory.RegSS.IdemTorus

section Torus

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def idemFam (σ : E →ₐ[F] E) (J : Matrix n n E) {s : ℕ} (ε : Fin s → Matrix n n E) :
    Fin s ⊕ Fin s → Matrix n n E :=
  Sum.elim ε (fun i => adj (σ : E →+* E) J (ε i))

def idemCoef (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (t : Fin s → Rˣ) :
    Fin s ⊕ Fin s → E ⊗[F] R :=
  Sum.elim (fun i => (1 : E) ⊗ₜ[F] (t i : R)) (fun i => (1 : E) ⊗ₜ[F] (((t i)⁻¹ : Rˣ) : R))

theorem idemCoef_one (R : Type) [CommRing R] [Algebra F R] {s : ℕ} :
    idemCoef (F := F) (E := E) R (1 : Fin s → Rˣ) = 1 := by
  funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.one_def]

theorem idemCoef_mul (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (a b : Fin s → Rˣ) :
    idemCoef (F := F) (E := E) R (a * b) = idemCoef R a * idemCoef R b := by
  funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

theorem idemCoef_swap (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (t : Fin s → Rˣ) :
    (fun k => idemCoef (F := F) (E := E) R t k.swap) = idemCoef R t⁻¹ := by
  funext k; cases k <;> simp [idemCoef]

theorem sigR_idemCoef (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {s : ℕ}
    (t : Fin s → Rˣ) (k : Fin s ⊕ Fin s) : sigR σ R (idemCoef R t k) = idemCoef R t k := by
  cases k <;> simp [idemCoef, sigR]

theorem tmul_right_injective {e : E} (he : e ≠ 0) (R : Type) [CommRing R] [Algebra F R] :
    Function.Injective (fun x : R => e ⊗ₜ[F] x) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F he
  intro x y h
  have := congrArg (fun z => TensorProduct.lid F R (LinearMap.rTensor R φ z)) h
  simpa [hφ] using this

end Torus

end GlobalTheory.RegSS.IdemTorus

namespace GlobalTheory.RegSS.IdemTorus

section Main

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

theorem idemFam_facts {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E} (hR : IsRegular σ J γ)
    (hA : ClauseAlg σ J γ) {s : ℕ} {ε : Fin s → Matrix n n E} (h : IsIdemFamily σ J γ ε) :
    (∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k) ∧
    (∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0) ∧
    (∀ k, adj (σ : E →+* E) J (idemFam σ J ε k) = idemFam σ J ε k.swap) ∧
    ∀ k, (γ : Matrix n n E) * idemFam σ J ε k = idemFam σ J ε k * (γ : Matrix n n E) := by
  obtain ⟨hmem, -, hid, hor, had⟩ := h
  have hcomm : ∀ a b : Matrix n n E, a ∈ genAlg (γ : Matrix n n E) → b ∈ genAlg (γ : Matrix n n E) →
      a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : genAlg (γ : Matrix n n E)) ⟨b, hb⟩)
  have hmem' : ∀ k, idemFam σ J ε k ∈ genAlg (γ : Matrix n n E) := by
    intro k
    cases k with
    | inl i => exact hmem i
    | inr i => exact hA.2.2.2.2.1 _ (hmem i)
  refine ⟨?_, ?_, ?_, fun k => commute_of_mem_genAlg rfl (hmem' k)⟩
  · intro k
    cases k with
    | inl i => exact hid i
    | inr i =>
      simp only [idemFam, Sum.elim_inr]
      rw [← adj_mul _ hR.nondeg, hid]
  · intro k l hkl
    cases k with
    | inl i =>
      cases l with
      | inl j => exact hor i j (fun e => hkl (congrArg _ e))
      | inr j => exact had i j
    | inr i =>
      cases l with
      | inl j =>
        simp only [idemFam, Sum.elim_inl, Sum.elim_inr]
        rw [hcomm _ (ε j) (hA.2.2.2.2.1 _ (hmem i)) (hmem j), had]
      | inr j =>
        simp only [idemFam, Sum.elim_inr]
        rw [← adj_mul _ hR.nondeg, hor j i (fun e => hkl (congrArg _ e.symm)), adj_zero]
  · intro k
    cases k with
    | inl i => rfl
    | inr i => exact adj_adj _ hR.quad.invol hR.herm hR.nondeg _

def idemFamR (σ : E →ₐ[F] E) (J : Matrix n n E) {s : ℕ} (ε : Fin s → Matrix n n E) (R : Type)
    [CommRing R] [Algebra F R] : Fin s ⊕ Fin s → Matrix n n (E ⊗[F] R) :=
  fun k => (idemFam σ J ε k).map (inclE (F := F) R)

variable {σ : E →ₐ[F] E} {J : Matrix n n E} {s : ℕ} {ε : Fin s → Matrix n n E}

theorem idemFamR_idem (hi : ∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k)
    (R : Type) [CommRing R] [Algebra F R] (k : Fin s ⊕ Fin s) :
    idemFamR σ J ε R k * idemFamR σ J ε R k = idemFamR σ J ε R k := by
  simp only [idemFamR]; rw [← Matrix.map_mul, hi]

theorem idemFamR_orth (ho : ∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0)
    (R : Type) [CommRing R] [Algebra F R] (k l : Fin s ⊕ Fin s) (hkl : k ≠ l) :
    idemFamR σ J ε R k * idemFamR σ J ε R l = 0 := by
  simp only [idemFamR]; rw [← Matrix.map_mul, ho k l hkl, Matrix.map_zero _ (map_zero _)]

def idemHom (hi : ∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k)
    (ho : ∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0) (R : Type) [CommRing R]
    [Algebra F R] : (Fin s → Rˣ) →* Matrix n n (E ⊗[F] R) where
  toFun t := idemLin (idemFamR σ J ε R) (idemCoef R t)
  map_one' := by simp only [idemCoef_one]; exact idemLin_one _
  map_mul' a b := by
    simp only [idemCoef_mul]
    exact idemLin_mul (idemFamR_idem hi R) (idemFamR_orth ho R) _ _

end Main

theorem subtorusOfIdempotents : SubtorusOfIdempotents := by
  intro F E _ _ _ _ n _ _ σ J γ hR hA s ε h
  obtain ⟨hi, ho, had, hγ⟩ := idemFam_facts hR hA h
  have hJ' : ∀ (R : Type) [CommRing R] [Algebra F R], IsUnit (J.map (inclE (F := F) R)).det :=
    fun R _ _ => isUnit_det_map _ hR.nondeg
  have hadR : ∀ (R : Type) [CommRing R] [Algebra F R] (k : Fin s ⊕ Fin s),
      adj (sigR σ R) (J.map (inclE (F := F) R)) (idemFamR σ J ε R k) = idemFamR σ J ε R k.swap := by
    intro R _ _ k
    simp only [idemFamR]
    rw [adj_map (σ : E →+* E) (sigR σ R) (inclE R) (inclE_conj σ R) hR.nondeg, had]
  have hadjHom : ∀ (R : Type) [CommRing R] [Algebra F R] (t : Fin s → Rˣ),
      adj (sigR σ R) (J.map (inclE (F := F) R)) (idemHom hi ho R t) = idemHom hi ho R t⁻¹ := by
    intro R _ _ t
    show adj _ _ (idemLin _ _) = idemLin _ _
    rw [adj_idemLin _ (hJ' R)]
    have e1 : (fun k => adj (sigR σ R) (J.map (inclE (F := F) R)) (idemFamR σ J ε R k)) =
        fun k => idemFamR σ J ε R k.swap := funext (hadR R)
    have e2 : (fun k => sigR σ R (idemCoef R t k)) = idemCoef R t := funext (sigR_idemCoef σ R t)
    rw [e1, e2, idemLin_swap, idemCoef_swap]
  refine ⟨⟨(fun R _ _ => (idemHom hi ho R).toHomUnits), ?_, ?_, ?_⟩, ?_⟩
  · intro R _ _ t
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · refine (mem_UJ_iff_mul_adj (sigR σ R) (hJ' R) _).2 ?_
      rw [MonoidHom.coe_toHomUnits, hadjHom, ← map_mul, mul_inv_cancel, map_one]
    · refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_)
      show idemHom hi ho R t * (γ : Matrix n n E).map (inclE (F := F) R) =
        (γ : Matrix n n E).map (inclE (F := F) R) * idemHom hi ho R t
      refine (idemLin_commute _ _ (fun k => ?_) _).eq.symm
      show (γ : Matrix n n E).map (inclE (F := F) R) * (idemFam σ J ε k).map (inclE (F := F) R) =
        (idemFam σ J ε k).map (inclE (F := F) R) * (γ : Matrix n n E).map (inclE (F := F) R)
      rw [← Matrix.map_mul, ← Matrix.map_mul, hγ]
  · intro R _ _ a b hab
    funext i
    apply Units.ext
    have h1 := congrArg (fun g : GL n (E ⊗[F] R) =>
      (g : Matrix n n (E ⊗[F] R)) * idemFamR σ J ε R (.inl i)) hab
    change idemLin _ (idemCoef R a) * _ = idemLin _ (idemCoef R b) * _ at h1
    rw [idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R),
      idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R)] at h1
    obtain ⟨k, l, hkl⟩ : ∃ k l, ε i k l ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h.2.1 i (Matrix.ext hc)
    have h2 := congrFun (congrFun h1 k) l
    simp [idemFamR, idemFam, idemCoef, inclE, Algebra.TensorProduct.tmul_mul_tmul] at h2
    exact tmul_right_injective hkl R h2
  · intro R S _ _ _ _ f t
    refine Units.ext ?_
    show idemLin (idemFamR σ J ε S) (idemCoef S _) =
      (idemLin (idemFamR σ J ε R) (idemCoef R t)).map
        (Algebra.TensorProduct.map (AlgHom.id F E) f).toRingHom
    rw [idemLin_map]
    congr 1
    · funext k
      simp only [idemFamR, Matrix.map_map]
      congr 1
      funext x
      simp [inclE]
    · funext k
      cases k <;> simp [idemCoef]
  · intro R _ _ t i
    exact idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R) _ (.inl i)

end GlobalTheory.RegSS.IdemTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamilyStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_subtorus_of_idempotent_family : GlobalTheory.RegSS.SubtorusOfIdempotents := by
  first | exact @GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | exact GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | (intros; apply GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents <;> assumption)
end
end

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

section Clauses

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}

theorem clauseAlg (h1 : CyclicSemilocal) (h2 : CyclicAlgebra) (h : IsRegular σ J γ) :
    ClauseAlg σ J γ := by
  have hJ := h.nondeg
  have : Module.Finite F E := quad_finite h.quad
  have : IsArtinianRing E := isArtinian_of_tower F inferInstance
  obtain ⟨v, hv⟩ := h1 E n (γ : Matrix n n E) h.sep
  obtain ⟨⟨e, he⟩, ⟨b⟩, hbij⟩ := h2 E n (γ : Matrix n n E) v hv
  have hinv : adj (σ : E →+* E) J (γ : Matrix n n E) = ((γ⁻¹ : GL n E) : Matrix n n E) :=
    adj_eq_inv _ hJ h.mem
  unfold ClauseAlg
  refine ⟨⟨e, he⟩, ?_, ⟨b⟩, ⟨v, hbij⟩, ?_, hinv, fun x => adj_algebraMap _ hJ x⟩
  ·
    have : Algebra.Etale E (AdjoinRoot (γ : Matrix n n E).charpoly) := by
      apply etale_adjoinRoot_of_isUnit_derivative (Matrix.charpoly_monic _)
      obtain ⟨a, c, hac⟩ := h.sep
      have h' := congrArg (AdjoinRoot.mk (γ : Matrix n n E).charpoly) hac
      simp only [map_add (f := _), map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h'
      exact isUnit_iff_exists_inv.2 ⟨_, (mul_comm _ _).trans h'⟩
    exact Algebra.Etale.of_equiv e
  ·
    intro l hl
    apply mem_genAlg_of_commute hbij
    have hl' : (γ : Matrix n n E) * l = l * (γ : Matrix n n E) := commute_of_mem_genAlg rfl hl
    have key : adj (σ : E →+* E) J l * adj (σ : E →+* E) J (γ : Matrix n n E) =
        adj (σ : E →+* E) J (γ : Matrix n n E) * adj (σ : E →+* E) J l := by
      rw [← adj_mul _ hJ, ← adj_mul _ hJ, hl']
    rw [hinv] at key
    set A := adj (σ : E →+* E) J l
    calc A * (γ : Matrix n n E)
        = (γ : Matrix n n E) * ((γ⁻¹ : GL n E) : Matrix n n E) * A * (γ : Matrix n n E) := by
          rw [Units.mul_inv, one_mul]
      _ = (γ : Matrix n n E) * (((γ⁻¹ : GL n E) : Matrix n n E) * A) * (γ : Matrix n n E) := by
          simp only [mul_assoc]
      _ = (γ : Matrix n n E) * (A * ((γ⁻¹ : GL n E) : Matrix n n E)) * (γ : Matrix n n E) := by
          rw [key]
      _ = (γ : Matrix n n E) * A * (((γ⁻¹ : GL n E) : Matrix n n E) * (γ : Matrix n n E)) := by
          simp only [mul_assoc]
      _ = (γ : Matrix n n E) * A := by rw [Units.inv_mul, mul_one]

theorem centRat_iff (h : IsRegular σ J γ) (hA : ClauseAlg σ J γ) (g : GL n E) :
    g ∈ centRat σ J γ ↔ (g : Matrix n n E) ∈ genAlg (γ : Matrix n n E) ∧
      (g : Matrix n n E) * adj (σ : E →+* E) J (g : Matrix n n E) = 1 := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  have hJ := h.nondeg
  rw [centRat, Subgroup.mem_inf, mem_UJ_iff_mul_adj _ hJ, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨mem_genAlg_of_commute hv ?_, hu⟩
    have hc' := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul] at hc'
    exact hc'.symm
  · rintro ⟨hm, hu⟩
    refine ⟨hu, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul]
    exact commute_of_mem_genAlg rfl hm

theorem exists_prod_fields (P : Type) [CommRing P] [Algebra F P] (hP : Algebra.Etale F P) :
    ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)),
      Nonempty (P ≃ₐ[F] ∀ i, K i) := by
  have := hP
  obtain ⟨I, hI, A, hA, hA', e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (K := F) (A := P)).1 inferInstance
  have := hI
  let c := Finite.equivFin I
  exact ⟨Nat.card I, fun i => A (c.symm i), fun i => hA _, fun i => hA' _,
    ⟨e.trans (AlgEquiv.piCongrLeft F A c.symm).symm⟩⟩

theorem exists_idemFamily [CharZero F] (h1 : SplitIdempotents) (h : IsRegular σ J γ)
    (hP : ClausePlus σ J γ) (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)]
    (e : Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i)) {ι : Type}
    (q : ι → {i : Fin k // ¬ IsField (K i ⊗[F] E)}) (hq : Function.Injective q) :
    ∃ ε : ι → Matrix n n E, IsIdemFamily σ J γ ε := by
  obtain ⟨δ, hne, hid, hort, hconj⟩ := h1 F E σ h.quad (plusAlg σ J (γ : Matrix n n E)) k K e
  have hinj := hP.2.2.1

  refine ⟨fun i => ((plusTensor σ J (γ : Matrix n n E) (δ (q i)) : genAlg (γ : Matrix n n E)) :
    Matrix n n E), ?_⟩
  unfold IsIdemFamily
  refine ⟨fun i => (plusTensor σ J (γ : Matrix n n E) (δ (q i))).2, ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply hne (q i)
    apply hinj
    rw [map_zero]
    exact Subtype.ext hi
  · intro i
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (δ (q i)) = plusTensor σ J (γ : Matrix n n E) (δ (q i)) by
        rw [← map_mul, hid])
  · intro i j hij
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (δ (q j)) = 0 by
        rw [← map_mul, hort _ _ (hq.ne hij), map_zero])
  · intro i j
    rw [← plusTensor_tConj h]
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (tConj _ σ (δ (q j))) = 0 by
        rw [← map_mul, hconj, map_zero])

theorem clauseRank [CharZero F] (h1 : SplitIdempotents) (h2 : SubtorusOfIdempotents)
    (h3 : SplitRankUpper) (h4 : TensorFieldIff) (h : IsRegular σ J γ) (hA : ClauseAlg σ J γ)
    (hP : ClausePlus σ J γ) (hC : PointsClause σ J γ) : ClauseRank σ J γ := by
  unfold ClauseRank
  refine ⟨exists_prod_fields _ hP.1, ?_⟩
  intro k K _ _ e
  unfold HasSplitRank
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  ·
    let c := Finite.equivFin {i : Fin k // ¬ IsField (K i ⊗[F] E)}
    obtain ⟨ε, hε⟩ := exists_idemFamily h1 h hP k K e c.symm c.symm.injective
    obtain ⟨A, -⟩ := h2 F E n σ J γ h hA _ ε hε
    exact ⟨A⟩
  · rintro s ⟨A⟩
    exact h3 F E n σ J γ h hP hC k K e s ⟨A⟩
  · intro hn
    obtain ⟨b⟩ := hP.2.1
    obtain ⟨f⟩ := e
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨i⟩ := hn
    apply b.ne_zero i
    apply f.injective
    funext j
    exact j.elim0
  · have := quad_nontrivial h.quad
    exact ((AlgEquiv.ofBijective _ hP.2.2).toMulEquiv.isField_congr.symm).trans (h4 F E _ k K e)

theorem centPts_comm (hC : PointsClause σ J γ) (R : Type) [CommRing R] [Algebra F R] :
    ∀ a ∈ centPts σ J γ R, ∀ b ∈ centPts σ J γ R, a * b = b * a := by
  intro a ha b hb
  obtain ⟨-, -, hiff⟩ := hC R
  obtain ⟨u, -, hu⟩ := (hiff a).1 ha
  obtain ⟨w, -, hw⟩ := (hiff b).1 hb
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← hu, ← hw, ← map_mul, ← map_mul,
    mul_comm (u : LPts σ J (γ : Matrix n n E) R)]

theorem tConj_tConj (hσ : ∀ x, σ (σ x) = x) (P : Type) [CommRing P] [Algebra F P]
    (x : P ⊗[F] E) : tConj P σ (tConj P σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p e => simp [tConj, Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Clauses

theorem regularSemisimple_of (a1 : CyclicSemilocal) (a2 : CyclicAlgebra) (a3 : PlusTensorBijective)
    (a4 : PlusEtale) (a5 : PointsCentraliser) (a6 : SplitClosed) (a7 : SplitIdempotents)
    (a8 : SubtorusOfIdempotents) (a9 : SplitRankUpper) (a10 : TensorFieldIff)
    (a11 : SubtorusNotCentral) (a12 : TraceClause) (a13 : FieldUnitBounded)
    (a14 : NormOfUnitBounded) (a15 : ProductUnitBounded) (a16 : MatOfNormBounded)
    (a17 : CompactOfMatBounded) (a18 : NotCompactOfIdempotent) : RegularSemisimple := by
  unfold RegularSemisimple RegularStructure RegularAdelic
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ n _ _ σ J γ h
    have hA := clauseAlg a1 a2 h
    have hP := a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)
    have hC := a5 F E n σ J γ h hA hP
    refine ⟨hA, hP, ?_, clauseRank a7 a8 a9 a10 h hA hP hC, ?_, a12 F E n σ J γ h hA⟩
    · unfold ClauseCent
      refine ⟨fun R _ _ => hC R, fun g => centRat_iff h hA g, ?_⟩
      intro Ω _ _ _
      exact a6 F E σ h.quad _ n hP.1 hP.2.1 Ω
    · unfold ClauseProper
      exact ⟨fun R _ _ => centPts_comm hC R, fun hE s hs A => a11 F E n σ J γ h hE s hs A⟩
  · intro F E _ _ _ _ n _ _ σ J γ h k K _ _ e
    have hA := clauseAlg a1 a2 h
    have hP := a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)
    have hC := a5 F E n σ J γ h hA hP
    constructor
    ·
      intro hc
      by_contra hne
      obtain ⟨i, hi⟩ := not_forall.1 hne
      obtain ⟨ε, hε⟩ := exists_idemFamily a7 h hP k K e (ι := Fin 1) (fun _ => ⟨i, hi⟩)
        (fun a b _ => Subsingleton.elim a b)
      obtain ⟨A, hAε⟩ := a8 F E n σ J γ h hA 1 ε hε
      obtain ⟨hmem, hne0, hidem, -, -⟩ := hε
      refine a18 F E n σ J γ h (ε 0) (hmem 0) (hne0 0) (hidem 0) ?_ hc
      intro t
      exact ⟨A.hom (AdeleRing (𝓞 F) F) (fun _ => t), A.mem (AdeleRing (𝓞 F) F) (fun _ => t),
        hAε (AdeleRing (𝓞 F) F) (fun _ => t) 0⟩
    ·
      intro hf
      have : Module.Finite F E := quad_finite h.quad
      obtain ⟨b⟩ := hP.2.1
      have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis b
      obtain ⟨f⟩ := e
      have : ∀ i, Module.Finite F (K i) := fun i =>
        Module.Finite.of_surjective ((Pi.evalAlgHom F K i).comp f.toAlgHom).toLinearMap
          (fun x => ⟨f.symm (Pi.single i x), by simp⟩)
      have hU : ∀ i, UnitBounded F (K i ⊗[F] E) (tConj (K i) σ) := fun i =>
        a13 F (K i ⊗[F] E) (tConj (K i) σ) (hf i) (tConj_tConj h.quad.invol (K i))
      have hUP := a15 F E σ (plusAlg σ J (γ : Matrix n n E)) k K ⟨f⟩ hU
      have hN := a14 F _ _ hUP
      exact a17 F E n σ J γ h (a16 F E n σ J γ h hA hP hC hN)

theorem regularSemisimple : RegularSemisimple :=
  regularSemisimple_of (GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field GlobalTheory.T.cyclicVector_of_separable_charpoly_field) GlobalTheory.T.cyclicVector_generatedAlgebra_structure GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective GlobalTheory.T.regularSemisimple_selfAdjointPart_etale
    (GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint GlobalTheory.T.regularSemisimple_tensor_commutant GlobalTheory.T.regularSemisimple_tensor_involution_adjoint) GlobalTheory.T.etale_tensor_quadratic_split_algClosed GlobalTheory.T.split_factor_idempotents_exist GlobalTheory.T.split_subtorus_of_idempotent_family
    (GlobalTheory.T.centralizer_splitRank_upper_bound GlobalTheory.T.split_subtorus_laurentPolynomial_points GlobalTheory.T.laurentPolynomial_character_isMonomial GlobalTheory.T.conjugate_factor_points_separate) GlobalTheory.T.product_fields_baseChange_isField_iff
    (GlobalTheory.T.nontrivial_split_subtorus_not_central GlobalTheory.T.unitaryGroup_commutant_scalars GlobalTheory.T.split_subtorus_laurentPolynomial_points GlobalTheory.T.laurentPolynomial_character_isMonomial) (GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect GlobalTheory.T.reduced_free_algebra_traceForm_perfect)
    (GlobalTheory.T.fieldAdelicUnitTranslateBounded_of_smallMultiples GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup GlobalTheory.T.finiteAlgebraAdelicLattice_proof) (GlobalTheory.T.normOfUnitBounded_of_tensorLattice' GlobalTheory.T.finiteAlgebraAdelicLattice_proof)
    (GlobalTheory.T.adelic_unit_translate_bounded_of_factors GlobalTheory.T.finiteAlgebraAdelicLattice_proof) GlobalTheory.T.centraliser_points_bounded_of_normOne_bounded (GlobalTheory.T.adelic_quotient_compact_of_bounded_matrices GlobalTheory.T.finiteAlgebraAdelicLattice_proof)
    (GlobalTheory.T.adelic_quotient_not_compact_of_split_idempotent GlobalTheory.T.det_restrict_range_idempotent_matrix)

end GlobalTheory.RegSS
