module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTowerTrBasisAppendCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoord
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoord
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TowerTrdeg

theorem image_isAlgebraic : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  (letI := cL.toAlgebra; ∀ a : MvPolynomial (Fin r) R,
    IsAlgebraic (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))))
      ((MvPolynomial.eval₂Hom ι τ a : T) : L)) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  letI := cL.toAlgebra
  intro a
  have hy : IsTranscendenceBasis ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    trBasis_append cK cL n r R T ι ψ τ x h hx
  exact hy.isAlgebraic.isAlgebraic _

end GlobalTheory.FieldPair.TowerTrdeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoordStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_mvPolynomialEval_adjoin_etaleTowerCoords : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  (letI := cL.toAlgebra; ∀ a : MvPolynomial (Fin r) R,
    IsAlgebraic (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))))
      ((MvPolynomial.eval₂Hom ι τ a : T) : L)) := by
  first | exact @GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic | exact GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic | (intros; apply GlobalTheory.FieldPair.TowerTrdeg.image_isAlgebraic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinates
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem etTower_coords_algebraicIndependent {K L : Type} [Field K] [Field L] (cK : ℂ →+* K)
    (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) :
    IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
    Function.Injective (MvPolynomial.eval₂Hom ι τ) →
    (letI := cL.toAlgebra; AlgebraicIndependent ℂ
      (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro h hx hinj
  letI := cL.toAlgebra
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let φ : MvPolynomial (Fin n) ℂ →+* R := MvPolynomial.eval₂Hom c0 x
  have hφinj : Function.Injective φ := by
    have hxK : Function.Injective (MvPolynomial.eval₂Hom cK (fun i => (x i : K))) := by
      letI := cK.toAlgebra
      have h1 := hx.1
      rw [algebraicIndependent_iff_injective_aeval] at h1
      exact h1
    have hcomp : R.subtype.comp φ = MvPolynomial.eval₂Hom cK (fun i => (x i : K)) := by
      ext <;> simp [φ, c0]
    intro a b e
    apply hxK
    rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, e]
  have key : (T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)))
        = (MvPolynomial.aeval (Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have := h.const a
      simp [φ, c0, MvPolynomial.sumAlgEquiv_C_inl]
      exact this
    · rintro (i | j) <;> simp [φ, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have hy : Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) ∘ finSumFinEquiv
      = Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)) := by
    ext (i | j) <;> simp
  rw [← algebraicIndependent_equiv finSumFinEquiv, hy, algebraicIndependent_iff_injective_aeval,
    injective_iff_map_eq_zero]
  intro P hP
  have hP' : T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)) P = 0 := by
    rw [key]; exact hP
  have h1 : MvPolynomial.eval₂Hom ι τ (MvPolynomial.map φ (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n) P)) = 0 :=
    Subtype.ext hP'
  have h2 := (injective_iff_map_eq_zero _).1 hinj _ h1
  have h3 := (injective_iff_map_eq_zero _).1 (MvPolynomial.map_injective φ hφinj) _ h2
  exact (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).map_eq_zero_iff.1 h3

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinatesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicIndependent_etaleTower_coordinates : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  (letI := cL.toAlgebra; AlgebraicIndependent ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | exact GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | (intros; apply GlobalTheory.FieldPair.etTower_coords_algebraicIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOverMvPolynomialRangeEtaleTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOverMvPolynomialRangeEtaleTower
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem isAlgebraic_range_eval₂Hom_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T),
  IsEtTower cK R cL T ι ψ τ → Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  ∀ z : L, IsAlgebraic (T.subtype.comp (MvPolynomial.eval₂Hom ι τ)).range z := by
  intro K L _ _ cK cL r R T ι ψ τ h hinj z
  classical
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  let φL : A →+* L := T.subtype.comp φ
  have hφL : Function.Injective φL := Subtype.val_injective.comp hinj

  letI : Algebra A T := φ.toAlgebra
  letI : Algebra A L := φL.toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallyEtale A T := h.etale

  haveI : IsFractionRing T L := IsFractionRing.of_field T L fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.top.frac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI : Algebra.FormallyUnramified T L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.comp A T L

  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  haveI : IsScalarTower ℂ T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq fun a => by
    change cL a = T.subtype (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C (c0 a)))
    rw [MvPolynomial.eval₂Hom_C]
    exact (h.const a).symm
  haveI : Algebra.EssFiniteType ℂ T := RingHom.essFiniteType_algebraMap.1 h.top.essFiniteType
  haveI : Algebra.EssFiniteType T L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ T L
  haveI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_comp ℂ A L

  let F := FractionRing A
  letI : Algebra F L := (IsFractionRing.lift hφL : F →+* L).toAlgebra
  haveI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap hφL a).symm
  haveI : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_restrictScalars A F L
  haveI : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L
  haveI : Algebra.IsSeparable F L := Algebra.FormallyUnramified.isSeparable F L
  have hA : IsAlgebraic A z :=
    (IsFractionRing.isAlgebraic_iff A F L).2 (Algebra.IsAlgebraic.isAlgebraic z)

  obtain ⟨p, hp, hpz⟩ := hA
  refine ⟨p.map φL.rangeRestrict, (Polynomial.map_ne_zero_iff
    (RingHom.injective_codRestrict.2 hφL)).2 hp, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact hpz

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOverMvPolynomialRangeEtaleTowerStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_over_mvPolynomial_range_etaleTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T),
  IsEtTower cK R cL T ι ψ τ → Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  ∀ z : L, IsAlgebraic (T.subtype.comp (MvPolynomial.eval₂Hom ι τ)).range z := by
  first | exact @GlobalTheory.FieldPair.isAlgebraic_range_eval₂Hom_of_isEtTower | exact GlobalTheory.FieldPair.isAlgebraic_range_eval₂Hom_of_isEtTower | (intros; apply GlobalTheory.FieldPair.isAlgebraic_range_eval₂Hom_of_isEtTower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSubringIsAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSubringIsAlgebraic
namespace GlobalTheory


open Algebra in
theorem isAlgebraic_of_subring_isAlgebraic {L : Type} [Field L] [Algebra ℂ L]
    (S : Subalgebra ℂ L) (B : Subring L) (z : L)
    (hB : ∀ b ∈ B, IsAlgebraic S b) (hz : IsAlgebraic B z) : IsAlgebraic S z := by
  set T := adjoin ℂ ((S : Set L) ∪ (B : Set L)) with hT
  have hBT : ∀ b ∈ B, b ∈ T := fun b hb => subset_adjoin (Or.inr hb)
  let f : B →+* T :=
    { toFun := fun b => ⟨b.1, hBT b.1 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra B T := f.toAlgebra
  have : IsScalarTower B T L := .of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap B T) := by
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have hzT : IsAlgebraic T z := hz.extendScalars hinj
  have hSle : S ≤ adjoin ℂ (S : Set L) := subset_adjoin
  have key : IsAlgebraic (adjoin ℂ (S : Set L)) z := by
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := ℂ) (s := (S : Set L) ∪ (B : Set L)) ?_ hzT
    intro x hx
    rcases hx.1 with h | h
    · exact absurd h hx.2
    · exact (hB x h).tower_top_of_subalgebra_le hSle
  rwa [Algebra.adjoin_eq] at key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSubringIsAlgebraicStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring : ∀ {L : Type} [Field L] [Algebra ℂ L] (S : Subalgebra ℂ L) (B : Subring L) (z : L),
  (∀ b ∈ B, IsAlgebraic S b) → IsAlgebraic B z → IsAlgebraic S z := by
  first | exact @GlobalTheory.isAlgebraic_of_subring_isAlgebraic | exact GlobalTheory.isAlgebraic_of_subring_isAlgebraic | (intros; apply GlobalTheory.isAlgebraic_of_subring_isAlgebraic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialIdealEqBotOfPderivStableNoConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialIdealEqBotOfPderivStableNoConstants
namespace GlobalTheory

open MvPolynomial Finsupp

theorem mvPolynomial_ideal_eq_bot_of_pderiv_stable :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  intro R _ _ _ r I hI hC
  have key : ∀ n : ℕ, ∀ P ∈ I, P.totalDegree = n → P = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P hP h
    by_contra hne
    by_cases hn : n = 0
    · subst hn
      rw [totalDegree_eq_zero_iff_eq_C] at h
      apply hne
      rw [h] at hP ⊢
      rw [hC _ hP, C_0]
    · obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hne)
        (fun s => s.sum fun _ e => e)
      have hdeg : (m.sum fun _ e => e) = n := by rw [← h, totalDegree, hmd]
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hm0 : m = 0 := Finsupp.ext hcon
        subst hm0
        simp at hdeg
        omega
      have hQ : pderiv i P ∈ I := hI P hP i
      have hQne : pderiv i P ≠ 0 := by
        intro h0
        have hc := coeff_pderiv (i := i) P (m - single i 1)
        rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
          sub_add_single_one_cancel hi] at hc
        have hcm : AddMonoidAlgebra.coeff P m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
        have hk : (((m - single i 1 : Fin r →₀ ℕ) i : ℕ) : R) + 1 ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        exact (mul_ne_zero hcm hk) hc.symm
      have hlt : (pderiv i P).totalDegree < n := by
        have hle : (pderiv i P).totalDegree ≤ n - 1 := by
          apply Finset.sup_le
          intro s hs
          have hs' := MvPolynomial.mem_support_iff.mp hs
          rw [coeff_pderiv] at hs'
          have hsupp : s + single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs')
          have hd := le_totalDegree hsupp
          rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl, h] at hd
          omega
        omega
      exact hQne (ih _ hlt _ hQ rfl)
  rw [eq_bot_iff]
  intro P hP
  rw [Ideal.mem_bot]
  exact key _ P hP rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialIdealEqBotOfPderivStableNoConstantsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  first | exact @GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | exact GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | (intros; apply GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenTopFormEtaleTowerTranscendenceBasis
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem IsEtTower.eval₂Hom_pderiv_eq_zero {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) (P : MvPolynomial (Fin r) R) (i : Fin r)
    (hP : MvPolynomial.eval₂Hom ι τ P = 0) :
    MvPolynomial.eval₂Hom ι τ (MvPolynomial.pderiv i P) = 0 := by
  letI : Algebra R T := ι.toAlgebra
  letI : Algebra (MvPolynomial (Fin r) R) T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin r) R) T := IsScalarTower.of_algebraMap_eq' (by
    ext a; simp [RingHom.algebraMap_toAlgebra])
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) T := h.etale
  let d : Derivation R (MvPolynomial (Fin r) R) T :=
    (Algebra.linearMap (MvPolynomial (Fin r) R) T).compDer (MvPolynomial.pderiv i)
  let f : Ω[MvPolynomial (Fin r) R⁄R] →ₗ[MvPolynomial (Fin r) R] T := d.liftKaehlerDifferential
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale R (MvPolynomial (Fin r) R) T
  let g : Ω[T⁄R] →ₗ[T] T := hb.lift f
  have key : g (KaehlerDifferential.D R T (algebraMap (MvPolynomial (Fin r) R) T P)) =
      algebraMap (MvPolynomial (Fin r) R) T (MvPolynomial.pderiv i P) := by
    rw [← KaehlerDifferential.map_D R R (MvPolynomial (Fin r) R) T]
    erw [hb.lift_eq]
    simp [f, d]
  have h0 : algebraMap (MvPolynomial (Fin r) R) T P = 0 := hP
  rw [h0, map_zero, map_zero] at key
  exact key.symm

theorem charZero_subring_of_complex {K : Type} [Field K] (cK : ℂ →+* K) (R : Subring K) :
    CharZero R := by
  haveI : CharZero K := charZero_of_injective_ringHom cK.injective
  exact ⟨fun a b h => by
    have := congrArg (fun t : R => (t : K)) h
    simpa using this⟩

theorem IsEtTower.eval₂Hom_injective {K L : Type} [Field K] [Field L] {cK : ℂ →+* K}
    {cL : ℂ →+* L} {r : ℕ} {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R}
    {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Injective (MvPolynomial.eval₂Hom ι τ) := by
  haveI := charZero_subring_of_complex cK R
  have hI := GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants r (RingHom.ker (MvPolynomial.eval₂Hom ι τ))
    (fun P hP i => h.eval₂Hom_pderiv_eq_zero P i hP)
    (fun a ha => by
      rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_C] at ha
      simpa [h.retr] using congrArg ψ ha)
  exact (RingHom.injective_iff_ker_eq_bot _).2 hI

theorem isFreeGen_dForm_tower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L)
    (n r : ℕ) (R : Subring K) (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T)
    (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  have hinj := h.eval₂Hom_injective
  letI := cL.toAlgebra
  have hind := GlobalTheory.T.algebraicIndependent_etaleTower_coordinates cK cL n r R T ι ψ τ x h hx hinj
  have halg : Algebra.IsAlgebraic
      (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))) L := by
    refine ⟨fun z => GlobalTheory.T.isAlgebraic_of_isAlgebraic_over_algebraic_subring _ _ z ?_ (GlobalTheory.T.isAlgebraic_over_mvPolynomial_range_etaleTower cK cL r R T ι ψ τ h hinj z)⟩
    rintro b ⟨a, rfl⟩
    exact GlobalTheory.T.isAlgebraic_mvPolynomialEval_adjoin_etaleTowerCoords cK cL n r R T ι ψ τ x h hx a
  have htr : TrBasis cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨hind, halg⟩
  exact isFreeGen_dForm_of_trBasis cL htr

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenTopFormEtaleTowerTranscendenceBasisStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGen_topForm_etaleTower_transcendenceBasis : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.isFreeGen_dForm_tower | exact GlobalTheory.FieldPair.isFreeGen_dForm_tower | (intros; apply GlobalTheory.FieldPair.isFreeGen_dForm_tower <;> assumption)
end
