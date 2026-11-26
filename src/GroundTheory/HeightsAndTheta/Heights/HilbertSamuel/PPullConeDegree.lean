module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegree

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]


omit [CharZero Ω] in
theorem isWeightedHomogeneous_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k


omit [CharZero Ω] in
theorem isMultiHomog_of_isWeightedHomogeneous {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]


omit [DecidableEq K] [CharZero Ω] in
theorem prod_X_pow_eq_monomial (a : K → ℕ) :
    (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp

theorem coeff_mConeMapQ (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) ℚ) (n : K → ℕ) :
    AddMonoidAlgebra.coeff (mConeMapQ y f) (Finsupp.equivFunOnFinite.symm n) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMapQ_eq y hm, prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]


omit [DecidableEq K] [CharZero Ω] in
theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℚ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℚ) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegree.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L N hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩

  have hgI : g ∈ coneNullIdeal y L := by
    rw [g.as_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (AddMonoidAlgebra.coeff g μ)
    exact Ideal.mem_of_dvd _ hc (hN c)
  have hI : coneNullIdeal y L = RingHom.ker (mConeMapQ y) ⊔
      Ideal.span (Set.range fun j => map (Int.castRingHom ℚ) (L j)) := by
    rw [coneNullIdeal, Ideal.span_union, ← map_mCoordIdeal]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMapQ y (map (Int.castRingHom ℚ) (L j)) =
      monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    have h : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (map (Int.castRingHom ℚ) (L j)) e := fun m hm => hL j m (support_map_subset _ _ hm)
    rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog h), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
      ← algebraMap_int_eq, aeval_map_algebraMap]
  have hψg : mConeMapQ y g =
      ∑ j, mConeMapQ y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← huv, map_add (f := _), RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog hg), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMapQ]

end PullConeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem PullRatiosAlgebraic.proof (h₁ : PullConeNull.Statement) (h₂ : PullConeDegree.Statement)
    (h₃ : PullGradedAlgebraic.Statement) : PullRatiosAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L hy he hL hz
  obtain ⟨N, hN⟩ := h₁ K ι Ω y D L hz
  exact h₃ K ι Ω y D e L (fun k => e k + N * Fintype.card (ι k)) hy he hL
    (fun d g hg hd => h₂ K ι Ω y D e L N hy hL hN d g hg hd)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def coneNullIdealZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : Ideal (MRing ι) :=
  Ideal.span ((mCoordIdeal y : Set (MRing ι)) ∪ Set.range L)

def PullConeNullModP.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (p : ℕ) (hp : p.Prime), ¬ HasCommonZeroModP y L p hp →
      ∃ N M : ℕ, ¬ p ∣ M ∧ ∀ c : ∀ k, ι k,
        (M : MRing ι) * (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∈ coneNullIdealZ y L

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtTransc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGenPtTransc.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))),
      Transcendental (Algebra.adjoin ℤ (Set.range fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩))
        (G.x' ⟨Sum.inr (), (0 : Fin (D + 1))⟩)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtRel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGenPtRel.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))),
      (∀ n : ℕ, (n : G.Φ') = 0 → n = 0) ∧
      coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) = coordIdeal ℤ x ∧
      (∀ k : Fin (D + 1), G.x' ⟨Sum.inr (), k⟩ * G.x' ⟨Sum.inl (e 0).1, (e 0).2⟩ =
        G.x' ⟨Sum.inr (), (0 : Fin (D + 1))⟩ * G.x' ⟨Sum.inl (e k).1, (e k).2⟩) ∧
      (algebraMap G.Φ G.Φ').fieldRange = Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormGoodPrimeIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormGoodPrimeIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (p : ℕ) (hp : p.Prime), ¬ HasCommonZeroModP y L p hp →
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∀ m : Fin (D + 1) →₀ ℕ, 0 ≤ padicValRat p ((c (Module.finrank (pullField y L) Ω)).coeff m)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockPieceCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem TwoBlockPieceCycle.proof (hA : TwoBlockPieceIndex.Statement) (hF : TwoBlockModuleFinite.Statement)
    (hH : ModulePieceHilbert.Statement) (hC : TwoBlockModuleCycle.Statement) : TwoBlockPieceCycle.Statement := by
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl
  obtain ⟨hm₁, hm₂, hle, ⟨N, hN, hNJ⟩, hdim⟩ := hF D Ω κ x B c l hX hx hB hsp hl
  obtain ⟨a₀, C, h⟩ := hH (Fin 2) (FinTwoTypeFamily κ) _ _ N D hm₁ hm₂ hle hN hNJ hdim (fun _ => 1)
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  have h1 := h ![a, b] (fun k => by fin_cases k <;> simpa)
  have e1 : (![a, b] + fun _ => 1 : Fin 2 → ℕ) = ![a + 1, b + 1] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun (_ : Fin D) (k : Fin 2) => ((![a, b] k : ℕ) : ℤ)) = fun _ => ![(a : ℤ), (b : ℤ)] := by
    funext _ k
    fin_cases k <;> rfl
  have e3 : ((∑ k, ![a, b] k : ℕ) : ℝ) = (a + b : ℝ) := by
    simp [Fin.sum_univ_two]
  rw [e1, e2, hC D Ω κ x B c l hX hx hB hsp hl, e3] at h1
  rw [hA D Ω κ x B c l hX hx hB hsp hl a b]
  exact h1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLatticeNested
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

set_option linter.unusedSectionVars false

namespace ChangeOfLatticeNested

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem exists_mul_mem_sec_one (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ s ∈ sec ℤ (matAct B x) 1, (M : Ω) * s ∈ sec ℤ x 1 := by
  obtain ⟨d, hd0, hdB⟩ := ChangeOfLattice.exists_clear_den B
  refine ⟨d, Nat.pos_of_ne_zero hd0, fun s hs => ?_⟩
  rw [sec_one'] at hs ⊢
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, rfl⟩ := hs
    have e : (d : Ω) * matAct B x i = matAct ((d : ℚ) • B) x i := by
      simp only [matAct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact ChangeOfLattice.matAct_mem_span (fun i j => by simpa [Matrix.smul_apply] using hdB i j) x i
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb
  | smul k a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ k ha

theorem latLogIndex_eq_sum (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ)
    (hle : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x))) (n : ℕ) :
    latLogIndex x (matAct B x) n = ∑ j ∈ Finset.range n, twoBlockStep x (matAct B x) (n - j - 1) j := by
  have h1 : sec ℤ x 1 ≤ sec ℤ (matAct B x) 1 := by
    rw [sec_one', sec_one']
    exact hle
  have one : (sec ℤ (matAct B x) n).toAddSubgroup.relIndex (sec ℤ x n).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.2 fun _ h => ChangeOfLattice.sec_mono hle n h
  unfold latLogIndex
  rw [one, Nat.cast_one, Real.log_one, sub_zero, log_relIndex_eq_sum x _ h1 (exists_mul_mem_sec_one x B) n]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold twoBlockStep
  rw [show n - j - 1 + 1 = n - j by omega]

end ChangeOfLatticeNested

theorem ChangeOfLatticeNested.proof (hS : TwoBlockChainSum.Statement) (hT : TwoBlockTop.Statement) :
    ChangeOfLatticeNested.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨e0, e1⟩ := hT D Ω κ I x B m m' hI hX hx hB hm hm'
  have h := hS D Ω κ I x B m m' hI hX hx hB hm hm' hsp
  rw [e0, e1] at h
  refine h.congr_left fun n => ?_
  rw [ChangeOfLatticeNested.latLogIndex_eq_sum x B hsp n]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace FibreNormDehomCharpoly

theorem finiteDimensional_pullField (hR : PullRatiosAlgebraic.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ}
    {L : Fin (D + 1) → MRing ι} (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hB : Birational y) (he : ∀ k, 1 ≤ e k)
    (hL : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    FiniteDimensional (pullField y L) Ω := by
  classical
  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  set P := pullField y L
  set S : Set Ω := {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = y p / y q} with hS
  have hSf : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) => y pq.1 / y pq.2).subset
    (by rintro _ ⟨p, q, -, rfl⟩; exact ⟨(p, q), rfl⟩)
  have : Finite S := hSf.to_subtype
  have hSi : ∀ x ∈ S, IsIntegral P x := by
    rintro _ ⟨p, q, hpq, rfl⟩
    exact (hR K ι Ω y D e L hrel' he hL hz p q hpq).isIntegral
  have hfd : FiniteDimensional P (IntermediateField.adjoin P S) := IntermediateField.finiteDimensional_adjoin hSi
  have htop : IntermediateField.adjoin P S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ blockFnField y := (PullFormsGeneric.blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top
    have hle : blockFnField y ≤ (IntermediateField.adjoin P S).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      exact fun t ht => IntermediateField.subset_adjoin P S ht
    exact hle hx
  have hfd' : FiniteDimensional P (⊤ : IntermediateField P Ω) := htop ▸ hfd
  exact (IntermediateField.topEquiv (F := P) (E := Ω)).toLinearEquiv.finiteDimensional

end FibreNormDehomCharpoly


open FibreNormDehomCharpoly in
theorem FibreNormDehomCharpoly.proof (hG : PullFormsGeneric.Statement) (hR : PullRatiosAlgebraic.Statement)
    (hI : PullSectionIntegral.Statement) (hC : DehomCharpolyForms.Statement) : FibreNormDehomCharpoly.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hA hB he hL hz
  classical
  have hfin : FiniteDimensional (pullField y L) Ω := finiteDimensional_pullField hR hA hB he hL hz
  refine ⟨hfin, fun τ s hs j hj => ?_⟩
  set l : Fin (D + 1) → Ω := fun i => aeval y (L i) with hl
  have hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0 :=
    hG K ι Ω y D e L hA hB he hL hz
  have hne : ∀ k, l k ≠ 0 := fun k h0 =>
    X_ne_zero (R := ℚ) k (hgen 1 (X k) (isHomogeneous_X ℚ k) (by rw [aeval_X]; exact h0))
  have hint : ∀ k, s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) ∈
      integralClosure (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) Ω := by
    intro k
    have h : s / l j ^ (q * τ) * (l j / l k) ^ (q * τ) = s / l k ^ (q * τ) := by
      rw [div_pow, div_mul_div_comm, mul_comm (l j ^ (q * τ)), mul_div_mul_right _ _ (pow_ne_zero _ (hne j))]
    rw [h]
    exact hI K ι Ω y D e L q hA hB he hL hz τ s hs k (hne k)
  obtain ⟨c, hc0, hch, hcp, hcn⟩ := hC Ω D l (pullField y L) rfl hgen j (q * τ) (s / l j ^ (q * τ)) hint
  exact ⟨c, ⟨hj, hfin, hc0, hch, hcp⟩, fun hs0 => hcn (div_ne_zero hs0 (pow_ne_zero _ hj))⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtChartUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtChartUnit.proof : ClosedPtChartUnit.Statement := by
  classical
  intro S _ K _ ι _ P hP I hI hX f a hf hfP
  have : P.IsPrime := hP.1.1

  have hTP : KH.cellMon S I ≤ P.primeCompl :=
    Submonoid.closure_le.mpr (by rintro _ ⟨k, i, hi, rfl⟩; exact hX k i hi)
  have hPh : NumbersDVR.IsMultiHomogIdeal P := (NumbersDVR.Objects.isMultiHomogIdeal_iff P).mpr hP.1.2.1

  obtain ⟨t, htT, htJ⟩ : ∃ t ∈ KH.cellMon S I, t ∈ P ⊔ Ideal.span {f} := by
    by_contra hno
    push Not at hno
    obtain ⟨p, hp, hJp, hdisj⟩ := Ideal.exists_le_prime_disjoint (P ⊔ Ideal.span {f}) (KH.cellMon S I)
      (Set.disjoint_left.mpr fun x hxJ hxT => hno x hxT hxJ)
    obtain ⟨W, hW, hWh, hWp, hWJ, hWf⟩ := NumbersDVR.exists_multiHomog_core hp
    have hPW : P ≤ W := hWJ P hPh (le_sup_left.trans hJp)
    have hfW : f ∈ W :=
      hWf f a ((NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf)
        (hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
    have hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
      intro k
      obtain ⟨i, hi⟩ := hI k
      refine ⟨i, fun hXW => Set.disjoint_left.mp hdisj (hWp hXW) ?_⟩
      exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
    have hWP : W = P := hP.2 W ⟨hW, (NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp hWh, hrel⟩ hPW
    exact hfP (hWP ▸ hfW)

  obtain ⟨e, hte'⟩ : ∃ e, NumbersDVR.IsMultiHomog t e := by
    clear htJ
    induction htT using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, i, -, rfl⟩ := hx
      exact ⟨_, isWeightedHomogeneous_X S (NumbersDVR.blockWeight ι) ⟨k, i⟩⟩
    | one => exact ⟨0, isWeightedHomogeneous_one S (NumbersDVR.blockWeight ι)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, IsWeightedHomogeneous.mul hc hd⟩
  have hf' : NumbersDVR.IsMultiHomog f a := (NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf
  obtain ⟨p, hpP, r, hr, hpr⟩ := Submodule.mem_sup.mp htJ
  obtain ⟨g₀, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hcomp : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p +
        weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e (g₀ * f) := by
    rw [← hpr, map_add (f := _)]
  have htself : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t = t := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hte'), if_pos rfl]
  rw [htself] at hcomp
  have hpe : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p ∈ P := hPh p hpP e
  by_cases hae : a ≤ e
  · refine ⟨t, htT, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (e - a) g₀, e - a, ?_, ?_, ?_⟩
    · rw [add_tsub_cancel_of_le hae]
      exact (NumbersDVR.Objects.isMultiHomog_iff t e).mp hte'
    · exact (NumbersDVR.Objects.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [NumbersDVR.component_mul_form_of_le hf' hae] at hcomp
      rw [hcomp, add_sub_cancel_right]
      exact hpe
  · rw [NumbersDVR.component_mul_form_of_not_le hf' hae, add_zero] at hcomp
    exact absurd (hcomp ▸ hpe) (hTP htT)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBadPrimesFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem aeval_map_intRat_eq {σ : Type} (x : σ → ℂ) (f : MvPolynomial σ ℤ) :
    aeval x (map (algebraMap ℤ ℚ) f) = eval x (map (Int.castRingHom ℂ) f) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem FibreNormBadPrimesFinite.proof : FibreNormBadPrimesFinite.Statement := by
  intro K _ ι _ Ω _ _ y D e L _ _ _ _ hC
  set I : Ideal (MvPolynomial (Σ k, ι k) ℤ) := mCoordIdeal y ⊔ Ideal.span (Set.range L) with hIdef
  have key : ∀ c : ∀ k, ι k, ∃ N : ℤ, N ≠ 0 ∧
      ∃ r : ℕ, C N * (∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ r ∈ I := by
    intro c
    set f : MvPolynomial (Σ k, ι k) ℤ := ∏ k, X ⟨k, c k⟩
    set IQ := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) I
    have hv : algebraMap _ (MvPolynomial (Σ k, ι k) ℚ) f ∈ vanishingIdeal ℚ (zeroLocus ℂ IQ) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      have h0 : ∀ g ∈ I, eval x (map (Int.castRingHom ℂ) g) = 0 := fun g hg => by
        rw [← aeval_map_intRat_eq, ← algebraMap_def]
        exact hx _ (Ideal.mem_map_of_mem _ hg)
      rw [algebraMap_def, aeval_map_intRat_eq]
      by_contra hne
      simp only [f, map_prod, map_X, eval_X] at hne
      have hblk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hne) k (Finset.mem_univ _)
      obtain ⟨j, hj⟩ := hC x ⟨fun k => ⟨c k, hblk k⟩, fun g hg => h0 g (Ideal.mem_sup_left hg)⟩
      exact hj (h0 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))
    rw [vanishingIdeal_zeroLocus_eq_radical] at hv
    obtain ⟨r, hr⟩ := hv
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))]
      at hr
    obtain ⟨⟨⟨u, hu⟩, ⟨m, hm⟩⟩, h⟩ := hr
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.1 hm
    refine ⟨n, nonZeroDivisors.ne_zero hn, r, ?_⟩
    have hinj : Function.Injective (map (σ := Σ k, ι k) (algebraMap ℤ ℚ)) :=
      map_injective _ (algebraMap ℤ ℚ).injective_int
    have hu' : f ^ r * C n = u := hinj (by simpa only [algebraMap_def, map_mul] using h)
    rw [mul_comm, hu']
    exact hu
  choose N hN r hr using key
  refine Set.Finite.subset (Set.finite_iUnion fun c => (Set.finite_Iic (N c).natAbs)) ?_
  rintro p ⟨hp, hH⟩
  obtain ⟨z, hz, hP, hL⟩ := hH
  choose c hc using hz
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  have hker : I ≤ RingHom.ker ((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))) :=
    sup_le (fun g hg => hP g hg) (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hL j))
  have h1 := hker (hr c)
  simp only [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_pow, map_prod, map_X, eval_X, eq_intCast,
    map_intCast] at h1
  have hprod : (∏ k, z ⟨k, c k⟩) ^ r c ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hc k)
  have hNz : ((N c : ℤ) : AlgebraicClosure (ZMod p)) = 0 := (mul_eq_zero.1 h1).resolve_right hprod
  rw [CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at hNz
  simp only [Set.mem_iUnion, Set.mem_Iic]
  exact ⟨c, Nat.le_of_dvd (Int.natAbs_pos.2 (hN c)) (Int.natCast_dvd.1 hNz)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreSectionLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


set_option maxHeartbeats 1000000 in
theorem FibreSectionLift.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hsq : KH.CechDSqStatement) (hdg : KH.CechDDegStatement) (hR : ReductionComplex.Statement)
    (hZ : ZeroCocycleSection.Statement) (hC : SecCochReduce.Statement) : FibreSectionLift.Statement := by
  intro K _ _ ι _ _ Ω _ y D p a hV hp hH1
  have hH1' : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) := hH1
  show ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 0,
    ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z
  intro z hz'

  let instC : ∀ n : ℕ, Module ℤ (KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) := fun n =>
    (fun {A : Type} {_ : AddCommMonoid A} {i : Module ℤ A} (_ : Submodule ℤ A) => i)
      (KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n)
  let instZ : Module ℤ (KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := Submodule.module _
  let instCp : ∀ n : ℕ, Module (ZMod p) (KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n) :=
    fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module (ZMod p) A} (_ : Submodule (ZMod p) A) => i)
      (KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n)
  let instZp : Module (ZMod p) (KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) :=
    Submodule.module _
  let instH : Module ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) :=
    Submodule.Quotient.module _
  obtain ⟨hd, hrd, hon, hker₀, hnzd₀, hkill₀⟩ := hR K ι Ω y D p a hV hp

  have hker : ∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w' := by
    intro n w hw h0
    obtain ⟨w', h1, h2⟩ := hker₀ n w hw h0
    exact ⟨w', h1, by convert h2 using 2⟩
  have hnzd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      (p : ℤ) • w = 0 → w = 0 := fun n w h => hnzd₀ n w (by convert h using 2)
  have hkill : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0 := fun n w => by convert hkill₀ n w using 3
  have hgr : KH.IsMGraded ℤ ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) :=
    hG ℤ K ι _ (by rw [FibreReduction.idealOver_int]; exact hV.2.1.2.1)
  have hfin : Module.Finite ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := by
    exact (hS ℤ K ι _ _ inferInstance inferInstance hgr).1 a 1
  have dd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ (n + 1) (KH.cechD ℤ ι _ n w) = 0 := fun n w =>
    LinearMap.congr_fun (hsq ℤ K ι _ n) w
  have dsmul : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ n ((p : ℤ) • w) = (p : ℤ) • KH.cechD ℤ ι _ n w := fun n w =>
    map_zsmul (KH.cechD ℤ ι _ n).toAddMonoidHom (p : ℤ) w
  have memZ : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n → KH.cechD ℤ ι _ n w = 0 →
        w ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n := fun n w hC hD =>
    Submodule.mem_inf.mpr ⟨hC, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hD⟩

  let f : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 →ₗ[ℤ]
      KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 := LinearMap.lsmul ℤ _ (p : ℤ)
  have hq : ∀ x : KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1,
      f (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((p : ℤ) • x) := fun x => by
    rw [LinearMap.lsmul_apply, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_zsmul]
    exact int_smul_eq_zsmul instH (p : ℤ) _
  have hsurj : Function.Surjective f := by
    intro h
    induction h using Submodule.Quotient.induction_on with
    | H x =>
    have hx := Submodule.mem_inf.mp x.2
    have hxd : KH.cechD ℤ ι _ 1 x.1 = 0 := by
      have := hx.2
      rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
    have hrx : FibreReduction.redCoch y p 1 x.1 ∈
        KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1 :=
      Submodule.mem_inf.mpr ⟨hrd 1 _ hx.1, by
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, ← hd, hxd, map_zero]⟩
    have h0' : (Submodule.Quotient.mk ⟨_, hrx⟩ :
        KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) = 0 := Subsingleton.elim _ _
    have h0 := (Submodule.Quotient.mk_eq_zero _).mp h0'
    obtain ⟨u, hu, hdu⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp h0)
    obtain ⟨u', hu', hru'⟩ := hon 0 u hu
    have hdu' := hdg ℤ K ι _ _ a 0 u' hu'
    obtain ⟨x', hx'C, hx'eq⟩ := hker 1 (x.1 - KH.cechD ℤ ι _ 0 u') (sub_mem hx.1 hdu') (by
      rw [map_sub, hd, hru']
      exact sub_eq_zero.mpr hdu.symm)
    have hx'Z := memZ 1 x' hx'C (hnzd 2 _ (by rw [← dsmul, ← hx'eq, map_sub, hxd, dd, sub_self]))
    refine ⟨Submodule.Quotient.mk ⟨x', hx'Z⟩, ?_⟩
    rw [hq, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_zsmul]
    refine Submodule.mem_map.mpr ⟨-u', neg_mem hu', ?_⟩
    rw [LinearMap.restrictScalars_apply, map_neg, Submodule.subtype_apply, Submodule.subtype_apply]
    show _ = (p : ℤ) • x' - x.1
    rw [← hx'eq]
    abel
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj

  obtain ⟨w, hwC, hrw⟩ := hon 0 z (Submodule.mem_inf.mp hz').1
  have hzd : KH.cechD (ZMod p) ι _ 0 z = 0 := by
    have := (Submodule.mem_inf.mp hz').2
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
  obtain ⟨w', hw'C, hw'eq⟩ := hker 1 _ (hdg ℤ K ι _ _ a 0 w hwC) (by rw [hd, hrw, hzd])
  have hw'Z := memZ 1 w' hw'C (hnzd 2 _ (by rw [← dsmul, ← hw'eq, dd]))
  have hcls : (Submodule.Quotient.mk ⟨w', hw'Z⟩ : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) = 0 := by
    apply hinj
    rw [map_zero, hq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_zsmul, Submodule.subtype_apply]
    exact Submodule.mem_map.mpr ⟨w, hwC, hw'eq⟩
  obtain ⟨v, hvC, hdv⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hcls))
  have hv0 := memZ 0 (w - (p : ℤ) • v) (sub_mem hwC (zsmul_mem hvC _)) (by
    rw [map_sub, dsmul]
    rw [LinearMap.restrictScalars_apply] at hdv
    rw [hdv]
    exact sub_eq_zero.mpr hw'eq)
  obtain ⟨s, hs, hsv⟩ := hZ K ι Ω y a _ hv0
  refine ⟨s, hs, ?_⟩
  rw [← hC K ι Ω y p a s hs, hsv, map_sub, hkill, sub_zero, hrw]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtSkyscraper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ClosedPtSkyscraper

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_notMem {P : Ideal (MRingOver S ι)} (hP : P.IsPrime) {J : ∀ k, Finset (ι k)}
    (hJ : ∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) {u : MRingOver S ι} (hu : u ∈ KH.cellMon S J) :
    u ∉ P := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    exact hJ k i hi
  | one => exact (Ideal.ne_top_iff_one P).mp hP.ne_top
  | mul f f' _ _ hf hf' => exact fun h => (hP.mem_or_mem h).elim hf hf'

theorem loc_eq_zero {N : Type} [AddCommGroup N] [Module (MRingOver S ι) N] {P : Ideal (MRingOver S ι)}
    (hkill : ∀ p ∈ P, ∀ n : N, p • n = 0) {J : ∀ k, Finset (ι k)}
    (hJ : ∃ k, ∃ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∈ P) (x : LocalizedModule (KH.cellMon S J) N) :
    x = 0 := by
  obtain ⟨k, i, hi, hX⟩ := hJ
  induction x using LocalizedModule.induction_on with
  | h n w =>
    rw [← LocalizedModule.zero_mk (1 : KH.cellMon S J), LocalizedModule.mk_eq]
    refine ⟨⟨X ⟨k, i⟩, Submonoid.subset_closure ⟨k, i, hi, rfl⟩⟩, ?_⟩
    simp only [one_smul, smul_zero]
    rw [Submonoid.smul_def]
    exact hkill _ hX n

end ClosedPtSkyscraper

theorem ClosedPtSkyscraper.proof (hU : ClosedPtChartUnit.Statement) : ClosedPtSkyscraper.Statement := by
  classical
  intro S _ K _ _ ι _ _ N _ _ _ _ 𝓝 P d h𝓝 hP hkill I hI y hy
  obtain ⟨m, s, a, hsa, hm, rfl⟩ := GenSESStep.locPart_normal h𝓝 hy
  have hsP : (s : MRingOver S ι) ∉ P := ClosedPtSkyscraper.cellMon_notMem hP.1.1 hI s.2

  have hcong : ∀ p q : MRingOver S ι, p - q ∈ P → ∀ n : N, p • n = q • n := fun p q h n =>
    sub_eq_zero.mp (by rw [← sub_smul]; exact hkill _ h n)

  have hinv : ∀ J : ∀ k, Finset (ι k), (∀ k, (J k).Nonempty) →
      (∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
      ∃ t ∈ KH.cellMon S J, ∃ (g : MRingOver S ι) (b : K → ℕ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t (a + b) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b ∧ t - g * s ∈ P :=
    fun J hne hJ => hU S K ι P hP J hne hJ s a hsa hsP
  choose t ht g b htb hgb htg using hinv
  let z : KH.CechC S ι N 0 := fun J =>
    if hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P then
      LocalizedModule.mk (g J.1 J.2.1 hJ • m) ⟨t J.1 J.2.1 hJ, ht J.1 J.2.1 hJ⟩
    else 0

  have hagree : ∀ (J : KH.Cell K ι 0) (hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P)
      (u h' t' : MRingOver S ι), u - h' * s ∈ P →
      (u * t' * g J.1 J.2.1 hJ) • m = (h' * t' * t J.1 J.2.1 hJ) • m := by
    intro J hJ u h' t' hu
    refine hcong _ _ ?_ m
    have := sub_mem (P.mul_mem_right (t' * g J.1 J.2.1 hJ) hu) (P.mul_mem_left (h' * t') (htg J.1 J.2.1 hJ))
    convert this using 1
    ring
  refine ⟨z, ⟨Submodule.mem_pi.mpr fun J _ => ?_, LinearMap.mem_ker.mpr (funext fun E => ?_)⟩, ?_⟩
  ·
    by_cases hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · simp only [z, dif_pos hJ]
      refine GenSESStep.mk_mem_locPart _ _ (a + b J.1 J.2.1 hJ) (htb J.1 J.2.1 hJ) ?_
      have e : (d + fun k => ((a + b J.1 J.2.1 hJ) k : ℤ)) =
          (d + fun k => (a k : ℤ)) + fun k => (b J.1 J.2.1 hJ k : ℤ) := by
        funext k
        simp only [Pi.add_apply, Nat.cast_add]
        ring
      rw [e]
      exact h𝓝.2 _ _ _ _ (hgb J.1 J.2.1 hJ) hm
    · simp only [z, dif_neg hJ]
      exact zero_mem _
  ·
    obtain ⟨J₁, J₂, h₁, h₂, σ, -, hD⟩ := GenTwistGenerated.cechD_zero_apply (S := S) (M := N) E
    rw [Pi.zero_apply, hD z]
    by_cases hE : ∀ k, ∀ i ∈ E.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · have hJ₁ : ∀ k, ∀ i ∈ J₁.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₁ k hi)
      have hJ₂ : ∀ k, ∀ i ∈ J₂.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₂ k hi)
      obtain ⟨u, hu, h', -, -, -, huP⟩ := hU S K ι P hP E.1 E.2.1 hE s a hsa hsP
      simp only [z, dif_pos hJ₁, dif_pos hJ₂]
      rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
        GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂)]
      have heq : LocalizedModule.mk (g J₁.1 J₁.2.1 hJ₁ • m)
            (⟨t J₁.1 J₁.2.1 hJ₁, GenTwistGenerated.cellMon_mono h₁ (ht J₁.1 J₁.2.1 hJ₁)⟩ : KH.cellMon S E.1) =
          LocalizedModule.mk (g J₂.1 J₂.2.1 hJ₂ • m)
            ⟨t J₂.1 J₂.2.1 hJ₂, GenTwistGenerated.cellMon_mono h₂ (ht J₂.1 J₂.2.1 hJ₂)⟩ := by
        refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
        simp only [Submonoid.smul_def, smul_smul]
        rw [← mul_assoc, ← mul_assoc, hagree J₁ hJ₁ u h' (t J₂.1 J₂.2.1 hJ₂) huP,
          hagree J₂ hJ₂ u h' (t J₁.1 J₁.2.1 hJ₁) huP]
        congr 1
        ring
      rw [heq, sub_self]
      exact zsmul_zero σ
    · push Not at hE
      exact ClosedPtSkyscraper.loc_eq_zero hkill hE _
  ·
    simp only [z, dif_pos hI]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul]
    exact (hcong _ _ (by rw [mul_comm]; exact htg I.1 I.2.1 hI) m).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenerationOfH1Vanishing.proof (hU : ClosedPtGenUniform.Statement) (hC : GenNearCover.Statement) :
    GenerationOfH1Vanishing.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨c₂, hc₂⟩ := hH M 𝓜 hfin hgr hV e
  obtain ⟨c₃, hc₃⟩ := hC S K ι V M 𝓜 (fun c => e + c • N) hS hgr hV
    (fun P hP _ => hU S K ι V N hS hH M 𝓜 hfin hgr hV e P hP)
  exact ⟨max c₂ c₃, fun c hc => ⟨hc₂ c (le_of_max_le_left hc), hc₃ c (le_of_max_le_right hc)⟩⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
