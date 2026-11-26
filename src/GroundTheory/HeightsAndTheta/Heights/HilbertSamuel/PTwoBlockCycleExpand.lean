module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCycleExpand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockCycleExpand

theorem exists_perm_mem_iff {D : ℕ} (s : Finset (Fin D)) :
    ∃ σ : Equiv.Perm (Fin D), ∀ j, ((σ j : ℕ) < s.card ↔ j ∈ s) := by
  classical
  have hk : s.card ≤ D := by simpa using Finset.card_le_univ s
  have h1 : Fintype.card {j : Fin D // j ∈ s} = Fintype.card {j : Fin D // (j : ℕ) < s.card} := by
    rw [Fintype.card_coe]
    refine (Fintype.card_fin _).symm.trans (Fintype.card_congr ?_)
    exact { toFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, i.2⟩
            invFun := fun j => ⟨j.1, j.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  have h2 : Fintype.card {j : Fin D // ¬ j ∈ s} = Fintype.card {j : Fin D // ¬ (j : ℕ) < s.card} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun j => ?_⟩
  by_cases hj : j ∈ s
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hj,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact iff_of_true (Fintype.equivOfCardEq h1 ⟨j, hj⟩).2 hj
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hj,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact iff_of_false (Fintype.equivOfCardEq h2 ⟨j, hj⟩).2 hj

theorem expand {D : ℕ} (M : (Fin D → Fin 2 → ℤ) →ₘₗ[ℤ] ℤ)
    (hsym : ∀ (v : Fin D → Fin 2 → ℤ) (σ : Equiv.Perm (Fin D)), M (v ∘ σ) = M v) (a b : ℤ) :
    M (fun _ => ![a, b]) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℤ) * a ^ i * b ^ (D - i) * M (twoBlockDegList D i) := by
  classical
  have e : (fun _ : Fin D => ![a, b]) =
      (fun _ => a • (Pi.single 0 1 : Fin 2 → ℤ)) + (fun _ => b • (Pi.single 1 1 : Fin 2 → ℤ)) := by
    funext j k
    fin_cases k <;> simp
  have key : ∀ t : Finset (Fin D),
      M (t.piecewise (fun _ => a • (Pi.single 0 1 : Fin 2 → ℤ)) (fun _ => b • (Pi.single 1 1 : Fin 2 → ℤ))) =
        a ^ t.card * b ^ (D - t.card) * M (twoBlockDegList D t.card) := by
    intro t
    obtain ⟨σ, hσ⟩ := exists_perm_mem_iff t
    have hpw : t.piecewise (fun _ => a • (Pi.single 0 1 : Fin 2 → ℤ)) (fun _ => b • (Pi.single 1 1 : Fin 2 → ℤ)) =
        fun j => (if j ∈ t then a else b) • (twoBlockDegList D t.card ∘ σ) j := by
      funext j
      by_cases hj : j ∈ t
      · simp [Finset.piecewise, hj, twoBlockDegList, (hσ j).mpr hj]
      · have : ¬ (σ j : ℕ) < t.card := fun h => hj ((hσ j).mp h)
        simp [Finset.piecewise, hj, twoBlockDegList, this]
    rw [hpw, M.map_smul_univ, hsym]
    simp only [RingHom.id_apply, Finset.prod_ite, Finset.prod_const, smul_eq_mul]
    congr 2
    · congr 1
      simp
    · congr 1
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp
  rw [e, M.map_add_univ]
  simp_rw [key]
  rw [← Finset.powerset_univ]
  refine (Finset.sum_powerset_apply_card (fun i => a ^ i * b ^ (D - i) * M (twoBlockDegList D i))
    (x := (Finset.univ : Finset (Fin D)))).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul]
  ring

theorem geoNum_update_last_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {n : ℕ} (v : Fin (n + 1) → K → ℤ) (x y : K → ℤ) :
    geoNum (n + 1) W (Function.update v (Fin.last n) (x + y)) =
      geoNum (n + 1) W (Function.update v (Fin.last n) x) + geoNum (n + 1) W (Function.update v (Fin.last n) y) := by
  simp only [geoNum, Fin.init_update_last, Function.update_self]
  split_ifs
  · simp [add_mul, Finset.sum_add_distrib]
  · simp

theorem geoNum_update_last_smul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {n : ℕ} (v : Fin (n + 1) → K → ℤ) (c : ℤ) (x : K → ℤ) :
    geoNum (n + 1) W (Function.update v (Fin.last n) (c • x)) =
      c * geoNum (n + 1) W (Function.update v (Fin.last n) x) := by
  simp only [geoNum, Fin.init_update_last, Function.update_self]
  split_ifs
  · simp [mul_assoc, Finset.mul_sum]
  · simp

theorem geoNum_update_eq_last {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {n : ℕ} (hsym : ∀ (v : Fin (n + 1) → K → ℤ) (σ : Equiv.Perm (Fin (n + 1))), geoNum (n + 1) W (v ∘ σ) = geoNum (n + 1) W v)
    (v : Fin (n + 1) → K → ℤ) (j : Fin (n + 1)) (z : K → ℤ) :
    geoNum (n + 1) W (Function.update v j z) =
      geoNum (n + 1) W (Function.update (v ∘ Equiv.swap j (Fin.last n)) (Fin.last n) z) := by
  rw [← hsym (Function.update v j z) (Equiv.swap j (Fin.last n)), Function.update_comp_equiv,
    Equiv.symm_swap, Equiv.swap_apply_left]

def geoNumMulti {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (D : ℕ)
    (hsym : ∀ (v : Fin D → K → ℤ) (σ : Equiv.Perm (Fin D)), geoNum D W (v ∘ σ) = geoNum D W v) :
    (Fin D → K → ℤ) →ₘₗ[ℤ] ℤ where
  toFun := geoNum D W
  map_update_add' := by
    intro inst v j x y
    cases D with
    | zero => exact j.elim0
    | succ n =>
      obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
      exact (show geoNum (n + 1) W (Function.update v j (x + y)) =
          geoNum (n + 1) W (Function.update v j x) + geoNum (n + 1) W (Function.update v j y) by
        rw [geoNum_update_eq_last W hsym v j (x + y), geoNum_update_eq_last W hsym v j x,
          geoNum_update_eq_last W hsym v j y, geoNum_update_last_add])
  map_update_smul' := by
    intro inst v j c x
    cases D with
    | zero => exact j.elim0
    | succ n =>
      obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
      exact (show geoNum (n + 1) W (Function.update v j (c • x)) = c • geoNum (n + 1) W (Function.update v j x) by
        rw [geoNum_update_eq_last W hsym v j (c • x), geoNum_update_eq_last W hsym v j x,
          geoNum_update_last_smul, smul_eq_mul])

variable {κ : Type} [Fintype κ]

theorem geoNum_comp_perm {P W : Ideal (MRing (FinTwoTypeFamily κ))} {D : ℕ} (hP : IsArithVar P (D + 1)) {s : MRing (FinTwoTypeFamily κ)}
    {α : Fin 2 → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α) (hW : W ∈ divSupp P s) (hv : ¬ IsHorizontal W)
    (v : Fin D → Fin 2 → ℤ) (σ : Equiv.Perm (Fin D)) : geoNum D W (v ∘ σ) = geoNum D W v := by
  have hPp : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1.1
  have hsP : s ∉ P := by
    intro hsP
    have h1 := hW.1
    rw [sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsP), Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff] at h1
    exact hv (h1 ▸ hP.2.2.1)
  have hdim : ringKrullDim (MRing (FinTwoTypeFamily κ) ⧸ W) = ((D + Fintype.card (Fin 2) : ℕ) : WithBot ℕ∞) := by
    have h := dim_quot_minimal_add_one P W s hsP hW.1
    rw [hP.2.2.2] at h
    refine ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one (h.trans ?_)
    congr 1
  have hMP : IsMultiProjPrime W := ⟨hWp, isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1.2.1 hs hW.1, hW.2⟩
  have : Fact (charOf W).Prime := ⟨charOf_prime hWp hv⟩
  rw [← Bridge.intNum_map_eq_geoNum (charOf W) D W hMP (Inter.C_charOf_mem W) hdim,
    ← Bridge.intNum_map_eq_geoNum (charOf W) D W hMP (Inter.C_charOf_mem W) hdim,
    MixedNumberPolynomial.intNum_perm]

theorem vertCycleNum_expand {P : Ideal (MRing (FinTwoTypeFamily κ))} {D : ℕ} (hP : IsArithVar P (D + 1)) {s : MRing (FinTwoTypeFamily κ)}
    {α : Fin 2 → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α) (a b : ℕ) :
    vertCycleNum P s (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        vertCycleNum P s (twoBlockDegList D i) := by
  classical
  have hfin := divSupp_finite P s
  unfold vertCycleNum
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [Set.Finite.mem_toFinset] at hW
  split_ifs with hh
  · simp
  · have h := expand (geoNumMulti W D fun v σ => geoNum_comp_perm hP hs hW hh v σ)
      (fun v σ => geoNum_comp_perm hP hs hW hh v σ) (a : ℤ) (b : ℤ)
    change geoNum D W _ = ∑ i ∈ Finset.range (D + 1), _ * geoNum D W _ at h
    rw [h]
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem isMultiHomog_twoBlockDen (c : κ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (twoBlockDen c) (fun k => ∑ i, (Finsupp.single (⟨0, c⟩ : Σ k, FinTwoTypeFamily κ k) 1) ⟨k, i⟩) :=
  isMultiHomog_X _

theorem isMultiHomog_twoBlockNum (l : Ix κ → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (twoBlockNum l) (fun k : Fin 2 => if k = 1 then 1 else 0) := by
  classical
  intro m hm k
  unfold twoBlockNum at hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at hm
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at hj
  have hm' : Finsupp.single (⟨1, j.2⟩ : Σ k, FinTwoTypeFamily κ k) 1 = m := by
    by_contra h
    simp [h] at hj
  subst hm'
  fin_cases k <;> simp [Finsupp.single_apply]

end TwoBlockCycleExpand


open TwoBlockCycleExpand in
theorem TwoBlockCycleExpand.proof : TwoBlockCycleExpand.Statement := by
  classical
  have hA := CoordArithOfFnField.proof
  have hF := TwoBlockFnField.proof
  intro D Ω _ _ κ _ x B c l hx _ hB _ _ a b
  obtain ⟨hFp, -⟩ := hF Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx
  obtain ⟨i, hi⟩ := hx.2.1.2.2 ()
  have hx0 : x ≠ 0 := fun h => hi ((X_mem_coordIdeal_iff x _).mpr (by rw [h]; rfl))
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0
  have hpA : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  unfold twoBlockVert
  rw [vertCycleNum_expand hpA (isMultiHomog_twoBlockNum l) a b,
    vertCycleNum_expand hpA (isMultiHomog_twoBlockDen c) a b, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartPrimePowerInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ChartPrimePowerInverse.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
      ∃ M : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
          Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
            Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ e : Fin D → Fin 2 → ℤ,
      ∑ᶠ W ∈ topComps (twoBlockMInner x (matAct B x) l) D,
          ((multAt (twoBlockMInner x (matAct B x) l) W : ℝ) - multAt (twoBlockMOuter x (matAct B x) c) W) *
            Real.log (charOf W) * (geoNum D W e : ℝ) =
        twoBlockVert x (matAct B x) c l e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockPointNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def PowerBlockPointNorm.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N)),
    ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} → B.a = unitDeg (none : Option K) →
    (∀ j, v j ∈ chartLat y A.a m) →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    ∀ (q : ℕ) (F : MRing (addIdx ι N)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F (blockDeg (none : Option K) q) →
      ContinuousOn (secNormAt y A (m * q) (aeval (addBlock y v) F)) (mcPts (mCoordIdeal y)) ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)),
        secNormAt y A (m * q) (aeval (addBlock y v) F) (basePart₂ z) =
          ‖eval z (map (Int.castRingHom ℂ) F)‖ / B.h z ^ q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullGradedAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullGradedAlgebraic.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (d₀ : K → ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ (d : K → ℕ) (g : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → (∀ k, d₀ k ≤ d k) →
      ∃ a : Fin (D + 1) → MvPolynomial (Σ k, ι k) ℚ, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        aeval y g = ∑ j, aeval y (a j) * aeval y (L j)) →
    ∀ p q : Σ k, ι k, p.1 = q.1 → IsAlgebraic (pullField y L) (y p / y q)

namespace ProjLine

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleFinite.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    IsMultiHomogIdeal (twoBlockMOuter x (matAct B x) c) ∧ IsMultiHomogIdeal (twoBlockMInner x (matAct B x) l) ∧
      twoBlockMInner x (matAct B x) l ≤ twoBlockMOuter x (matAct B x) c ∧
      (∃ N : ℕ, 0 < N ∧ ∀ f ∈ twoBlockMOuter x (matAct B x) c,
        (N : MRing (FinTwoTypeFamily κ)) * f ∈ twoBlockMInner x (matAct B x) l) ∧
      ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), W.IsPrime → twoBlockMInner x (matAct B x) l ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W →
        ringKrullDim (MRing (FinTwoTypeFamily κ) ⧸ W) ≤ ((D + Fintype.card (Fin 2) : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem RelLatticeFinite.proof (hL : RelSectionsLarge.Statement) : RelLatticeFinite.Statement := by
  intro K _ ι _ Ω _ y a n m g hy
  have hN : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := adjoin_isNoetherianRing g
  obtain ⟨n₁, hn₁⟩ := hL K ι Ω (Algebra.adjoin ℤ (Set.range g)) hN y hy
  choose c0 hc0 using hy
  set R := Algebra.adjoin ℤ (Set.range g)
  let e : K → ℕ := fun k => n₁ + ((n : ℤ) * a k).natAbs
  let b : K → ℕ := fun k => ((n : ℤ) * a k + e k).toNat
  have hb : ∀ k, ((b k : ℕ) : ℤ) = (n : ℤ) * a k + e k := by
    intro k
    refine Int.toNat_of_nonneg ?_
    simp only [e]
    push_cast
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  have hbn : ∀ k, n₁ ≤ b k := by
    intro k
    have h1 := hb k
    simp only [e] at h1
    push_cast at h1
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  set mon : Ω := ∏ k, y ⟨k, c0 k⟩ ^ e k
  have hmon : mon ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  let φ : Ω →ₗ[R] Ω := LinearMap.mulRight R mon
  have hφ : Function.Injective φ := mul_left_injective₀ hmon
  have hmap : (relChartLat R y a n).map φ ≤ relSecM R y b := by
    rintro _ ⟨s, hs, rfl⟩
    exact hn₁ b hbn (mul_prod_mem_relChartLat R y e c0 (fun k => hb k) hs)
  have : IsNoetherian R (relSecM R y b) := isNoetherian_of_fg_of_noetherian _ (relSecM_fg R y b)
  exact Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le_of_isNoetherian hmap)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphChangeOfModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphChangeOfModel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} {ι₂ : K₂ → Type}

theorem exists_form_not_mem {P : Ideal (MRing ι)} {d : ℕ} {g : (Σ k, ι₂ k) → MRing ι} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P g) : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => g ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk

end GraphChangeOfModel


open GraphChangeOfModel IndefiniteRowSideFullHecke.Inter in
theorem GraphChangeOfModel.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hIso : IsomInvariance.Statement) (hGI : GraphIsometricForms.Statement) : GraphChangeOfModel.Statement := by
  intro I hI K _ ι _ K₂ _ ι₂ _ P d g δ G J L L₁ hP hg hBP hImg hJ hL hL₁ ha hh
  obtain ⟨hΓ, himg, hdeg⟩ := hGr K ι K₂ ι₂ P d g δ hP hg (exists_form_not_mem hP hBP)
  obtain ⟨G'⟩ := hGF K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := hEU G'.Φ _ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂))
  have e1 := hAI3 I hI K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d G' J' L₁
    (fun j => pullHerm isBlockMap_inl (L₁ j)) isBlockMap_inl hΓ (by rw [himg]; exact hP) hJ' hL₁
    (fun j => isPullHerm_pullHerm _ _)
  have e2 := hAI3 I hI K₂ ι₂ (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inr inrV _ d G J L
    (fun j => pullHerm isBlockMap_inr (L j)) isBlockMap_inr hΓ hImg hJ hL
    (fun j => isPullHerm_pullHerm _ _)
  have e3 := hIso (K ⊕ K₂) (Sum.elim ι ι₂) (I (K ⊕ K₂) (Sum.elim ι ι₂)) (hI _ _) _ d
    (fun j => pullHerm isBlockMap_inl (L₁ j)) (fun j => pullHerm isBlockMap_inr (L j)) hΓ
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inl (isPullHerm_pullHerm _ _) (hL₁ j))
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inr (isPullHerm_pullHerm _ _) (hL j))
    (fun j => hGI K ι K₂ ι₂ P d g δ (L₁ j) (L j) _ _ hP hg hBP (ha j) (hh j) (isPullHerm_pullHerm _ _)
      (isPullHerm_pullHerm _ _))
  rw [hdeg G' J' hJ', himg] at e1
  rw [← e2, ← e3, e1]
  simp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelOneStep

theorem chart_monomial_mem {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) (c : ∀ k, ι k) :
    ∏ k, y ⟨k, c k⟩ ^ b k ∈ relSecM R y b := by
  classical
  let μ : (Σ k, ι k) → ℕ := fun p => if p.2 = c p.1 then b p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k := by
    intro k
    simp [μ]
  have h := monomial_mem_relSecM R y μ hμ
  have heq : ∏ p, y p ^ μ p = ∏ k, y ⟨k, c k⟩ ^ b k := by
    rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [μ]
    rw [Finset.prod_congr rfl fun i _ => (show y ⟨k, i⟩ ^ (if i = c k then b k else 0) =
      if i = c k then y ⟨k, i⟩ ^ b k else 1 by split_ifs <;> simp)]
    simp
  rwa [heq] at h

end RelOneStep

theorem RelOneStep.proof (hC : RelChartPoly.Statement) (hT : RelTorsionBound.Statement) : RelOneStep.Statement := by
  intro K _ _ ι _ Ω _ R hR y c0 hc0
  choose n hn using fun k0 : K => hT K ι Ω R hR y c0 hc0 k0
  refine ⟨Finset.univ.sup n, fun b hb k0 t ht hxt => ?_⟩
  have hbk : ∀ k, n k0 ≤ b k := fun k => le_trans (Finset.le_sup (Finset.mem_univ k0)) (hb k)
  obtain ⟨g', hg', hfg⟩ := hn k0 b hbk (y ⟨k0, c0 k0⟩ * t) hxt (by
    intro c hc
    obtain ⟨N, hN⟩ := hC K ι Ω R y c _ (ht c hc)
    refine ⟨N, t * (∏ k, y ⟨k, c k⟩) ^ N, ?_, by ring⟩
    have hm := mul_mem_relSecM R y hN (RelOneStep.chart_monomial_mem R y b c)
    have hone : (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c k⟩ ^ b k = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← zpow_natCast, ← zpow_add₀ (hc k)]
      simp
    have heq : t * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * (∏ k, y ⟨k, c k⟩) ^ N *
        ∏ k, y ⟨k, c k⟩ ^ b k = t * (∏ k, y ⟨k, c k⟩) ^ N := by
      linear_combination (t * (∏ k, y ⟨k, c k⟩) ^ N) * hone
    rw [heq, add_comm] at hm
    exact hm)
  have hx : y ⟨k0, c0 k0⟩ ≠ 0 := hc0 k0
  rwa [mul_left_cancel₀ hx hfg]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockStepLocal

theorem nonempty_of_isArithVar {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {x : Ix κ → Ω}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) : Nonempty κ := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : IsEmpty (Σ k : Unit, GlobalTheory κ k) := ⟨fun p => h.false p.2⟩
  have h1 : ringKrullDim (MRing (GlobalTheory κ)) = 1 := by
    rw [ringKrullDim_mvPolynomial_of_isEmpty]
    exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField
  have h2 := ringKrullDim_quotient_le (coordIdeal ℤ x : Ideal (MRing (GlobalTheory κ)))
  rw [hX.2.2.2, h1] at h2
  have h3 : ((D + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := by simpa using h2
  have h4 := WithBot.coe_le_coe.1 h3
  norm_cast at h4

theorem choose_div_factorial {D i : ℕ} (hi : i ≤ D) (u : ℝ) :
    (D.choose i : ℝ) * u / (D.factorial : ℝ) = u / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)) := by
  have e : ((D.choose i : ℕ) : ℝ) * (i.factorial : ℝ) * ((D - i).factorial : ℝ) = (D.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have h0 : (D.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((D - i).factorial : ℝ) ≠ 0 := by positivity
  rw [← e]
  field_simp

end TwoBlockStepLocal


open TwoBlockStepLocal in
theorem TwoBlockStepLocal.proof (hA : TwoBlockPieceCycle.Statement) (hM : TwoBlockCycleExpand.Statement)
    (hR : TwoBlockCoeffCycle.Statement) : TwoBlockStepLocal.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨c⟩ := nonempty_of_isArithVar hX
  obtain ⟨l, hl⟩ : ∃ l : Ix κ → ℤ, x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j := by
    have hc : x ⟨(), c⟩ ∈ Submodule.span ℤ (Set.range (matAct B x)) :=
      hsp (Submodule.subset_span ⟨⟨(), c⟩, rfl⟩)
    obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hc
    exact ⟨l, by rw [← hl]; simp [zsmul_eq_mul]⟩
  obtain ⟨a₀, C, h⟩ := hA D Ω κ x B c l hX hx hB hsp hl
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  convert h a b ha hb using 3
  rw [hM D Ω κ x B c l hX hx hB hsp hl a b, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiD : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [hR D Ω κ I x B m m' c l hI hX hx hB hm hm' hsp hl i hiD,
    show (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i) =
      (D.choose i : ℝ) * ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i)) by ring,
    choose_div_factorial hiD]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PowerBlockArith

variable {K : Type} [Fintype K] {ι : K → Type}

theorem blockFnField_addBlock {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m N : ℕ}
    {v : Fin N → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y a m) :
    blockFnField (addBlock y v) = blockFnField y := by
  have hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y := by
    intro s hs
    have : chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
    exact this hs
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩
    · have hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ =
          (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) := by
        rw [mul_div_mul_right _ _ hP0]
        rfl
      rw [e]
      exact div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · obtain rfl : k = k' := Option.some_injective _ hpq
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _
      ⟨(⟨some p.1, p.2⟩ : Σ k, addIdx ι N k), (⟨some q.1, (hpq ▸ q.2 : ι q.1)⟩ : Σ k, addIdx ι N k),
        by simp [hpq], by cases p; cases q; simp at hpq; subst hpq; rfl⟩

end PowerBlockArith


open PowerBlockArith in
theorem PowerBlockArith.proof (hF : CoordArithOfFnField.Statement) : PowerBlockArith.Statement := by
  intro K _ ι _ Ω _ _ y D a m N v hy hv hgen

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0]
  choose c hc using hnz

  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨u, -, hu⟩ := hgen c hc
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hu
  exact hF K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩
    (fun k => by
      cases k with
      | none => exact ⟨j₀, hj₀⟩
      | some k => exact ⟨c k, hc k⟩)
    (blockFnField_addBlock c hc hv).symm hy

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TwoBlockTop

variable {κ : Type}

theorem isPullHerm_blockLine [Fintype κ] (m : ConeMetric ℂ (Ix κ)) (b : Fin 2) :
    IsPullHerm (blkOf b) (blkV κ b) (HermLine.ofCone m) (blockLine m b) := by
  refine ⟨?_, fun z => rfl⟩
  funext k
  show (Pi.single b 1 : Fin 2 → ℤ) k = Function.extend (blkOf b) (fun _ : Unit => (1 : ℤ)) 0 k
  by_cases hk : k = b
  · subst hk
    rw [Pi.single_eq_same]
    exact (Function.Injective.extend_apply (f := blkOf k) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 2 → ℤ) ()).symm
  · rw [Pi.single_eq_of_ne hk, Function.extend_apply' _ _ _ (fun ⟨_, hu⟩ => hk hu.symm)]
    rfl

theorem pair_comp_blkV_zero {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 0 = x := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

theorem pair_comp_blkV_one {Ω : Type} [Field Ω] (x x' : Ix κ → Ω) : pair x x' ∘ blkV κ 1 = x' := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp [pair, blkV]

end TwoBlockTop


open TwoBlockTop in
theorem TwoBlockTop.proof (hPF : PFCoordStatement) (hIm : ImageCoordStatement) (hA : CoordArithOfFnField.Statement)
    (hF : TwoBlockFnField.Statement) (hS : MetricTransportSmooth.Statement) : TwoBlockTop.Statement := by
  classical
  intro D Ω _ _ κ _ I x B m m' hI hx _ hB hm hm'
  obtain ⟨hFp, hFB⟩ := hF Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx

  obtain ⟨i, hi⟩ := hx.2.1.2.2 ()
  have hx0 : x ≠ 0 := fun h => hi ((X_mem_coordIdeal_iff x _).mpr (by rw [h]; rfl))
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0

  have hpA : IsArithVar (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hBA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) (matAct B x)) (D + 1) :=
    hA Unit (GlobalTheory κ) Unit (GlobalTheory κ) Ω x (matAct B x) (D + 1) ⟨()⟩ (fun _ => ⟨i₁, hi₁⟩) hFB.symm hxA

  have key : ∀ (b : Fin 2) (z : Ix κ → Ω) (μ : ConeMetric ℂ (Ix κ)), pair x (matAct B x) ∘ blkV κ b = z →
      IsArithVar (mCoordIdeal (ι := GlobalTheory κ) z) (D + 1) →
      blockFnField (ι := GlobalTheory κ) z = blockFnField (ι := GlobalTheory κ) x → IsSmoothMetric μ →
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine μ b) = top I z μ D := by
    intro b z μ hz hzA hzF hμ
    have himg : imageZ (blkV κ b) (mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x (matAct B x))) = coordIdeal ℤ z := by
      rw [hIm Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω _ (isBlockMap_blkV κ b), hz,
        coordIdeal_eq_mCoordIdeal]
    have h := hPF I hI Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) (blkOf b) (blkV κ b) Ω (pair x (matAct B x)) (D + 1)
      (fun _ => HermLine.ofCone μ) (fun _ => blockLine μ b) (isBlockMap_blkV κ b) hpA
      (by rw [himg, coordIdeal_eq_mCoordIdeal]; exact hzA)
      (fun _ => gbamix_smoothHerm_ofCone hμ) (fun _ => isPullHerm_blockLine μ b)
    rw [IntermediateField.relfinrank_eq_one_iff.mpr (by rw [hz, hzF, hFp]), Nat.cast_one, one_mul] at h
    rw [top, ← himg]
    exact h
  exact ⟨key 0 x m (pair_comp_blkV_zero _ _) hxA rfl hm,
    key 1 (matAct B x) m' (pair_comp_blkV_one _ _) hBA hFB (hS κ B m m' hB hm hm')⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.VanishOfVanishNsmul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem vanish_of_vanish_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (N : K → ℤ) {q : ℕ}
    (hq : 1 ≤ q)
    (h : ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + (c * q) • N) 1))
    (e : K → ℤ) : ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) := by
  choose c₀ hc₀ using fun r : ℕ => h (e + r • N)
  refine ⟨((Finset.range q).sup c₀ + 1) * q, fun c hc => ?_⟩
  have hr : c % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  have h1 : c₀ (c % q) ≤ (Finset.range q).sup c₀ := Finset.le_sup (f := c₀) hr
  have h2 : (Finset.range q).sup c₀ + 1 ≤ c / q := (Nat.le_div_iff_mul_le (by omega)).mpr hc
  have h3 := hc₀ (c % q) (c / q) (by omega)
  have e' : e + (c % q) • N + (c / q * q) • N = e + c • N := by
    rw [add_assoc, ← add_smul, Nat.mod_add_div' c q]
  rwa [e'] at h3

theorem KleimanVarietyH1Generation.proof (hK : KH.KAmpStatement) (hDev : H1VanishingDevissage.Statement)
    (hGen : GenerationOfH1Vanishing.Statement) : KleimanVarietyH1Generation.Statement := by
  intro F _ K _ _ ι _ _ I Q α b a hI hQ hN hb ha
  refine hGen F K ι Q _ inferInstance (hDev F K ι Q _ inferInstance fun P hP hQP e => ?_)

  obtain ⟨D, hKD, hD⟩ := Targets.ContractMixedField.exists_dim hP
  have hPd : IsProjVarF P (D - Fintype.card K) := ⟨hP, by rw [hD, Nat.sub_add_cancel hKD]⟩
  have hNP : KH.NefOnF I P α := fun W hW hPW => hN W hW (hQP.trans hPW)

  obtain ⟨q, hq, -, hvan⟩ := hK F K ι I P _ α b a hI hPd hNP hb ha
  exact vanish_of_vanish_nsmul _ _ hq hvan e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
