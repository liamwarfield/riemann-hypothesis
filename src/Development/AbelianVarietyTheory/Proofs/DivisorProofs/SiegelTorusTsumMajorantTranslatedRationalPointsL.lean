module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorRationalMatricesInBox
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominator
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.BoundedDen

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → Af D.host.F ⊗[D.host.F] D.host.E) = fun z => (e z).2 := by
    funext z; exact ((he z).2).symm
  rw [this]
  exact continuous_snd.comp hc


set_option maxHeartbeats 1000000 in
theorem bounded_den : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E,
    finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  intro D K hK
  let U : AddSubgroup (AE D) := (intAE D).comap (finPart D).toAddMonoidHom
  have hU : IsOpen (U : Set (AE D)) :=
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_finPart D)
  obtain ⟨n, hn⟩ := GlobalTheory.CondBound.exists_small D K hK U hU
  refine ⟨n.factorial, Nat.factorial_pos n, fun k hk x hx => ?_⟩
  have h := hn k hk
  have h2 : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) ∈ intAE D := by
    have e : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) =
        finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * k) := by
      rw [map_mul (incA D), map_mul (finPart D), map_mul (finPart D), hx, GlobalTheory.CondBound.finPart_r]
    rw [e]; exact h
  obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h2
  have e2 : (((n.factorial : ℕ) : D.host.E) * x) = (y : D.host.E) := hy.symm
  rw [e2]
  exact NumberField.RingOfIntegers.isIntegral_coe y

end GlobalTheory.BoundedDen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominatorStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_finPart_in_compact_bounded_denominator : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E, finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  first | exact @GlobalTheory.BoundedDen.bounded_den | exact GlobalTheory.BoundedDen.bounded_den | (intros; apply GlobalTheory.BoundedDen.bounded_den <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorRationalMatricesInBox
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaConv

theorem exists_den_of_inBox : ∀ (D : D7) (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ (x : Mx D m n) (ξ : Matrix (Fin m) (Fin n) D.host.E), x.map (finPart D) = (ξ.map (incA D) : Mx D m n).map (finPart D) → GlobalTheory.Unf.InBox K x → ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j) := by
  intro D m n K hK
  have hK1 : IsCompact (⋃ p : Fin m × Fin n, (fun x : Mx D m n => x p.1 p.2) '' K) :=
    isCompact_iUnion fun p => hK.image (continuous_id.matrix_elem p.1 p.2)
  obtain ⟨L, hL, h⟩ := GlobalTheory.T.rational_finPart_in_compact_bounded_denominator D _ hK1
  refine ⟨L, hL, fun x ξ hx ⟨k, hk, hxk⟩ i j => ?_⟩
  refine h (k i j) (Set.mem_iUnion.2 ⟨(i, j), k, hk, rfl⟩) (ξ i j) ?_
  have h1 : finPart D (x i j) = finPart D (incA D (ξ i j)) := congrFun (congrFun hx i) j
  have h2 : finPart D (x i j - k i j) = 0 := congrFun (congrFun hxk i) j
  have h3 : finPart D (x i j) - finPart D (k i j) = 0 :=
    ((finPart D).map_sub (x i j) (k i j)).symm.trans h2
  exact h1.symm.trans (sub_eq_zero.1 h3)

end GlobalTheory.ThetaConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorRationalMatricesInBoxStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_denominator_rational_matrices_in_box : ∀ (D : D7) (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ (x : Mx D m n) (ξ : Matrix (Fin m) (Fin n) D.host.E), x.map (finPart D) = (ξ.map (incA D) : Mx D m n).map (finPart D) → GlobalTheory.Unf.InBox K x → ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j) := by
  first | exact @GlobalTheory.ThetaConv.exists_den_of_inBox | exact GlobalTheory.ThetaConv.exists_den_of_inBox | (intros; apply GlobalTheory.ThetaConv.exists_den_of_inBox <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInverseLatticeCountStackedEigenprojections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalising
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralTupleLatticeCountBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralTupleLatticeCountBound
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedCount
open NumberField GlobalTheory.LatCount

theorem weighted_count : ∀ (D : D7) (κ : Type) [Fintype κ] (L : ℕ), 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ s : κ → ℝ, (∀ k, 0 < s k) → ∑' η : κ → D.host.E,
      {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)}.indicator
        (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^ N)⁻¹)) η ≤
      ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
  intro D κ _ L hL
  classical
  obtain ⟨C₀, hC₀, hCb⟩ := exists_repr_le D
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let P := κ × ι
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨2 * Fintype.card P, (1 + 2 * C₀ * L) ^ Fintype.card P, by positivity, fun s hs => ?_⟩
  set S := {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)} with hS
  rw [← tsum_subtype S]
  let b : P → ℝ := fun p => 1 / (C₀ * L * s p.1)
  have hb : ∀ p, 0 < b p := fun p => by have := hs p.1; positivity
  let kap : (κ → D.host.E) → P → ℤ := fun η p =>
    ⌊(integralBasis D.host.E).repr ((L : D.host.E) * η p.1) p.2⌋
  have hint : ∀ η ∈ S, ∀ p : P, (((kap η p : ℤ) : ℚ)) =
      (L : ℚ) * (integralBasis D.host.E).repr (η p.1) p.2 := by
    intro η hη p
    rw [← repr_nat_mul]
    exact repr_int (hη p.1) p.2
  let G : (P → ℤ) → ℝ≥0∞ := fun z => ∏ p, ENNReal.ofReal (((1 + b p * |((z p : ℤ) : ℝ)|) ^ 2)⁻¹)
  have hpt : ∀ η : S, ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ ((η : κ → D.host.E) k)‖) / s k) ^
      (2 * Fintype.card P))⁻¹) ≤ G (kap η) := by
    rintro ⟨η, hη⟩
    show ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^
      (2 * Fintype.card P))⁻¹) ≤ G (kap η)
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k := ⟨_, rfl⟩
    rw [← hT]
    have hterm : ∀ k, 0 ≤ (∑ τ, ‖tauE D τ (η k)‖) / s k := fun k =>
      div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hs k).le
    have hT0 : 0 ≤ T := by rw [hT]; exact Finset.sum_nonneg fun k _ => hterm k
    have hkp : ∀ p : P, 1 + b p * |((kap η p : ℤ) : ℝ)| ≤ 1 + T := by
      rintro ⟨k, l⟩
      have e1 : |((kap η (k, l) : ℤ) : ℝ)| =
          L * |((integralBasis D.host.E).repr (η k) l : ℝ)| := by
        have := congrArg (fun q : ℚ => (q : ℝ)) (hint η hη (k, l))
        simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
        rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have hsk := hs k
      have h1 : |((integralBasis D.host.E).repr (η k) l : ℝ)| ≤
          ∑ l', |((integralBasis D.host.E).repr (η k) l' : ℝ)| :=
        Finset.single_le_sum (f := fun l' => |((integralBasis D.host.E).repr (η k) l' : ℝ)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
      have h2 := hCb (η k)
      have h3 : (∑ τ, ‖tauE D τ (η k)‖) / s k ≤ T := by
        rw [hT]
        exact Finset.single_le_sum (f := fun k => (∑ τ, ‖tauE D τ (η k)‖) / s k)
          (fun k _ => hterm k) (Finset.mem_univ k)
      have e2 : b (k, l) * |((kap η (k, l) : ℤ) : ℝ)| =
          |((integralBasis D.host.E).repr (η k) l : ℝ)| / (C₀ * s k) := by
        rw [e1]; simp only [b]; field_simp
      have h4 : |((integralBasis D.host.E).repr (η k) l : ℝ)| / (C₀ * s k) ≤
          (∑ τ, ‖tauE D τ (η k)‖) / s k := by
        rw [div_le_div_iff₀ (by positivity) hsk]
        nlinarith
      linarith
    show ENNReal.ofReal (((1 + T) ^ (2 * Fintype.card P))⁻¹) ≤
      ∏ p, ENNReal.ofReal (((1 + b p * |((kap η p : ℤ) : ℝ)|) ^ 2)⁻¹)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => by have := hb p; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.prod_inv_distrib]
    apply inv_anti₀ (Finset.prod_pos fun p _ => by have := hb p; positivity)
    calc ∏ p, (1 + b p * |((kap η p : ℤ) : ℝ)|) ^ 2 ≤ ∏ _p : P, (1 + T) ^ 2 :=
          Finset.prod_le_prod₀ (fun p _ => by have := hb p; positivity)
            (fun p _ => pow_le_pow_left₀ (by have := hb p; positivity) (hkp p) 2)
      _ = (1 + T) ^ (2 * Fintype.card P) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hinj : Function.Injective (fun η : S => kap η) := by
    rintro ⟨η, hη⟩ ⟨η', hη'⟩ h
    apply Subtype.ext
    funext k
    have hL0 : (L : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
    apply mul_left_cancel₀ hL0
    apply (integralBasis D.host.E).repr.injective
    ext l
    have h1 := hint η hη (k, l)
    have h2 := hint η' hη' (k, l)
    have h3 : kap η (k, l) = kap η' (k, l) := congrFun h (k, l)
    rw [repr_nat_mul, repr_nat_mul]
    rw [← h1, ← h2, h3]
  have hcard : Fintype.card ι = Module.finrank ℚ D.host.E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  have hbnd : ∀ p : P, 1 + 2 / b p ≤ (1 + 2 * C₀ * L) * max 1 (s p.1) := by
    intro p
    have e : 2 / b p = 2 * C₀ * L * s p.1 := by simp only [b]; field_simp
    rw [e]
    have h1 : (1 : ℝ) ≤ max 1 (s p.1) := le_max_left _ _
    have h2 : s p.1 ≤ max 1 (s p.1) := le_max_right _ _
    have : 0 ≤ 2 * C₀ * L := by positivity
    nlinarith
  calc ∑' η : S, ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ ((η : κ → D.host.E) k)‖) / s k) ^
        (2 * Fintype.card P))⁻¹)
      ≤ ∑' η : S, G (kap η) := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' z, G z := ENNReal.tsum_comp_le_tsum_of_injective hinj G
    _ = ∏ p : P, ∑' z : ℤ, ENNReal.ofReal (((1 + b p * |(z : ℝ)|) ^ 2)⁻¹) :=
        GlobalTheory.HL.tsum_pi_prod_ennreal (X := fun _ : P => ℤ)
          (fun (p : P) (z : ℤ) => ENNReal.ofReal (((1 + b p * |(z : ℝ)|) ^ 2)⁻¹))
    _ ≤ ∏ p : P, ENNReal.ofReal (1 + 2 / b p) := Finset.prod_le_prod' fun p _ => tsum_int_le (hb p)
    _ = ENNReal.ofReal (∏ p : P, (1 + 2 / b p)) :=
        (ENNReal.ofReal_prod_of_nonneg (fun p _ => by have := hb p; positivity)).symm
    _ ≤ ENNReal.ofReal ((1 + 2 * C₀ * L) ^ Fintype.card P *
          ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∏ p : P, (1 + 2 / b p) ≤ ∏ p : P, ((1 + 2 * C₀ * L) * max 1 (s p.1)) :=
              Finset.prod_le_prod₀ (fun p _ => by have := hb p; positivity) (fun p _ => hbnd p)
          _ = (1 + 2 * C₀ * L) ^ Fintype.card P * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
              congr 1
              rw [Fintype.prod_prod_type]
              refine Finset.prod_congr rfl fun k _ => ?_
              show ∏ _y : ι, max 1 (s k) = _
              rw [Finset.prod_const, Finset.card_univ, hcard]

end GlobalTheory.WeightedCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralTupleLatticeCountBoundStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_integral_tuple_lattice_count_bound : ∀ (D : D7) (κ : Type) [Fintype κ] (L : ℕ), 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ s : κ → ℝ, (∀ k, 0 < s k) → ∑' η : κ → D.host.E, {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)}.indicator (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^ N)⁻¹)) η ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
  first | exact @GlobalTheory.WeightedCount.weighted_count | exact GlobalTheory.WeightedCount.weighted_count | (intros; apply GlobalTheory.WeightedCount.weighted_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledEmbeddingNormBoundHostField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledEmbeddingNormBoundHostField
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.GNorm

theorem entry_bound {ι κ E : Type} [Fintype κ] [DecidableEq κ] [Ring E] {m n : ℕ}
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) (s : κ → ℝ) (hs : ∀ k, 0 < s k)
    (B : ι → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ))
    (ξ : Matrix (Fin m) (Fin n) E) (τ : ι) (k : κ) (j : Fin n) :
    ‖σ τ ((T * ξ) k j)‖ / s k ≤ ∑ i, ‖T.map (σ τ) k i‖ * ‖(B τ * ξ.map (σ τ)) i j‖ := by
  have hmap : σ τ ((T * ξ) k j) = (T.map (σ τ) * ξ.map (σ τ)) k j := by
    rw [← Matrix.map_mul]; rfl
  have key : ((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j) = (T.map (σ τ) * (B τ * ξ.map (σ τ))) k j := by
    rw [hmap, ← Matrix.mul_assoc, hB τ, Matrix.mul_assoc, Matrix.diagonal_mul]
  have hnorm : ‖σ τ ((T * ξ) k j)‖ / s k = ‖((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hs k).le, div_eq_inv_mul]
  rw [hnorm, key, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ => norm_mul _ _)

theorem gnorm_gen {ι κ E : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Ring E] (m n : ℕ)
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : ι → Matrix (Fin m) (Fin m) ℂ,
      (∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ)) →
      ∀ ξ : Matrix (Fin m) (Fin n) E,
        ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤
          C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (σ τ)) i j‖ := by
  set c : ℝ := ∑ τ, ∑ k, ∑ i, ‖T.map (σ τ) k i‖ with hc
  have hc0 : 0 ≤ c := by positivity
  have hac : ∀ τ k i, ‖T.map (σ τ) k i‖ ≤ c := by
    intro τ k i
    have h1 : ‖T.map (σ τ) k i‖ ≤ ∑ i', ‖T.map (σ τ) k i'‖ :=
      Finset.single_le_sum (f := fun i' => ‖T.map (σ τ) k i'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i', ‖T.map (σ τ) k i'‖ ≤ ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ :=
      Finset.single_le_sum (f := fun k' => ∑ i', ‖T.map (σ τ) k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ k)
    have h3 : ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ ≤ c :=
      Finset.single_le_sum (f := fun τ' => ∑ k', ∑ i', ‖T.map (σ τ') k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ τ)
    linarith
  refine ⟨1 + Fintype.card κ * c, by nlinarith [hc0, (Nat.cast_nonneg (Fintype.card κ) : (0:ℝ) ≤ _)], ?_⟩
  intro s hs B hB ξ
  set b : ι → Fin m → Fin n → ℝ := fun τ i j => ‖(B τ * ξ.map (σ τ)) i j‖ with hb
  have hb0 : ∀ τ i j, 0 ≤ b τ i j := fun _ _ _ => norm_nonneg _
  have S0 : 0 ≤ ∑ τ, ∑ i, ∑ j, b τ i j := by positivity
  calc ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1
      = ∑ p : κ × Fin n, ∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖ / s p.1 := by
        simp_rw [Finset.sum_div]
    _ ≤ ∑ p : κ × Fin n, ∑ τ, ∑ i, c * b τ i p.2 := by
        gcongr with p _ τ _
        refine (entry_bound σ T s hs B hB ξ τ p.1 p.2).trans ?_
        gcongr with i _
        exact hac τ p.1 i
    _ = ∑ _k : κ, ∑ j : Fin n, ∑ τ, ∑ i, c * b τ i j := by
        rw [Fintype.sum_prod_type]
    _ = Fintype.card κ * (c * ∑ j, ∑ τ, ∑ i, b τ i j) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Finset.mul_sum]
    _ = Fintype.card κ * c * ∑ τ, ∑ i, ∑ j, b τ i j := by
        rw [mul_assoc]
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_comm]
    _ ≤ (1 + Fintype.card κ * c) * ∑ τ, ∑ i, ∑ j, b τ i j := by nlinarith

end GlobalTheory.Proof.GNorm

namespace GlobalTheory

theorem tGnorm : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E), ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤ C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ := by
  intro D κ _ _ m n T
  exact GlobalTheory.Proof.GNorm.gnorm_gen m n (tauE D) T

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledEmbeddingNormBoundHostFieldStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaledEmbeddingNorm_bound_hostField : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E), ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤ C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ := by
  first | exact @GlobalTheory.tGnorm | exact GlobalTheory.tGnorm | (intros; apply GlobalTheory.tGnorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCmFieldEqTwoMulTotallyRealSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCmFieldEqTwoMulTotallyRealSubfield
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.cm_finrank_eq_two_mul (D : D7) :
    Module.finrank ℚ D.host.E = Module.finrank ℚ D.host.F * 2 := by
  have h := (GlobalTheory.AdelicU.isCMExt_host D).2.2.1
  rw [← h]
  exact (Module.finrank_mul_finrank ℚ D.host.F D.host.E).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCmFieldEqTwoMulTotallyRealSubfieldStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cmField_eq_two_mul_totallyRealSubfield : ∀ D : D7, Module.finrank ℚ D.host.E = Module.finrank ℚ D.host.F * 2 := by
  first | exact @GlobalTheory.cm_finrank_eq_two_mul | exact GlobalTheory.cm_finrank_eq_two_mul | (intros; apply GlobalTheory.cm_finrank_eq_two_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorBoundMatrixMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorBoundMatrixMul
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem denom_bound_mul : ∀ (E κ ι : Type) [Field E] [NumberField E] [Fintype κ] [Fintype ι] (T : Matrix κ ι E), ∃ M : ℕ, 0 < M ∧ ∀ (L : ℕ) (x : ι → E), (∀ i, IsIntegral ℤ ((L : E) * x i)) → ∀ k, IsIntegral ℤ (((M * L : ℕ) : E) * ∑ i, T k i * x i) := by
  intro E κ ι _ _ _ _ T
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image (fun p : κ × ι => T p.1 p.2))
  refine ⟨y.natAbs ^ 2, by positivity, ?_⟩
  intro L x hx k
  have hT : ∀ i, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * T k i) := by
    intro i
    have h1 := hint (T k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
    have hy' : IsIntegral ℤ ((y : E)) := by
      have := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E y)); simpa using this
    have : ((y.natAbs ^ 2 : ℕ) : E) * T k i = (y : E) * (y • T k i) := by
      rw [zsmul_eq_mul]
      have : ((y.natAbs ^ 2 : ℕ) : E) = ((y ^ 2 : ℤ) : E) := by
        have hz : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
        rw [← hz, Int.cast_natCast]
      rw [this]; push_cast; ring
    rw [this]
    exact hy'.mul h1
  have heq : (((y.natAbs ^ 2 * L : ℕ) : E) * ∑ i, T k i * x i)
      = ∑ i, (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [heq]
  have := Subalgebra.sum_mem (integralClosure ℤ E) (t := Finset.univ)
    (f := fun i => (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i))
    (fun i _ => Subalgebra.mul_mem _ (hT i) (hx i))
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorBoundMatrixMulStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_bound_matrix_mul : ∀ (E κ ι : Type) [Field E] [NumberField E] [Fintype κ] [Fintype ι] (T : Matrix κ ι E), ∃ M : ℕ, 0 < M ∧ ∀ (L : ℕ) (x : ι → E), (∀ i, IsIntegral ℤ ((L : E) * x i)) → ∀ k, IsIntegral ℤ (((M * L : ℕ) : E) * ∑ i, T k i * x i) := by
  first | exact @GlobalTheory.denom_bound_mul | exact GlobalTheory.denom_bound_mul | (intros; apply GlobalTheory.denom_bound_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalising
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem lattice_count_diag_mul : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E) (S : Matrix (Fin m) κ D.host.E), S * T = 1 → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D κ _ _ m n T S hST L hL
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.exists_denominator_bound_matrix_mul D.host.E κ (Fin m) T
  obtain ⟨N, C₁, hC₁, hcount⟩ := GlobalTheory.T.weighted_integral_tuple_lattice_count_bound D (κ × Fin n) (M * L) (Nat.mul_pos hM0 hL)
  obtain ⟨C₂, hC₂, hnorm⟩ := GlobalTheory.T.exists_scaledEmbeddingNorm_bound_hostField D κ m n T
  refine ⟨N, C₂ ^ N * C₁, mul_nonneg (pow_nonneg (by linarith) _) hC₁, ?_⟩
  intro s hs B hB
  set e : Matrix (Fin m) (Fin n) D.host.E → (κ × Fin n → D.host.E) := fun ξ p => (T * ξ) p.1 p.2 with he
  have he_inj : Function.Injective e := by
    intro ξ ξ' h
    have h' : T * ξ = T * ξ' := Matrix.ext fun k j => congrFun h (k, j)
    calc ξ = S * T * ξ := by rw [hST, Matrix.one_mul]
      _ = S * T * ξ' := by rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc]
      _ = ξ' := by rw [hST, Matrix.one_mul]
  set s' : κ × Fin n → ℝ := fun p => s p.1 with hs'
  have hs'pos : ∀ p, 0 < s' p := fun p => hs p.1
  have hc := hcount s' hs'pos
  set G : (κ × Fin n → D.host.E) → ℝ≥0∞ := {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)}.indicator (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s' k) ^ N)⁻¹)) with hG
  have hterm : ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C₂ ^ N) * G (e ξ) := by
    intro ξ
    by_cases hξ : ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)
    · rw [Set.indicator_of_mem (by exact hξ : ξ ∈ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      have hmem : e ξ ∈ {η : κ × Fin n → D.host.E | ∀ k, IsIntegral ℤ (((M * L : ℕ) : D.host.E) * η k)} := by
        intro p
        have := hM L (fun i => ξ i p.2) (fun i => hξ i p.2) p.1
        simpa [he, Matrix.mul_apply] using this
      rw [hG, Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
      apply ENNReal.ofReal_le_ofReal
      have hA := hnorm s hs B hB ξ
      set W := ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ with hW
      set A := ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 with hAdef
      have hW0 : 0 ≤ W := by positivity
      have hA0 : 0 ≤ A := Finset.sum_nonneg (fun p _ => div_nonneg (by positivity) (hs p.1).le)
      have h1 : 1 + A ≤ C₂ * (1 + W) := by nlinarith
      have hp1 : 0 < (1 + A) ^ N := by positivity
      have hp2 : 0 < (1 + W) ^ N := by positivity
      have h2 : (1 + A) ^ N ≤ C₂ ^ N * (1 + W) ^ N := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 N
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp2 hp1]
      linarith
    · rw [Set.indicator_of_notMem (by exact hξ : ξ ∉ {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)})]
      exact bot_le
  calc _ ≤ ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ENNReal.ofReal (C₂ ^ N) * G (e ξ) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (C₂ ^ N) * ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, G (e ξ) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ∑' η, G η := by gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective he_inj G
    _ ≤ ENNReal.ofReal (C₂ ^ N) * ENNReal.ofReal (C₁ * ∏ p, max 1 (s' p) ^ Module.finrank ℚ D.host.E) := by gcongr
    _ = ENNReal.ofReal (C₂ ^ N * C₁ * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (by linarith) _), mul_assoc]
      congr 2
      rw [Fintype.prod_prod_type]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      simp only [hs', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, GlobalTheory.T.finrank_cmField_eq_two_mul_totallyRealSubfield D]
      ring_nf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalisingStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCount_sum_bound_of_rational_diagonalising : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E) (S : Matrix (Fin m) κ D.host.E), S * T = 1 → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  first | exact @GlobalTheory.lattice_count_diag_mul | exact GlobalTheory.lattice_count_diag_mul | (intros; apply GlobalTheory.lattice_count_diag_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusCone
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusCone
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConeMax

theorem prod_max_le_prod (r m e : ℕ) (c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c,
    ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤
      C * ∏ i, t i ^ e := by
  set c0 : ℝ := min c 1 ^ r with hc0
  have hm0 : 0 < min c 1 := lt_min hc one_pos
  have hc0pos : 0 < c0 := pow_pos hm0 r
  have hc0le : c0 ≤ 1 := pow_le_one₀ hm0.le (min_le_right _ _)
  refine ⟨(c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r, by positivity, ?_⟩
  intro t ht
  have hlow : ∀ i, c0 ≤ t i := fun i => GlobalTheory.LatCount.cone_pow_le hc ht i
  have htpos : ∀ i, 0 < t i := fun i => hc0pos.trans_le (hlow i)
  have h1 : ∀ i, max 1 (t i) ≤ t i * c0⁻¹ := by
    intro i
    have hi : 1 ≤ c0⁻¹ := one_le_inv₀ hc0pos |>.2 hc0le
    refine max_le ?_ ?_
    · rw [← mul_inv_cancel₀ hc0pos.ne']
      exact mul_le_mul_of_nonneg_right (hlow i) (inv_nonneg.2 hc0pos.le)
    · exact le_mul_of_one_le_right (htpos i).le hi
  have h2 : ∀ i, max 1 (t i)⁻¹ ≤ c0⁻¹ := by
    intro i
    refine max_le (one_le_inv₀ hc0pos |>.2 hc0le) ?_
    exact inv_anti₀ hc0pos (hlow i)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, max_self, one_pow, Finset.prod_const_one, mul_one]
  have A : ∏ i : Fin r, max 1 (t i) ^ e ≤ ∏ i : Fin r, (t i ^ e * c0⁻¹ ^ e) := by
    refine Finset.prod_le_prod₀ (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (le_max_left _ _ |>.trans' zero_le_one) (h1 i) e
  have B : ∏ i : Fin r, max 1 (t i)⁻¹ ^ e ≤ ∏ _i : Fin r, c0⁻¹ ^ e :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ =>
      pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (h2 i) e
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at A
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at B
  have hA0 : 0 ≤ ∏ i : Fin r, max 1 (t i)⁻¹ ^ e := Finset.prod_nonneg fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  calc (∏ i : Fin r, max 1 (t i) ^ e) * ∏ i : Fin r, max 1 (t i)⁻¹ ^ e
      ≤ ((∏ i : Fin r, t i ^ e) * (c0⁻¹ ^ e) ^ r) * (c0⁻¹ ^ e) ^ r :=
        mul_le_mul A B hA0
          (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (htpos i).le _) (by positivity))
    _ = (c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r * ∏ i, t i ^ e := by ring

end GlobalTheory.ConeMax
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusConeStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone : ∀ (r m e : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤ C * ∏ i, t i ^ e := by
  first | exact @GlobalTheory.ConeMax.prod_max_le_prod | exact GlobalTheory.ConeMax.prod_max_le_prod | (intros; apply GlobalTheory.ConeMax.prod_max_le_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInverseLatticeCountStackedEigenprojections
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusStack

theorem lattice_count_stack : ∀ (D : D7) (m n r : ℕ) (X Y : Matrix (Fin m) (Fin r) D.host.E) (X' Y' : Matrix (Fin r) (Fin m) D.host.E) (c : ℝ), 0 < c → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, Y'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map (tauE D τ) ∧ X'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map (tauE D τ) ∧ (1 - X * Y' - Y * X').map (tauE D τ) * B τ = (1 - X * Y' - Y * X').map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D m n r X Y X' Y' c hc L hL
  have hST : Matrix.fromCols X (Matrix.fromCols Y (1 : Matrix (Fin m) (Fin m) D.host.E)) *
      Matrix.fromRows Y' (Matrix.fromRows X' (1 - X * Y' - Y * X')) = 1 := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.one_mul]
    abel
  obtain ⟨N, C, hC, h⟩ := GlobalTheory.T.latticeCount_sum_bound_of_rational_diagonalising D (Fin r ⊕ Fin r ⊕ Fin m) m n _ _ hST L hL
  obtain ⟨C', hC', h'⟩ := GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone r m (Module.finrank ℚ D.host.F * (2 * n)) c hc
  refine ⟨N, C * C', mul_nonneg hC hC', fun t ht B hB => ?_⟩
  have htpos : ∀ i, 0 < t i := ht.1
  refine (h (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ)))) ?_ B ?_).trans ?_
  · rintro (k | k | k)
    · exact htpos k
    · exact inv_pos.2 (htpos k)
    · exact one_pos
  · intro τ
    obtain ⟨h1, h2, h3⟩ := hB τ
    ext k j
    rcases k with k | k | k
    · have := congrFun (congrFun h1 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h2 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h3 k) j
      rw [Matrix.diagonal_mul]
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.fromRows_apply_inr, Sum.elim_inr,
        Complex.ofReal_one, inv_one, one_mul] at this ⊢
      exact this
  · apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h' t ht) hC

end GlobalTheory.TorusStack
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInverseLatticeCountStackedEigenprojectionsStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusInverse_latticeCount_stacked_eigenprojections : ∀ (D : D7) (m n r : ℕ) (X Y : Matrix (Fin m) (Fin r) D.host.E) (X' Y' : Matrix (Fin r) (Fin m) D.host.E) (c : ℝ), 0 < c → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, Y'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map (tauE D τ) ∧ X'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map (tauE D τ) ∧ (1 - X * Y' - Y * X').map (tauE D τ) * B τ = (1 - X * Y' - Y * X').map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  first | exact @GlobalTheory.TorusStack.lattice_count_stack | exact GlobalTheory.TorusStack.lattice_count_stack | (intros; apply GlobalTheory.TorusStack.lattice_count_stack <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementInvFinitePartOneDualFrameEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrame
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusDict

open GlobalTheory.AdelicU

theorem compAt_mt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (a : GA D V) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) a) := by
  refine Matrix.ext fun i j => ?_
  change θ τ (infPart D (Formalism.L2.Theta.mt V a i j)) = _
  rw [eq_infProj hθ (embOverOf D τ) rfl]
  exact GlobalTheory.Doubling.infProj_fst (embOverOf D τ) _

theorem torus_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Fin r → ℝ) (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a).map (finPart D) = 1 ∧ ∀ τ, Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * X.map (tauE D τ) = X.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) ∧ Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Y.map (tauE D τ) = Y.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) ∧ ∀ z : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) *ᵥ z = 0 → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) *ᵥ z = 0 → Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *ᵥ (fun i => tauE D τ (z i)) = fun i => tauE D τ (z i) := by
  intro D θ hθ V r X Y t a ha
  refine ⟨congrArg Units.val (MonoidHom.mem_ker.1 ha.1), fun τ => ?_⟩
  rw [compAt_mt hθ V a τ]
  exact ha.2 (placeOf D τ) (embOverOf D τ)

end GlobalTheory.TorusDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrameStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTorusElement_real_components_of_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Fin r → ℝ) (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a).map (finPart D) = 1 ∧ ∀ τ, Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * X.map (tauE D τ) = X.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) ∧ Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Y.map (tauE D τ) = Y.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) ∧ ∀ z : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) *ᵥ z = 0 → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) *ᵥ z = 0 → Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *ᵥ (fun i => tauE D τ (z i)) = fun i => tauE D τ (z i) := by
  first | exact @GlobalTheory.TorusDict.torus_dict | exact GlobalTheory.TorusDict.torus_dict | (intros; apply GlobalTheory.TorusDict.torus_dict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementDualFrameRowsEigenInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementDualFrameRowsEigenInverse
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.torus_dual_frame_rows_eigen : ∀ (R : Type) [CommRing R] (m r : ℕ) (X Y : Matrix (Fin m) (Fin r) R) (X' Y' : Matrix (Fin r) (Fin m) R) (d e : Matrix (Fin r) (Fin r) R) (A B : Matrix (Fin m) (Fin m) R), X' * X = 0 → Y' * Y = 0 → X' * Y = 1 → Y' * X = 1 → d * e = 1 → e * d = 1 → A * X = X * d → A * Y = Y * e → A * (1 - X * Y' - Y * X') = 1 - X * Y' - Y * X' → A * B = 1 → Y' * B = e * Y' ∧ X' * B = d * X' ∧ (1 - X * Y' - Y * X') * B = 1 - X * Y' - Y * X' := by
  intro R _ m r X Y X' Y' d e A B hX'X hY'Y hX'Y hY'X hde hed hAX hAY hAP hAB
  obtain ⟨P, hP⟩ : ∃ P, P = 1 - X * Y' - Y * X' := ⟨_, rfl⟩
  rw [← hP] at hAP ⊢
  have hsum : X * Y' + Y * X' + P = 1 := by rw [hP]; abel
  have hY'P : Y' * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hY'X, hY'Y, Matrix.one_mul, Matrix.zero_mul, sub_self, zero_sub, neg_zero]
  have hX'P : X' * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hX'X, hX'Y, Matrix.one_mul, Matrix.zero_mul, sub_zero, sub_self]
  have hPX : P * X = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      hY'X, hX'X, Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
  have hPY : P * Y = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      hY'Y, hX'Y, Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  have hPP : P * P = P := by
    have h1 : P * P = P * (1 - X * Y' - Y * X') := by rw [← hP]
    rw [h1, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hPX, hPY, Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have hA : A = X * d * Y' + Y * e * X' + P := by
    calc A = A * (X * Y' + Y * X' + P) := by rw [hsum, Matrix.mul_one]
      _ = X * d * Y' + Y * e * X' + P := by
        rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY, hAP]
  have hY'A : Y' * A = d * Y' := by
    rw [hA, Matrix.mul_add, Matrix.mul_add, hY'P, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hY'X, hY'Y, Matrix.one_mul, Matrix.zero_mul,
      Matrix.zero_mul, add_zero, add_zero]
  have hX'A : X' * A = e * X' := by
    rw [hA, Matrix.mul_add, Matrix.mul_add, hX'P, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX'X, hX'Y, Matrix.one_mul, Matrix.zero_mul,
      Matrix.zero_mul, zero_add, add_zero]
  have hPA : P * A = P := by
    rw [hA, Matrix.mul_add, Matrix.mul_add, hPP, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPX, hPY, Matrix.zero_mul, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.zero_mul, zero_add, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · calc Y' * B = (e * d) * (Y' * B) := by rw [hed, Matrix.one_mul]
      _ = e * ((Y' * A) * B) := by rw [hY'A, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = e * Y' := by rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  · calc X' * B = (d * e) * (X' * B) := by rw [hde, Matrix.one_mul]
      _ = d * ((X' * A) * B) := by rw [hX'A, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = d * X' := by rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  · calc P * B = (P * A) * B := by rw [hPA]
      _ = P := by rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementDualFrameRowsEigenInverseStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusElement_dualFrameRows_eigen_inverse : ∀ (R : Type) [CommRing R] (m r : ℕ) (X Y : Matrix (Fin m) (Fin r) R) (X' Y' : Matrix (Fin r) (Fin m) R) (d e : Matrix (Fin r) (Fin r) R) (A B : Matrix (Fin m) (Fin m) R), X' * X = 0 → Y' * Y = 0 → X' * Y = 1 → Y' * X = 1 → d * e = 1 → e * d = 1 → A * X = X * d → A * Y = Y * e → A * (1 - X * Y' - Y * X') = 1 - X * Y' - Y * X' → A * B = 1 → Y' * B = e * Y' ∧ X' * B = d * X' ∧ (1 - X * Y' - Y * X') * B = 1 - X * Y' - Y * X' := by
  first | exact @GlobalTheory.torus_dual_frame_rows_eigen | exact GlobalTheory.torus_dual_frame_rows_eigen | (intros; apply GlobalTheory.torus_dual_frame_rows_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementInvFinitePartOneDualFrameEigen
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusInv

theorem dual_mul_compl {R : Type} [CommRing R] {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) R)
    (X' Y' : Matrix (Fin r) (Fin m) R) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1) :
    X' * (1 - X * Y' - Y * X') = 0 ∧ Y' * (1 - X * Y' - Y * X') = 0 := by
  constructor
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp

theorem mapped {E : Type} [CommRing E] (f : E →+* ℂ) {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) E)
    (X' Y' : Matrix (Fin r) (Fin m) E) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1)
    (t : Fin r → ℝ) (ht : ∀ i, 0 < t i) (A B : Matrix (Fin m) (Fin m) ℂ)
    (hX : A * X.map f = X.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)))
    (hY : A * Y.map f = Y.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹))
    (hz : ∀ z : Fin m → E, X' *ᵥ z = 0 → Y' *ᵥ z = 0 → A *ᵥ (fun i => f (z i)) = fun i => f (z i))
    (hAB : A * B = 1) :
    Y'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map f ∧
    X'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map f ∧
    (1 - X * Y' - Y * X').map f * B = (1 - X * Y' - Y * X').map f := by
  have hP : (1 - X * Y' - Y * X').map f = 1 - X.map f * Y'.map f - Y.map f * X'.map f := by
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_one _ (map_zero f) (map_one f)]
  obtain ⟨k1, k2⟩ := dual_mul_compl X Y X' Y' xx yy xy yx
  have hA : A * (1 - X * Y' - Y * X').map f = (1 - X * Y' - Y * X').map f := by
    ext i j
    have := hz (fun k => (1 - X * Y' - Y * X' : Matrix (Fin m) (Fin m) E) k j)
      (by funext a; exact congrFun (congrFun k1 a) j) (by funext a; exact congrFun (congrFun k2 a) j)
    exact congrFun this i
  have hne : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  rw [hP] at hA ⊢
  refine GlobalTheory.T.torusElement_dualFrameRows_eigen_inverse ℂ m r (X.map f) (Y.map f) (X'.map f) (Y'.map f) _ _ A B ?_ ?_ ?_ ?_ ?_ ?_ hX hY hA hAB
  · rw [← Matrix.map_mul, xx, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, yy, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, xy, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, yx, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hne i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hne i)

theorem torus_inv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 ∧ ∀ τ, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) ∧ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) ∧ (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) := by
  intro D θ hθ V r X Y hW t ht a ha
  obtain ⟨hf, hr⟩ := GlobalTheory.T.siegelTorusElement_real_components_of_frame D θ hθ V r X Y t a ha
  have h1 : Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹ = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨?_, fun τ => ?_⟩
  · have h2 := congrArg (fun M => Matrix.map M (finPart D)) h1
    rw [Matrix.map_mul, hf, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  · obtain ⟨hX, hY, hz⟩ := hr τ
    have hAB : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *
        Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = 1 := by
      have h3 : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹) =
          Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) :=
        Matrix.map_mul (f := (θ τ).comp (infPart D))
      rw [← h3, h1]
      exact Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))
    exact mapped (tauE D τ) X Y _ _ hW.xx hW.yy hW.xy (GlobalTheory.T.witt_frame_conjugate_gram_inv D V r X Y hW) t ht _ _ hX hY hz hAB

end GlobalTheory.TorusInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementInvFinitePartOneDualFrameEigenStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTorusElement_inv_finitePart_one_dualFrame_eigen : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 ∧ ∀ τ, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) ∧ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) ∧ (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) := by
  first | exact @GlobalTheory.TorusInv.torus_inv | exact GlobalTheory.TorusInv.torus_inv | (intros; apply GlobalTheory.TorusInv.torus_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsL
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ENNReal.ofReal (GlobalTheory.Unf.maj θ K N (GlobalTheory.SiegelFormula.invPt V a ξ)) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc K hK
  obtain ⟨L, hL, hden⟩ := GlobalTheory.T.exists_bounded_denominator_rational_matrices_in_box D V.rank n K hK
  obtain ⟨N, C, hC, hst⟩ := GlobalTheory.T.torusInverse_latticeCount_stacked_eigenprojections D V.rank n r X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) c hc L hL
  refine ⟨N, C, hC, fun t ht a ha => ?_⟩
  obtain ⟨hfin, hrel⟩ := GlobalTheory.T.siegelTorusElement_inv_finitePart_one_dualFrame_eigen D θ hθ V r X Y hXY t ht.1 a ha
  refine le_trans (ENNReal.tsum_le_tsum fun ξ => ?_)
    (hst t ht (fun τ => compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) hrel)
  have e : (GlobalTheory.SiegelFormula.invPt V a ξ : Matrix (Fin V.rank) (Fin n) (AE D)) =
      HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D) : Matrix (Fin V.rank) (Fin n) (AE D)) := rfl
  have hcomp : ∀ τ, compAt θ τ (GlobalTheory.SiegelFormula.invPt V a ξ) =
      compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) * ξ.map (tauE D τ) := by
    intro τ
    have h1 : compAt θ τ (ξ.map (incA D) : Mx D V.rank n) = ξ.map (tauE D τ) := by
      ext i j
      exact (hθ τ).1 (ξ i j)
    rw [e, ← h1]
    exact Matrix.map_mul (f := (θ τ).comp (infPart D))
  unfold GlobalTheory.Unf.maj
  split_ifs with hb
  · have hmem : ξ ∈ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E |
        ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} := by
      refine hden _ ξ ?_ hb
      rw [e, Matrix.map_mul, hfin, Matrix.one_mul]
    rw [Set.indicator_of_mem hmem]
    simp only [GlobalTheory.Unf.realSize, hcomp, le_refl]
  · simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsLStatement
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTorus_tsum_majorant_translatedRationalPoints_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ENNReal.ofReal (GlobalTheory.Unf.maj θ K N (GlobalTheory.SiegelFormula.invPt V a ξ)) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  first | exact @GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le | exact GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le | (intros; apply GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le <;> assumption)
end
