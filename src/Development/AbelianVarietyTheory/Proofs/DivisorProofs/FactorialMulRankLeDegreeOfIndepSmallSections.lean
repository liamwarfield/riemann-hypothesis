module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormBallFamilyPowLeEncardOfLinearIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormBallFamilyPowLeEncardOfLinearIndependent
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_pow_le_encard :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ)
      (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) →
      ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  classical
  intro G _ Λ B hB r Q R v hR hv hvB
  obtain ⟨hmono, -, hadd⟩ := isBallFam_mono_neg_add G Λ B hB
  let f : (Fin r → Fin Q) → G := fun c => ∑ j, ((c j : ℕ) • v j)

  have hterm : ∀ (n : ℕ) (j : Fin r), n • v j ∈ B (n * R) := by
    intro n j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hB.zero_mem 0 le_rfl
    · exact (hB.nsmul_iff n R (v j) hn (hB.subset R (hvB j))).2 (hvB j)
  have hsum : ∀ (c : Fin r → Fin Q) (s : Finset (Fin r)),
      ∑ j ∈ s, ((c j : ℕ) • v j) ∈ B (∑ j ∈ s, ((c j : ℕ) : ℝ) * R) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hB.zero_mem 0 le_rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact hadd _ _ _ _ (hterm _ a) ih
  have hmem : ∀ c, f c ∈ B (r * Q * R) := by
    intro c
    refine hmono _ _ ?_ (hsum c Finset.univ)
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hR
    calc (∑ j, ((c j : ℕ) : ℝ)) ≤ ∑ _j : Fin r, (Q : ℝ) :=
          Finset.sum_le_sum fun j _ => by exact_mod_cast (c j).isLt.le
      _ = r * Q := by simp
  have hinj : Function.Injective f := by
    intro c c' h
    have h0 : ∑ j, (((c j : ℕ) : ℤ) - ((c' j : ℕ) : ℤ)) • v j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
      exact sub_eq_zero.mpr h
    have := Fintype.linearIndependent_iff.1 hv _ h0
    funext j
    have hj := this j
    exact Fin.ext (by omega)
  have hsub : ((Finset.univ.image f : Finset G) : Set G) ⊆ B (r * Q * R) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨c, rfl⟩ := hx
    exact hmem c
  calc ((Q ^ r : ℕ) : ℕ∞) = ((Finset.univ.image f).card : ℕ∞) := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ = ((Finset.univ.image f : Finset G) : Set G).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (B (r * Q * R)).encard := Set.encard_le_encard hsub

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormBallFamilyPowLeEncardOfLinearIndependentStatement
open Filter Topology
open GlobalTheory GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seminormBallFamily_pow_le_encard_of_linearIndependent : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ) (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) → ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  first | exact @GlobalTheory.VolBr.isBallFam_pow_le_encard | exact GlobalTheory.VolBr.isBallFam_pow_le_encard | (intros; apply GlobalTheory.VolBr.isBallFam_pow_le_encard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeOfGrowthInRadius
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeOfGrowthInRadius
open Filter Topology

namespace GlobalTheory

theorem rank_le_of_growth_in_radius : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ →
    (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) →
    (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) →
      ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  intro D f α γ ρ t₀ t₁ hρ hlim hbd
  have hev : ∀ᶠ m : ℕ in atTop, ρ * (m : ℝ) ^ D * Real.exp (-(m : ℝ)) ≤ 1 := by
    have h1 : Tendsto (fun x : ℝ => x ^ D * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero D
    have h2 : Tendsto (fun m : ℕ => ρ * ((m : ℝ) ^ D * Real.exp (-(m : ℝ)))) atTop (𝓝 (ρ * 0)) :=
      (h1.comp tendsto_natCast_atTop_atTop).const_mul ρ
    rw [mul_zero] at h2
    filter_upwards [h2.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with m hm
    rw [mul_assoc]; exact hm.le
  have key : ∀ t, max t₀ (t₁ + 2) ≤ t → ρ * (t - t₁ - 2) ≤ α + γ * t := by
    intro t ht
    have ht0 : t₀ ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : t₁ + 2 ≤ t := le_trans (le_max_right _ _) ht
    refine ge_of_tendsto (hlim t ht0) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
    set x := Real.exp ((t - t₁ - 1) * m) with hx
    have hx2 : 2 ≤ x := by
      have : 1 ≤ (t - t₁ - 1) * m := by nlinarith
      have h := Real.add_one_le_exp ((t - t₁ - 1) * m)
      linarith
    set Q := ⌊x⌋₊ with hQ
    have hQle : (Q : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hQgt : x < Q + 1 := Nat.lt_floor_add_one x
    have hQpos : 0 < Q := by
      rw [hQ]; exact Nat.floor_pos.mpr (by linarith)
    have e2 : Real.exp (-(m:ℝ)) ≤ 1 / 2 := by
      have h := Real.add_one_le_exp (m:ℝ)
      have hp : Real.exp (-(m:ℝ)) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-(m:ℝ))]
    have hQge : Real.exp ((t - t₁ - 2) * m) ≤ Q := by
      have e1 : Real.exp ((t - t₁ - 2) * m) = x * Real.exp (-(m:ℝ)) := by
        rw [hx, ← Real.exp_add]; congr 1; ring
      rw [e1]
      have : x * Real.exp (-(m:ℝ)) ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left e2 (by linarith)
      linarith
    have e3 : x * Real.exp (t₁ * m) = Real.exp (-(m:ℝ)) * Real.exp (t * m) := by
      rw [hx, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hρm : 0 ≤ ρ * (m : ℝ) ^ D := mul_nonneg hρ (pow_nonneg hmpos.le _)
    have hcond : ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) := by
      calc ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m)
          ≤ ρ * (m : ℝ) ^ D * x * Real.exp (t₁ * m) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle hρm) (Real.exp_pos _).le
        _ = (ρ * (m : ℝ) ^ D * Real.exp (-(m:ℝ))) * Real.exp (t * m) := by
            rw [mul_assoc (ρ * (m : ℝ) ^ D) x, e3]; ring
        _ ≤ 1 * Real.exp (t * m) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = Real.exp (t * m) := one_mul _
    have hb := hbd t m Q (by omega) hQpos hcond
    have hlog : (t - t₁ - 2) * (m : ℝ) ≤ Real.log Q :=
      calc (t - t₁ - 2) * (m : ℝ) = Real.log (Real.exp ((t - t₁ - 2) * m)) := (Real.log_exp _).symm
        _ ≤ Real.log Q := Real.log_le_log (Real.exp_pos _) hQge
    rw [le_div_iff₀ (by positivity)]
    calc ρ * (t - t₁ - 2) * (m : ℝ) ^ (D + 1) = ρ * (m : ℝ) ^ D * ((t - t₁ - 2) * m) := by ring
      _ ≤ ρ * (m : ℝ) ^ D * Real.log Q := mul_le_mul_of_nonneg_left hlog hρm
      _ ≤ f t m := hb
  by_contra h
  push_neg at h
  have hd : 0 < ρ - γ := sub_pos.mpr h
  set T := max (max t₀ (t₁ + 2)) ((α + ρ * (t₁ + 2)) / (ρ - γ) + 1) with hTdef
  have hk := key T (le_max_left _ _)
  have hT : (α + ρ * (t₁ + 2)) / (ρ - γ) + 1 ≤ T := le_max_right _ _
  have hlt : (α + ρ * (t₁ + 2)) / (ρ - γ) < T := by linarith
  have h3 : α + ρ * (t₁ + 2) < T * (ρ - γ) := (div_lt_iff₀ hd).mp hlt
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeOfGrowthInRadiusStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_slope_of_tendsto_div_pow_of_log_lower_bound : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ → (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) → (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) → ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  first | exact @GlobalTheory.rank_le_of_growth_in_radius | exact GlobalTheory.rank_le_of_growth_in_radius | (intros; apply GlobalTheory.rank_le_of_growth_in_radius <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (M : HermLB p), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → ∀ (ρ : ℕ) (t₁ : ℝ), (∀ m : ℕ, 0 < m → ∃ v : Fin (ρ * m ^ D) → X.functionField, LinearIndependent ℤ v ∧ ∀ s, v s ∈ P.Bl (m * a) (m * b) (Real.exp (t₁ * m))) → (D.factorial : ℝ) * ρ ≤ gdeg M D := by
  intro hA hHS k _ X _ p D hX P a b M hRep hAmp hSemi ρ t₁ hv
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => M).1
  have hα : M.IsSelfInter (Φ (MvPolynomial.X PUnit.unit ^ (D + 1))) :=
    ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, hlim⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hHS k X p D hX P a b 0 0 M _ hRep hAmp hSemi hα
  have key := GlobalTheory.T.le_slope_of_tendsto_div_pow_of_log_lower_bound D (fun t m => P.lc (m * a) (m * b) (Real.exp (t * m)))
    (Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / ((D + 1).factorial : ℝ))
    (((D : ℝ) + 1) * gdeg M D / ((D + 1).factorial : ℝ)) ρ t₀ t₁ (Nat.cast_nonneg _) ?_ ?_
  · have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * (D.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
    have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [hf, mul_div_mul_left _ _ hD1.ne', le_div_iff₀ hD] at key
    linarith
  · intro t ht
    simpa using hlim t ht
  · intro t m Q hm hQ hle
    obtain ⟨v, hli, hvB⟩ := hv m hm
    have hB := GlobalTheory.VolBr.Pair.isBallFam k X p P (m * a) (m * b)
    have hcard := GlobalTheory.T.seminormBallFamily_pow_le_encard_of_linearIndependent _ _ _ hB (ρ * m ^ D) Q (Real.exp (t₁ * m)) v (Real.exp_pos _).le hli hvB
    have hsub : P.Bl (m * a) (m * b) (((ρ * m ^ D : ℕ) : ℝ) * Q * Real.exp (t₁ * m)) ⊆
        P.Bl (m * a) (m * b) (Real.exp (t * m)) :=
      (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ hB).1 _ _ (by push_cast; linarith)
    have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P (m * a) (m * b) (Real.exp (t * m))
    have h1 : ((Q ^ (ρ * m ^ D) : ℕ) : ℕ∞) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard :=
      hcard.trans (Set.encard_le_encard hsub)
    rw [← hfin.cast_ncard_eq] at h1
    have hn : Q ^ (ρ * m ^ D) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard := by exact_mod_cast h1
    show _ ≤ Real.log _
    have hQ' : (0 : ℝ) < ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by positivity
    calc (ρ : ℝ) * (m : ℝ) ^ D * Real.log Q = Real.log ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      _ ≤ Real.log ((P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard : ℝ) :=
          Real.log_le_log hQ' (by exact_mod_cast hn)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (M : HermLB p), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → ∀ (ρ : ℕ) (t₁ : ℝ), (∀ m : ℕ, 0 < m → ∃ v : Fin (ρ * m ^ D) → X.functionField, LinearIndependent ℤ v ∧ ∀ s, v s ∈ P.Bl (m * a) (m * b) (Real.exp (t₁ * m))) → (D.factorial : ℝ) * ρ ≤ gdeg M D := by
  first | exact @GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep | exact GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep | (intros; apply GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamCoefVal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.TorsionAnyChar

noncomputable section

namespace GlobalTheory.PeriodsAnyChar

end GlobalTheory.PeriodsAnyChar

open GlobalTheory.PeriodsAnyChar

namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

end GlobalTheory.UT.CoefVal

namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

end GlobalTheory.UT.CoefUnit

namespace GlobalTheory.UT.SmallPoint
open CoefBasic

end GlobalTheory.UT.SmallPoint

namespace GlobalTheory.UT.SmallZero
open CoefBasic SmallPoint

end GlobalTheory.UT.SmallZero

namespace GlobalTheory.UT.EvalZero
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

end GlobalTheory.UT.EvalZero

namespace GlobalTheory.UT.MixedConv
open GlobalTheory.FieldBaseChange

section Core
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

end Core

end GlobalTheory.UT.MixedConv

namespace GlobalTheory.UT

theorem _root_.GlobalTheory.PeriodsAnyChar.weilQkIs_iff_weilIs : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  intro hL R _ _ I _ D A G _ _ _ U F _ _ _ k hk p p' x x' hx hx' ζ
  have hG := hL.1.globalFns
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.1.kerPow _ A F _ k hk x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  obtain ⟨ρ, hρ, hcomm, -⟩ := thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG A.isAb A.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, Units.ext (by simp [unitOn])⟩
  let E : SecM A.A A.L (k : ℤ) (TFK (R := R) F) → Fam D.toPre F k := fun v => e (SecM.toSec A.A v)
  have hE : ∀ s, ∃ v, E v = s := fun s => ⟨SecM.ofSec A.A (e.symm s), e.apply_symm_apply s⟩
  have a : ∀ v, PhiRel D.toPre F k p w (E v) (E (ρ θ v)) := fun v =>
    h _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have a' : ∀ v, PhiRel D.toPre F k p' w' (E v) (E (ρ θ' v)) := fun v =>
    h' _ _ _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) ((hρ _ _ _).2 rfl)
  have b : ∀ v t, PhiRel D.toPre F k p w (E v) t → t = E (ρ θ v) := fun v t H =>
    phi_unique p w ((phiRel_iff hG p w hw _ _).1 H) ((phiRel_iff hG p w hw _ _).1 (a v))
  have b' : ∀ v t, PhiRel D.toPre F k p' w' (E v) t → t = E (ρ θ' v) := fun v t H =>
    phi_unique p' w' ((phiRel_iff hG p' w' hw' _ _).1 H) ((phiRel_iff hG p' w' hw' _ _).1 (a' v))
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' (z : F) (fun s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ => by
    obtain ⟨v, rfl⟩ := hE s
    obtain rfl := b' _ _ h₁
    obtain rfl := b _ _ h₂
    obtain rfl := b _ _ h₃
    obtain rfl := b' _ _ h₄
    rw [hcomm θ θ' _ hc v]
    exact e.map_smul (z : F) (SecM.toSec A.A (ρ θ' (ρ θ v)))) (by
    obtain ⟨B, hB, -⟩ := BoxSpan.exists_basis hL.1.secBaseChange A k hk F (jFK (R := R) F)
    have : Nontrivial Γ((TFK (R := R) F).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    have hne := hB.ne_zero ⟨0, pow_pos hk _⟩
    refine ⟨_, _, _, a (B ⟨0, pow_pos hk _⟩), a' _, fun h0 => hne ?_⟩
    have h1 : SecM.toSec A.A (ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩))) = _ := e.map_eq_zero_iff.1 h0
    have h2 : ρ θ' (ρ θ (B ⟨0, pow_pos hk _⟩)) = 0 := congrArg (SecM.ofSec A.A) h1
    exact (ρ θ).map_eq_zero_iff.1 ((ρ θ').map_eq_zero_iff.1 h2)) hk (ζ : F)
  have hz := GlobalLift.weilIs_of_commIsOf hG A.isAb A.isLB hc
  rw [key]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective (CommutatorPairing.weilIs_unique hG A.isAb A.isLB H hz))

end GlobalTheory.UT

namespace GlobalTheory.TorsionIso

theorem _root_.GlobalTheory.PeriodsAnyChar.torsion_map : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧ ((k : F) ≠ 0 → ∀ x, x ^ k = 1 → ∃ p, f p = x) ∧ (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧ ∀ p p' (z : Fˣ), WeilQkIs D.toPre F k p p' z ↔ WeilIs A.A A.L k (f p) (f p') (unitOn z) := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k hk
  have hqk := indAtTransl_any hL R I hI D A G hG U F k hk
  have hcomp := indAtComp_any hL R I hI D A G hG U F k hk
  have huniq := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hinj := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hex : ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U.toUnifPre F k p x := fun p => by
    obtain ⟨x, hx⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
    exact ⟨x, (hqk p x).1 (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩
  choose f hf using hex
  have hwd : ∀ p p', QkPt.Equiv D.toPre F p p' → f p = f p' := fun p p' h =>
    huniq p' _ _ ((hqk _ _).1 ((hcomp p p' p' _ (𝟙 _) ((hqk _ _).2 (hf p))).2.1 h)) (hf p')
  have hpow : ∀ p, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.ext
    exact (hf p w hw).1
  refine ⟨f, fun p x => ⟨fun h => huniq p _ _ h (hf p), fun h => h ▸ hf p⟩, ?_,
    fun p p' => ⟨fun h => hinj p p' (f p) (hf p) (h ▸ hf p'), hwd p p'⟩, ?_,
    fun p p' z => GlobalTheory.PeriodsAnyChar.weilQkIs_iff_weilIs hL R I hI D A G hG U F k hk p p' _ _ (hf p) (hf p') z⟩
  · intro hkF x hx
    obtain ⟨p, hp⟩ := exists_qkToAkU R I hI D A G hG U F k hkF x hx
    exact ⟨p, huniq p _ _ (hf p) hp⟩
  · intro p p' p'' h
    have := (hcomp p p' p'' _ _ ((hqk _ _).2 (hf p))).1 ((hqk _ _).2 (hf p')) h
    rw [translT_comp] at this
    exact huniq p'' _ _ (hf p'') ((hqk _ _).1 this)

end GlobalTheory.TorsionIso

namespace GlobalTheory.LevelCompat
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem _root_.GlobalTheory.PeriodsAnyChar.qkToAkU_level : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n → N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, (q.y = n • p.y → q.g = p.g → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F N q x)) ∧ (p.y = q.y → GtPtF.IsNsmul n q.g p.g → QkToAkU U.toUnifPre F N q x → QkToAkU U.toUnifPre F k p (x ^ n)) := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨f, hf, -⟩ := GlobalTheory.PeriodsAnyChar.torsion_map hL R I hI D A G hG U F k hk
  obtain ⟨f', hf', -, -, hadd, -⟩ := GlobalTheory.PeriodsAnyChar.torsion_map hL R I hI D A G hG U F N hN1
  have key : ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → f p = f' q := by
    intro p q hy hg
    obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
    have a := (indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1
      (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
    have b := (indAtTransl_any hL R I hI D A G hG U F N hN1 q x₀).1 (h₀ n N hn hN q hy hg)
    exact ((hf p x₀).1 a).symm.trans ((hf' q x₀).1 b)
  intro p q x
  refine ⟨fun hy hg => by rw [hf, hf', key p q hy hg], fun hy hg hx => ?_⟩
  have hx' : x = f' q := (hf' q x).1 hx
  have hp : ∀ j : ℕ, f' (qkNsmul D.tau_bimult (j + 1) q) = x ^ (j + 1) := by
    intro j
    induction j with
    | zero => rw [Nat.zero_add, qkNsmul_one, pow_one, hx']
    | succ j ih => rw [hadd _ _ _ (qkAdd_qkNsmul D.tau_bimult (j + 1) q), ih, ← hx', ← pow_succ]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [hf, ← hp j]
  exact (key p _ (by rw [hy]; rfl) ((isNsmul_iff_eq _ _ _).1 hg).symm).symm

end GlobalTheory.LevelCompat

namespace GlobalTheory.UT.EndTors
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic
attribute [local instance] gtGroup

end GlobalTheory.UT.EndTors

namespace GlobalTheory.UT.EndBaseChange
open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.UT.EndBaseChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QLevelRescale
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qkPt_rescale : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  intro o Ω _ _ _ S ρ p _ y₀ u k k' d pk x hk hd hk' hx
  have hA : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  have e : k' • pk.g = iota hB (PadicAlgCl p) (d • pk.y) := by
    rw [hk', ← smul_smul, qk_nsmul hB, map_nsmul]
  refine ⟨qkMk hB (d • pk.y) pk.g e, rfl, ?_⟩
  have L := GlobalTheory.PeriodsAnyChar.qkToAkU_level GlobalTheory.firstFiveLaws u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p)
    k d k' hk hd (by rw [hk', Nat.mul_comm]) pk (qkMk hB (d • pk.y) pk.g e) x
  exact (L.1 rfl rfl).1 hx

end GlobalTheory.QLevelRescale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  first | exact @GlobalTheory.QLevelRescale.exists_qkPt_rescale | exact GlobalTheory.QLevelRescale.exists_qkPt_rescale | (intros; apply GlobalTheory.QLevelRescale.exists_qkPt_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopDensityEqPolarisedTopChern
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffChernPolyEqPolarised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffProdOneOneForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffProdOneOneForms
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

open GlobalTheory.GoodMetric.LinSubst

theorem sum_det_rowSel_mul {n : ℕ} (F : (Fin n → Fin n) → ℂ) :
    ∑ c : Fin n → Fin n, (rowSel c).det * F c =
      ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * F u := by
  classical
  symm
  refine Finset.sum_of_injOn (fun u : Equiv.Perm (Fin n) => (u : Fin n → Fin n))
    (fun u _ v _ h => DFunLike.coe_injective h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro c _ hc
    rw [det_rowSel_of_not_injective, zero_mul]
    intro hinj
    exact hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  · intro u _
    rw [det_rowSel_perm]

theorem topCoeff_prod_forms {n : ℕ} (k : Fin n → Fin n → Fin n → ℂ) :
    topCoeff (∏ i, ∑ a, ∑ b, MvPolynomial.C (k i a b) * MvPolynomial.X (a, b)) =
      ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i b => k i (u i) b).det := by
  classical
  rw [← sum_det_rowSel_mul (fun c => (Matrix.of fun i b => k i (c i) b).det)]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum,
    ← sum_prod_mul_det_rowSel (Matrix.of fun i b => k i (c i) b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, topCoeff_prod_X_pair]
  simp only [Matrix.of_apply]
  ring

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffProdOneOneFormsStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_oneOneForms : ∀ {n : ℕ} (k : Fin n → Fin n → Fin n → ℂ), topCoeff (∏ i, ∑ a, ∑ b, MvPolynomial.C (k i a b) * MvPolynomial.X (a, b)) = ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i b => k i (u i) b).det := by
  first | exact @GlobalTheory.GoodTop.topCoeff_prod_forms | exact GlobalTheory.GoodTop.topCoeff_prod_forms | (intros; apply GlobalTheory.GoodTop.topCoeff_prod_forms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCoeffCharpolyRevNegEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCoeffCharpolyRevNegEqSum
open Polynomial Matrix

namespace GlobalTheory.GoodTop

theorem sum_det_submatrix_image_eq {A : Type} [CommRing A] {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) (n : ℕ) (s : Finset r) (hs : s.card = n) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n → r => Finset.univ.image p = s),
      (M.submatrix p p).det =
    (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
  classical
  have hc : Fintype.card (Fin n) = Fintype.card s := by simp [hs]
  have h1 : ∑ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
      (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
    have : ∀ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
        (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
      intro e
      rw [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_fin]
  rw [← h1]
  symm
  refine Finset.sum_bij (fun e _ => Subtype.val ∘ e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  · intro e _ e' _ h
    ext i
    exact congrFun h i
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let f : Fin n → s := fun i => ⟨p i, hp ▸ Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [← hp] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨a, rfl⟩
    have hb : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hc⟩
    exact ⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩

theorem factorial_mul_coeff_charpolyRev_neg {A : Type} [CommRing A] {r : Type} [Fintype r]
    [DecidableEq r] (M : Matrix r r A) (n : ℕ) :
    (n.factorial : A) * (Matrix.charpolyRev (-M)).coeff n =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) := by
  classical
  have hrev : (-M).charpolyRev = det (1 + (X : A[X]) • M.map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) M, smul_neg, neg_neg]
  have hdet : ∀ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) = (M.submatrix p p).det := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hrev, coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]
  simp only [hdet]
  rw [← Finset.sum_filter_of_ne (s := Finset.univ)
    (p := fun p : Fin n → r => Finset.univ.image p ∈ (Finset.univ : Finset r).powersetCard n)]
  · rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset r).powersetCard n)
      (g := fun p : Fin n → r => Finset.univ.image p) (fun p hp => (Finset.mem_filter.mp hp).2)]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← sum_det_submatrix_image_eq M n s (Finset.mem_powersetCard.mp hs).2]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hs, h⟩, fun h => h.2⟩
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      exact hp (Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]))
    rw [Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]
    simp

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCoeffCharpolyRevNegEqSumStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_mul_coeff_charpolyRev_neg_eq_sum : ∀ {A : Type} [CommRing A] {r : Type} [Fintype r] [DecidableEq r] (M : Matrix r r A) (n : ℕ), (n.factorial : A) * (Matrix.charpolyRev (-M)).coeff n = ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) := by
  first | exact @GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg | exact GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg | (intros; apply GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffChernPolyEqPolarised
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem topCoeff_finsum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, MvPolynomial.coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem topCoeff_const_mul {n : ℕ} (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (MvPolynomial.C a * P) = a * topCoeff P := by
  simp only [topCoeff, MvPolynomial.coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem topCoeff_chernPoly_eq_mixTop : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    topCoeff (chernPoly G v n) = mixTop fun _ => curvAt G v := by
  intro n r _ _ G v
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have key := GlobalTheory.T.factorial_mul_coeff_charpolyRev_neg_eq_sum (curvPoly G v) n
  have h1 : (n.factorial : ℂ) * topCoeff (chernPoly G v n) =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
          (Matrix.of fun i b => curvAt G v (u i) b (p i) (p (π i))).det := by
    rw [← topCoeff_const_mul, map_natCast, chernPoly, key, topCoeff_finsum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [topCoeff_finsum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ), topCoeff_const_mul]
    have hp : (∏ i, curvPoly G v (p i) (p (π i))) = ∏ i, ∑ a, ∑ b,
        MvPolynomial.C (curv G v (coordVec a) (coordVec b) (p i) (p (π i))) * MvPolynomial.X (a, b) := by
      simp [curvPoly]
    rw [hp, GlobalTheory.T.topDegreeFormCoeff_prod_oneOneForms, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [curvAt, mul_assoc]
  rw [mixTop, ← h1, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffChernPolyEqPolarisedStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_polarised : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), topCoeff (chernPoly G v n) = mixTop fun _ => curvAt G v := by
  first | exact @GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop | exact GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop | (intros; apply GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopDensityEqPolarisedTopChern
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem chernTop_eq_mixTop {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n) :
    chernTop (MvPolynomial.X ((), n)) G v =
      (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  rw [chernTop, MvPolynomial.aeval_X, GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_polarised]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopDensityEqPolarisedTopChernStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopDensity_eq_polarisedTopChern : ∀ {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n), chernTop (MvPolynomial.X ((), n)) G v = (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  first | exact @GlobalTheory.GoodTop.chernTop_eq_mixTop | exact GlobalTheory.GoodTop.chernTop_eq_mixTop | (intros; apply GlobalTheory.GoodTop.chernTop_eq_mixTop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryW
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryW
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

theorem ptVia_spOver (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E E' : Type} [CommRing E] [Algebra R' E]
    [CommRing E'] [Algebra R' E'] (φ : E →ₐ[R'] E') (y : Pt X' E) :
    ptVia w (spOver φ ≫ y) =
      @spOver R _ E E' _ (algVia σ E) _ (algVia σ E') (homVia σ φ) ≫ ptVia w y := by
  apply Over.OverMorphism.ext
  change (spMap (φ : E →+* E') ≫ y.left) ≫ q = spMap (φ : E →+* E') ≫ (y.left ≫ q)
  exact Category.assoc _ _ _

theorem bcPull_coc_cob (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) :
    (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧
      ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  constructor
  · intro h
    unfold IsCoc at h ⊢
    intro E _ _ E' _ _ E'' _ _ φ ψ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    let _ : Algebra R E'' := algVia σ E''
    have hc : (homVia σ ψ).comp (homVia σ φ) = homVia σ (ψ.comp φ) := AlgHom.ext fun _ ↦ rfl
    simp only [bcPull, ptVia_spOver, ← hc]
    exact h E E' E'' (homVia σ φ) (homVia σ ψ) (ptVia w y) (sm_whole _)
  · rintro ⟨k, hk⟩
    refine ⟨fun E _ _ y ↦ @k E _ (algVia σ E) (ptVia w y), ?_⟩
    unfold IsCob at hk ⊢
    intro E _ _ E' _ _ φ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    simp only [bcPull, ptVia_spOver]
    exact hk E E' (homVia σ φ) (ptVia w y) (sm_whole _)

theorem bcPull_keeps : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) :=
  fun _ _ _ _ _ _ _ _ w u ↦ bcPull_coc_cob w u

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryWStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointCochainPullbackBaseChange_cocycle_coboundary_whole : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  first | exact @GlobalTheory.PtExt.bcPull_keeps | exact GlobalTheory.PtExt.bcPull_keeps | (intros; apply GlobalTheory.PtExt.bcPull_keeps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycle
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.PolRoot

private theorem gm_charPullTop {X T : Scheme.{0}} (r : T ⟶ X) (t : T) (a : Γ(X, ⊤)ˣ) :
    gm (𝟙 T) t ⊤ (GlobalTheory.CharKer.pullTop r a) = gm r t ⊤ a :=
  (gm_pull (𝟙 T) r t ⊤ trivial a).trans (by rw [Category.id_comp])

theorem defect_tri {X Y T : Scheme.{0}} {f : X ⟶ Y} {M : LB X} {φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ}
    {D : Γ(Triple f, ⊤)ˣ} (h : Defect f M φ D) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f)
    (t : T) (i j k : M.ι) (hi : a t ∈ M.U i) (hj : b t ∈ M.U j) (hk : c t ∈ M.U k) :
    gm (tri f a b c h₁ h₂) t ⊤ D * gm (pullback.lift a c (h₁.trans h₂)) t _ (φ i k) =
      gm (pullback.lift a b h₁) t _ (φ i j) * gm (pullback.lift b c h₂) t _ (φ j k) := by
  have e₁ : tri f a b c h₁ h₂ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) = pullback.lift a b h₁ :=
    pullback.lift_fst _ _ _
  have e₂ : tri f a b c h₁ h₂ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) = pullback.lift b c h₂ :=
    pullback.lift_snd _ _ _
  have e₃ : tri f a b c h₁ h₂ ≫ pr13 f = pullback.lift a c (h₁.trans h₂) := by
    apply pullback.hom_ext
    · rw [pr13, Category.assoc, pullback.lift_fst, reassoc_of% e₁, pullback.lift_fst]
      try rw [pullback.lift_fst]
    · rw [pr13, Category.assoc, pullback.lift_snd, reassoc_of% e₂, pullback.lift_snd]
      try rw [pullback.lift_snd]
  have := h T (tri f a b c h₁ h₂) t i j k
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_fst]; exact hi)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_snd]; exact hj)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₂, pullback.lift_snd]; exact hk)
  rwa [e₁, e₂, e₃] at this

theorem triCocycle_of_defect : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  intro X Y f M hM φ D h T a b c d h₁ h₂ h₃
  refine unit_ext fun t _ => ?_
  obtain ⟨i, hi⟩ := exists_chart hM (a t)
  obtain ⟨j, hj⟩ := exists_chart hM (b t)
  obtain ⟨k, hk⟩ := exists_chart hM (c t)
  obtain ⟨l, hl⟩ := exists_chart hM (d t)
  have e₁ := defect_tri h a b c h₁ h₂ t i j k hi hj hk
  have e₂ := defect_tri h a c d (h₁.trans h₂) h₃ t i k l hi hk hl
  have e₃ := defect_tri h b c d h₂ h₃ t j k l hj hk hl
  have e₄ := defect_tri h a b d h₁ (h₂.trans h₃) t i j l hi hj hl
  rw [map_mul, map_mul, gm_charPullTop, gm_charPullTop, gm_charPullTop, gm_charPullTop]
  apply mul_right_cancel (b := gm (pullback.lift a d ((h₁.trans h₂).trans h₃)) t _ (φ i l))
  rw [_root_.mul_assoc, _root_.mul_assoc, e₂, e₄, ← _root_.mul_assoc, e₁, _root_.mul_left_comm, e₃, _root_.mul_assoc]

end GlobalTheory.PolRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentCocycleDefect_isTripleCocycle : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  first | exact @GlobalTheory.PolRoot.triCocycle_of_defect | exact GlobalTheory.PolRoot.triCocycle_of_defect | (intros; apply GlobalTheory.PolRoot.triCocycle_of_defect <;> assumption)
end
end
