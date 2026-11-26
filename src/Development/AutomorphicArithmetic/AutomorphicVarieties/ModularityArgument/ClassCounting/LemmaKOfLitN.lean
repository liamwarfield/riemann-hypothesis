module

public import Development.EtaleCohomology.CyclotomicDiscriminants.FinSRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.STrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SThetaOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.PiRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.ExistsOfInLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.BlkEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CGtNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SUpperOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.RingEquivalences.OrderOfOneAddPrimePowZmodPrimePow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.JointWinOfCounts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PropZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardQuotPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.MainCotSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CountQuadraticOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfCmEigensystemCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfRatEigensystemCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OneCharOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CountVOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Number
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ConductorAtMapInjectiveCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LemmaX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ResidualBernoulliNonvanishing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnitaryLiftTheoremOfReducedForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Xpp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoHostVanE

@[expose] public section

section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.FinSFewOf
namespace LateralTheory.Fin.SFewOf
theorem few_of_statement_holds : UpperTheory.V.ZK.SFewOf := by
  apply LateralTheory.Q.SFewOfCut.sFewOf
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SFewOf := few_of_statement_holds
end LateralTheory.Fin.SFewOf
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SClassOf
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.sClassOf :
    UpperTheory.V.ZK.SClassOf :=
  cJoin cChain cFree cTriv UpperTheory.V.ZK.Cl.cAct cSplit cSupp cLatLoc cMu cInt cVal cGtNe cGtEq cBetaDiv cBetaVal cRep cUnit
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.NumThree
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

private theorem num_three (C u Y t : ℝ) (hu : 2 ≤ u) (hY : 1 / 2 ≤ Y) (P : ℝ) (hP : P ≤ u ^ 9 * Y)
    (ht : t ≤ 2 * Real.exp (u ^ C * Y) + P) : t ≤ Real.exp (u ^ (max C 9 + 2) * Y) := by
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  have hY0 : (0:ℝ) < Y := by linarith
  have hA1 : u ^ C ≤ u ^ (max C 9) := Real.rpow_le_rpow_of_exponent_le hu1 (le_max_left _ _)
  have hA2 : u ^ (9:ℕ) ≤ u ^ (max C 9) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by push_cast; exact le_max_right _ _)
  have h2 : u ^ (max C 9 + 2) = u ^ (max C 9) * u ^ (2:ℕ) := by
    rw [Real.rpow_add hu0, Real.rpow_two]
  have hu9 : (256:ℝ) ≤ u ^ (9:ℕ) := by
    calc (256:ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ u ^ 9 := pow_le_pow_left₀ (by norm_num) hu 9
  have hAC : u ^ C * Y ≤ u ^ (max C 9) * Y := mul_le_mul_of_nonneg_right hA1 hY0.le
  have hPA : P ≤ u ^ (max C 9) * Y := le_trans hP (mul_le_mul_of_nonneg_right hA2 hY0.le)
  have hA9 : u ^ (9:ℕ) * Y ≤ u ^ (max C 9) * Y := mul_le_mul_of_nonneg_right hA2 hY0.le
  have hApos : 1 ≤ u ^ (max C 9) * Y := by nlinarith
  have hu2 : (4:ℝ) ≤ u ^ (2:ℕ) := by nlinarith
  have h4A : 4 * (u ^ (max C 9) * Y) ≤ u ^ (max C 9 + 2) * Y := by
    rw [h2]
    have : u ^ (max C 9) * u ^ (2:ℕ) * Y = u ^ (2:ℕ) * (u ^ (max C 9) * Y) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hu2 (by linarith)
  have e1 : Real.exp (u ^ C * Y) ≤ Real.exp (u ^ (max C 9) * Y) := Real.exp_le_exp.mpr hAC
  have e3 : 3 * (u ^ (max C 9) * Y) + 1 ≤ Real.exp (3 * (u ^ (max C 9) * Y)) := by
    have := Real.add_one_le_exp (3 * (u ^ (max C 9) * Y))
    linarith
  have e4 : Real.exp (4 * (u ^ (max C 9) * Y)) =
      Real.exp (u ^ (max C 9) * Y) * Real.exp (3 * (u ^ (max C 9) * Y)) := by
    rw [← Real.exp_add]
    ring_nf
  have eA := Real.add_one_le_exp (u ^ (max C 9) * Y)
  have ep := Real.exp_pos (u ^ (max C 9) * Y)
  have e5 : Real.exp (u ^ (max C 9) * Y) * (3 * (u ^ (max C 9) * Y) + 1) ≤
      Real.exp (u ^ (max C 9) * Y) * Real.exp (3 * (u ^ (max C 9) * Y)) :=
    mul_le_mul_of_nonneg_left e3 ep.le
  calc t ≤ 2 * Real.exp (u ^ (max C 9) * Y) + u ^ (max C 9) * Y := by linarith
    _ ≤ Real.exp (4 * (u ^ (max C 9) * Y)) := by rw [e4]; nlinarith
    _ ≤ Real.exp (u ^ (max C 9 + 2) * Y) := Real.exp_le_exp.mpr h4A

private theorem num_poly (u Y t b g c v : ℝ) (hu : 2 ≤ u) (hY : 1 / 2 ≤ Y) (ht : t ≤ u)
    (hb0 : 0 ≤ b) (hb : b ≤ u + 2 * u ^ 2) (hg0 : 0 ≤ g) (hg : g ≤ u + 2 * u * Y + 2) (hc0 : 0 ≤ c) (hc : c ≤ u)
    (hv0 : 0 ≤ v) (hv : v ≤ u) : ((b + v) * g + c + v) * t ≤ u ^ 9 * Y := by
  have hu0 : (0:ℝ) ≤ u := by linarith
  have hY0 : (0:ℝ) < Y := by linarith
  have huY : 1 ≤ u * Y := by nlinarith
  have hu2 : 2 * u ≤ u ^ 2 := by nlinarith
  have hbv : b + v ≤ 3 * u ^ 2 := by nlinarith
  have hg' : g ≤ 6 * (u * Y) := by nlinarith
  have h1 : (b + v) * g ≤ 3 * u ^ 2 * (6 * (u * Y)) :=
    mul_le_mul hbv hg' hg0 (by positivity)
  have h4 : (4:ℝ) ≤ u ^ 2 := by nlinarith
  have h4' : 4 * (u * Y) ≤ u ^ 2 * (u * Y) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have hcv : c + v ≤ 4 * (u * Y) := by nlinarith
  have hS0 : 0 ≤ (b + v) * g + c + v := by positivity
  have hsum : (b + v) * g + c + v ≤ 19 * (u ^ 3 * Y) := by nlinarith
  have hst : ((b + v) * g + c + v) * t ≤ ((b + v) * g + c + v) * u :=
    mul_le_mul_of_nonneg_left ht hS0
  have hsu : ((b + v) * g + c + v) * u ≤ 19 * (u ^ 3 * Y) * u :=
    mul_le_mul_of_nonneg_right hsum hu0
  have h5 : (32:ℝ) ≤ u ^ 5 := by
    calc (32:ℝ) = 2 ^ 5 := by norm_num
      _ ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu 5
  have h4Y : 0 ≤ u ^ 4 * Y := by positivity
  have hfin : 19 * (u ^ 3 * Y) * u ≤ u ^ 9 * Y := by
    have e : 19 * (u ^ 3 * Y) * u = 19 * (u ^ 4 * Y) := by ring
    have e' : u ^ 9 * Y = u ^ 5 * (u ^ 4 * Y) := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_right (by linarith) h4Y
  linarith

set_option maxHeartbeats 800000 in
private theorem num_down (C : ℝ) (hC : 0 ≤ C) (E n D n' D' d w : ℕ) (hE : 1 ≤ E) (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hD' : 1 ≤ D') (h1 : n' = d * n) (hn' : 1 ≤ n') (h2 : d ≤ (n + 1) * (4 * E + 4)) (hw : w ≤ 2 * n')
    (h3 : D' ≤ D ^ d * w ^ n') : kBound C E n' D' ≤ kBound (5 * C + 11) E n D := by
  have hw1 : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h
      rw [zero_pow (by omega), mul_zero] at h3
      omega
    · exact h
  unfold kBound
  apply Real.exp_le_exp.mpr
  have hE' : (1:ℝ) ≤ E := by exact_mod_cast hE
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hD'1 : (1:ℝ) ≤ D' := by exact_mod_cast hD'
  have hn'1 : (1:ℝ) ≤ n' := by exact_mod_cast hn'
  have hw1R : (1:ℝ) ≤ w := by exact_mod_cast hw1
  have h1R : (n':ℝ) = d * n := by exact_mod_cast h1
  have h2R : (d:ℝ) ≤ (n + 1) * (4 * E + 4) := by exact_mod_cast h2
  have hwR : (w:ℝ) ≤ 2 * n' := by exact_mod_cast hw
  have h3R : (D':ℝ) ≤ D ^ d * w ^ n' := by exact_mod_cast h3
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hd16 : (d:ℝ) ≤ 16 * E * n := by
    have : ((n:ℝ) + 1) * (4 * E + 4) ≤ (2 * n) * (8 * E) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    nlinarith
  have hn'16 : (n':ℝ) ≤ 16 * E * n ^ 2 := by
    rw [h1R]
    have := mul_le_mul_of_nonneg_right hd16 (by linarith : (0:ℝ) ≤ n)
    nlinarith
  set x : ℝ := 2 * E * n with hx
  have hx2 : 2 ≤ x := by nlinarith
  have hx0 : 0 < x := by linarith
  have hEn : (E:ℝ) * n ^ 2 ≤ E ^ 2 * n ^ 2 := by
    have : (E:ℝ) ≤ E ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hn'x : (n':ℝ) ≤ 4 * x ^ 2 := by
    have : x ^ 2 = 4 * E ^ 2 * n ^ 2 := by rw [hx]; ring
    nlinarith
  have hd8 : (d:ℝ) ≤ 8 * x := by rw [hx]; linarith
  have hx3 : 8 ≤ x ^ 3 := by nlinarith
  have hbase : 2 * (E:ℝ) * n' ≤ x ^ 5 := by
    have a1 : 2 * (E:ℝ) * n' ≤ 2 * E * (16 * E * n ^ 2) :=
      mul_le_mul_of_nonneg_left hn'16 (by positivity)
    have a2 : 2 * (E:ℝ) * (16 * E * n ^ 2) = 8 * x ^ 2 := by rw [hx]; ring
    have a3 : 8 * x ^ 2 ≤ x ^ 3 * x ^ 2 := mul_le_mul_of_nonneg_right hx3 (by positivity)
    have a4 : x ^ 3 * x ^ 2 = x ^ 5 := by ring
    linarith
  have hbase0 : (0:ℝ) ≤ 2 * E * n' := by positivity
  have hpowC : (2 * (E:ℝ) * n') ^ C ≤ (x ^ 5) ^ C := Real.rpow_le_rpow hbase0 hbase hC
  have hx5C : (x ^ 5) ^ C = x ^ (5 * C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hxadd : x ^ (5 * C + 11) = x ^ (5 * C) * x ^ (11:ℕ) := by
    rw [Real.rpow_add hx0, ← Real.rpow_natCast]
    norm_num
  have hL2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLD : Real.log 2 ≤ Real.log (2 * (D:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hlogD : Real.log D ≤ Real.log (2 * (D:ℝ)) := Real.log_le_log (by linarith) (by linarith)
  have hlogD0 : 0 ≤ Real.log (D:ℝ) := Real.log_nonneg hD1
  have hlogw0 : 0 ≤ Real.log (w:ℝ) := Real.log_nonneg hw1R
  have hlogw : Real.log (w:ℝ) ≤ 8 * x ^ 2 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < w)
    linarith
  have hlogD' : Real.log (2 * (D':ℝ)) ≤ Real.log 2 + d * Real.log D + n' * Real.log w := by
    have hDd : (0:ℝ) < (D:ℝ) ^ d := pow_pos (by linarith) _
    have hwn : (0:ℝ) < (w:ℝ) ^ n' := pow_pos (by linarith) _
    calc Real.log (2 * (D':ℝ)) ≤ Real.log (2 * ((D:ℝ) ^ d * (w:ℝ) ^ n')) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + d * Real.log D + n' * Real.log w := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hDd.ne' hwn.ne',
            Real.log_pow, Real.log_pow]
          ring
  have hlogD'0 : 0 ≤ Real.log (2 * (D':ℝ)) := Real.log_nonneg (by linarith)
  set LD := Real.log (2 * (D:ℝ)) with hLDdef
  have t1 : (d:ℝ) * Real.log D ≤ 8 * x * LD :=
    mul_le_mul hd8 hlogD hlogD0 (by positivity)
  have t2 : (n':ℝ) * Real.log w ≤ 4 * x ^ 2 * (8 * x ^ 2) :=
    mul_le_mul hn'x hlogw hlogw0 (by positivity)
  have t2' : 4 * x ^ 2 * (8 * x ^ 2) = 32 * x ^ 4 := by ring
  have hLD1 : 1 ≤ 2 * LD := by linarith
  have hx40 : 0 ≤ 32 * x ^ 4 := by positivity
  have t3 : 32 * x ^ 4 * 1 ≤ 32 * x ^ 4 * (2 * LD) := mul_le_mul_of_nonneg_left hLD1 hx40
  have hx4 : 1 ≤ x ^ 4 := by nlinarith
  have hxx4 : x ≤ x ^ 4 := by nlinarith
  have hx7 : 128 ≤ x ^ 7 := by
    calc (128:ℝ) = 2 ^ 7 := by norm_num
      _ ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx2 7
  have hLD0 : 0 ≤ LD := by linarith
  have s1 : 1 * LD ≤ x ^ 4 * LD := mul_le_mul_of_nonneg_right hx4 hLD0
  have s2 : x * LD ≤ x ^ 4 * LD := mul_le_mul_of_nonneg_right hxx4 hLD0
  have tsum : Real.log (2 * (D':ℝ)) ≤ 73 * (x ^ 4 * LD) := by
    have e1 : 8 * x * LD = 8 * (x * LD) := by ring
    have e2 : 32 * x ^ 4 * (2 * LD) = 64 * (x ^ 4 * LD) := by ring
    linarith
  have tfin : Real.log (2 * (D':ℝ)) ≤ x ^ (11:ℕ) * LD := by
    have e : x ^ (11:ℕ) * LD = x ^ 7 * (x ^ 4 * LD) := by ring
    have h0 : 0 ≤ x ^ 4 * LD := by positivity
    have : 73 * (x ^ 4 * LD) ≤ x ^ 7 * (x ^ 4 * LD) :=
      mul_le_mul_of_nonneg_right (by linarith) h0
    rw [e]
    linarith
  rw [hxadd, ← hx5C]
  calc (2 * (E:ℝ) * n') ^ C * Real.log (2 * (D':ℝ)) ≤ (x ^ 5) ^ C * (x ^ (11:ℕ) * LD) :=
        mul_le_mul hpowC tfin hlogD'0 (by positivity)
    _ = (x ^ 5) ^ C * x ^ (11:ℕ) * LD := by ring

private theorem gens_le (L : Type) [Field L] [NumberField L] :
    (gens L : ℝ) ≤ 2 * (Module.finrank ℚ L : ℝ) +
      2 * (2 * (Module.finrank ℚ L : ℝ)) * Real.log (2 * ((discr L).natAbs : ℝ)) + 2 := by
  have key := K.numGens 2 L (classNumber L) (by apply Nat.le_mul_of_pos_right; positivity)
  have key0 := K.numGens 2 L 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, Real.log_zero, Nat.cast_ofNat] at key key0
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnD : 0 ≤ 4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) := by
    nlinarith
  have hk : (Nat.log 2 (classNumber L) : ℝ) ≤
      4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) := by
    rcases Nat.eq_zero_or_pos (classNumber L) with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero]
      exact hnD
    · have hp : 2 ^ Nat.log 2 (classNumber L) ≤ classNumber L := Nat.pow_log_le_self 2 hpos.ne'
      have hpR : (2:ℝ) ^ Nat.log 2 (classNumber L) ≤ (classNumber L : ℝ) := by exact_mod_cast hp
      have hlog : (Nat.log 2 (classNumber L) : ℝ) * Real.log 2 ≤ Real.log (classNumber L) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hpR
      nlinarith
  show ((2 * Module.finrank ℚ L + Nat.log 2 (classNumber L) + 2 : ℕ) : ℝ) ≤ _
  push_cast
  linarith

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.ZK.sNum :
    UpperTheory.V.ZK.SNum := by
  unfold UpperTheory.V.ZK.SNum
  intro hFew hCount hSha hLayer hTors
  obtain ⟨C0, hC0⟩ := hTors
  refine ⟨5 * (max C0 9 + 2) + 11, ?_⟩
  unfold UpperTheory.V.ZK.ShaK
  intro l hl L i1 i2 hTC hMu E hE
  obtain ⟨k, rfl⟩ : ∃ k, E = k + 1 := ⟨E - 1, by omega⟩
  obtain ⟨L', i3, i4, c, d, hTC', hTop, hlc, hcp, hdeg, hd, hlc2, hdisc, hsha⟩ :=
    hLayer L l (k + 1) hMu hE
  have hl1 : 1 < l := hl.out.one_lt
  have hB : ∀ (F : Type) [Field F] [NumberField F] [Algebra L' F] (ν : ℕ) (ζ : (𝓞 F)ˣ)
      (γ : Gal(F/L')), Lay l c ν ζ γ →
      Finite ↑(EqHom γ ((1 + l ^ c) ^ (k + 1)) (l ^ ν)) ∧
        Nat.card ↑(EqHom γ ((1 + l ^ c) ^ (k + 1)) (l ^ ν)) ≤
          tc L' (4 * k + 10) (2 * k + 3) * tc L' (4 * k + 10) (2 * k + 2) *
            l ^ ((2 * k + 2 + (2 * k + 3) * (c + (2 * k + 3)) + (k + 1).factorization l) * gens L' +
              c + (k + 1).factorization l) := by
    intro F i5 i6 i7 ν ζ γ hLay
    have hfew := hFew L' F hTC' l c ν k ζ γ hLay (by omega) (by omega)
    have hcnt := hCount L' F hTC' l c ν (k + 1) _ _ ζ γ hLay (by omega) hfew
    refine ⟨hcnt.1, ?_⟩
    have hP : 0 < (l ^ ν) ^ InfinitePlace.nrComplexPlaces L' := pow_pos (pow_pos (by omega) _) _
    have h2 := hcnt.2
    apply le_of_mul_le_mul_left _ hP
    calc _ = Nat.card ↑(EqHom γ ((1 + l ^ c) ^ (k + 1)) (l ^ ν)) *
          (l ^ ν) ^ InfinitePlace.nrComplexPlaces L' := mul_comm _ _
      _ ≤ _ := h2
      _ = _ := by ring
  obtain ⟨s, hs, hlsB⟩ := hSha L' hTC' l c (k + 1) _ hTop hE hB
  have hne : LDataCardLeFinrank.shaInv L l ((k + 1 : ℕ) : ℤ) ≠ ⊤ := by
    intro htop
    rw [htop, hs] at hsha
    exact ENat.coe_ne_top s (top_le_iff.mp hsha)
  refine ⟨(LDataCardLeFinrank.shaInv L l ((k + 1 : ℕ) : ℤ)).toNat, (ENat.coe_toNat hne).symm, ?_⟩
  have hs0 : (LDataCardLeFinrank.shaInv L l ((k + 1 : ℕ) : ℤ)).toNat ≤ s := by
    have h := hsha
    rw [← ENat.coe_toNat hne, hs] at h
    exact_mod_cast h
  set s0 := (LDataCardLeFinrank.shaInv L l ((k + 1 : ℕ) : ℤ)).toNat with hs0def
  set T1 := tc L' (4 * k + 10) (2 * k + 3) with hT1
  set T2 := tc L' (4 * k + 10) (2 * k + 2) with hT2
  set bN := 2 * k + 2 + (2 * k + 3) * (c + (2 * k + 3)) with hbN
  set fN := (k + 1).factorization l with hfN
  set g := gens L' with hg
  set X := (bN + fN) * g + c + fN with hX
  have hlsB' : l ^ s ≤ T1 * T2 * l ^ X := hlsB
  have hBpos : 1 ≤ T1 * T2 * l ^ X := le_trans (Nat.one_le_pow _ _ (by omega)) hlsB'
  have hT1ne : T1 ≠ 0 := by
    intro h
    rw [h] at hBpos
    simp at hBpos
  have hT2ne : T2 ≠ 0 := by
    intro h
    rw [h] at hBpos
    simp at hBpos
  have hlR : (1:ℝ) < l := by exact_mod_cast hl1
  have hl0R : (0:ℝ) < l := by linarith
  have hlog0 : 0 < Real.log (l:ℝ) := Real.log_pos hlR
  have hlogs : (s:ℝ) * Real.log l ≤ Real.log T1 + Real.log T2 + (X:ℝ) * Real.log l := by
    have hT1R : (0:ℝ) < T1 := by exact_mod_cast Nat.pos_of_ne_zero hT1ne
    have hT2R : (0:ℝ) < T2 := by exact_mod_cast Nat.pos_of_ne_zero hT2ne
    calc (s:ℝ) * Real.log l = Real.log ((l:ℝ) ^ s) := by rw [Real.log_pow]
      _ ≤ Real.log ((T1:ℝ) * T2 * (l:ℝ) ^ X) := by
          apply Real.log_le_log (pow_pos hl0R _)
          exact_mod_cast hlsB'
      _ = Real.log T1 + Real.log T2 + (X:ℝ) * Real.log l := by
          rw [Real.log_mul (by positivity) (pow_pos hl0R _).ne', Real.log_mul hT1R.ne' hT2R.ne',
            Real.log_pow]
  have hT1b := hC0 L' hTC' (k + 1) hE (2 * k + 3) (by omega)
  have hT2b := hC0 L' hTC' (k + 1) hE (2 * k + 2) (by omega)
  rw [show 4 * (k + 1) + 6 = 4 * k + 10 by ring] at hT1b hT2b
  unfold kBound at hT1b hT2b
  have hcard := InfinitePlace.card_add_two_mul_card_eq_rank L'
  have hn'big : 2 * k + 4 ≤ Module.finrank ℚ L' := by omega
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, pow_zero] at hlc
    omega
  have hcl : c < l ^ c := Nat.lt_pow_self hl1
  have hll : l ≤ l ^ c := Nat.le_self_pow hc0 l
  have hf : fN < k + 1 := Nat.factorization_lt l (by omega)
  have hDne := NumberField.discr_ne_zero L'
  have hD'1 : 1 ≤ (discr L').natAbs := Int.natAbs_pos.mpr hDne
  have hD'1R : (1:ℝ) ≤ ((discr L').natAbs : ℝ) := by exact_mod_cast hD'1
  have hgl := gens_le L'
  set n' : ℝ := (Module.finrank ℚ L' : ℝ) with hn'
  set Y := Real.log (2 * ((discr L').natAbs : ℝ)) with hY
  set u : ℝ := 2 * ((k + 1 : ℕ) : ℝ) * n' with hu
  have hkR : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hn'bigR : 2 * (k:ℝ) + 4 ≤ n' := by rw [hn']; exact_mod_cast hn'big
  have hk1 : ((k + 1 : ℕ) : ℝ) = k + 1 := by push_cast; ring
  have hu' : u = 2 * ((k:ℝ) + 1) * n' := by rw [hu, hk1]
  have hn'0 : (0:ℝ) ≤ n' := by linarith
  have hn'u : 2 * n' ≤ u := by
    rw [hu']
    have := mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 2 * ((k:ℝ) + 1) by linarith) hn'0
    linarith
  have hku : 2 * ((k:ℝ) + 1) ≤ u := by
    rw [hu']
    have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ n' by linarith)
      (show (0:ℝ) ≤ 2 * ((k:ℝ) + 1) by positivity)
    linarith
  have hu2 : 2 ≤ u := by linarith
  have hL2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hY2 : Real.log 2 ≤ Y := Real.log_le_log (by norm_num) (by linarith)
  have hYh : 1 / 2 ≤ Y := by linarith
  have hcR : (c:ℝ) ≤ 2 * n' := by
    have : c ≤ 2 * Module.finrank ℚ L' := by omega
    rw [hn']; exact_mod_cast this
  have hlR2 : (l:ℝ) ≤ 2 * n' := by
    have : l ≤ 2 * Module.finrank ℚ L' := le_trans hll hlc2
    rw [hn']; exact_mod_cast this
  have hfR : (fN:ℝ) ≤ k + 1 := by
    have : fN ≤ k + 1 := hf.le
    exact_mod_cast this
  have htl : Real.log l ≤ u := by
    have := Real.log_le_sub_one_of_pos hl0R
    linarith
  have hbR : (bN:ℝ) = 2 * k + 2 + (2 * k + 3) * (c + (2 * k + 3)) := by rw [hbN]; push_cast; ring
  have hb0 : (0:ℝ) ≤ bN := Nat.cast_nonneg _
  have hbb : (bN:ℝ) ≤ u + 2 * u ^ 2 := by
    rw [hbR]
    have a1 : (2 * (k:ℝ) + 3) * (c + (2 * k + 3)) ≤ n' * (3 * n') :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    have a2 : 2 * (k:ℝ) + 2 ≤ u := by linarith
    have a3 : n' * (3 * n') ≤ 2 * u ^ 2 := by
      have h4 : (2 * n') ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hn'u 2
      have e1 : (2 * n') ^ 2 = 4 * n' ^ 2 := by ring
      have e2 : n' * (3 * n') = 3 * n' ^ 2 := by ring
      have h5 : 0 ≤ n' ^ 2 := by positivity
      linarith
    linarith
  have hg0 : (0:ℝ) ≤ g := Nat.cast_nonneg _
  have hgg : (g:ℝ) ≤ u + 2 * u * Y + 2 := by
    have hY0 : 0 ≤ Y := by linarith
    have : 2 * (2 * n') * Y ≤ 2 * u * Y := by
      have := mul_le_mul_of_nonneg_right hn'u hY0
      linarith
    have hgl' : (g:ℝ) ≤ 2 * n' + 2 * (2 * n') * Y + 2 := hgl
    linarith
  have hc0R : (0:ℝ) ≤ c := Nat.cast_nonneg _
  have hcu : (c:ℝ) ≤ u := by linarith
  have hf0 : (0:ℝ) ≤ fN := Nat.cast_nonneg _
  have hfu : (fN:ℝ) ≤ u := by linarith
  have hP := num_poly u Y (Real.log l) bN g c fN hu2 hYh htl hb0 hbb hg0 hgg hc0R hcu hf0 hfu
  have hXR : (X:ℝ) = ((bN:ℝ) + fN) * g + c + fN := by rw [hX]; push_cast; ring
  have hP' : (X:ℝ) * Real.log l ≤ u ^ 9 * Y := by rw [hXR]; exact hP
  have ht : (s:ℝ) * Real.log l ≤ 2 * Real.exp (u ^ C0 * Y) + (X:ℝ) * Real.log l := by
    have e1 : Real.log (T1:ℝ) ≤ Real.exp (u ^ C0 * Y) := hT1b
    have e2 : Real.log (T2:ℝ) ≤ Real.exp (u ^ C0 * Y) := hT2b
    linarith
  have h3 := num_three C0 u Y ((s:ℝ) * Real.log l) hu2 hYh _ hP' ht
  have hs0R : (s0:ℝ) * Real.log l ≤ (s:ℝ) * Real.log l :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hs0) hlog0.le
  have hC : 0 ≤ max C0 9 + 2 := by
    have := le_max_right C0 9
    linarith
  have hn1 : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
  have hD1 : 1 ≤ (discr L).natAbs := Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
  have hdown := num_down (max C0 9 + 2) hC (k + 1) (Module.finrank ℚ L) (discr L).natAbs
    (Module.finrank ℚ L') (discr L').natAbs d (l ^ c) hE hn1 hD1 hD'1 hdeg (by omega) hd hlc2 hdisc
  have hmid : Real.exp (u ^ (max C0 9 + 2) * Y) =
      kBound (max C0 9 + 2) (k + 1) (Module.finrank ℚ L') (discr L').natAbs := by
    unfold kBound
    rfl
  linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ExpStep
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK
open Polynomial

private theorem exp_cong (w : ℕ) (g : ℤ[X]) : (X ^ w - 1 : ℤ[X]) ∣ expand ℤ (1 + w) g - g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact dvd_add hp hq
  | monomial n a =>
    rw [expand_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← mul_sub]
    apply dvd_mul_of_dvd_right
    have h1 : (X : ℤ[X]) ^ (n * (1 + w)) - X ^ n = X ^ n * ((X ^ w) ^ n - 1 ^ n) := by
      ring
    rw [h1]
    exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ _) _

private theorem exp_step (w j : ℕ) (x : ℤ[X]) (hx : (X ^ w - 1 : ℤ[X]) ^ j ∣ x) :
    (X ^ w - 1 : ℤ[X]) ^ (j + 1) ∣ expand ℤ (1 + w) x - ((1 + w : ℕ) : ℤ[X]) ^ j * x := by
  obtain ⟨y, rfl⟩ := hx
  have hE : expand ℤ (1 + w) (X ^ w - 1 : ℤ[X]) = (X ^ w - 1) * ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i := by
    rw [mul_comm, geom_sum_mul]
    simp only [map_sub, map_pow, expand_X, map_one, ← pow_mul, mul_comm]
  have hSk : (X ^ w - 1 : ℤ[X]) ∣ ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i - ((1 + w : ℕ) : ℤ[X]) := by
    have h1 : ((1 + w : ℕ) : ℤ[X]) = ∑ i ∈ Finset.range (1 + w), ((1 : ℤ[X]) ^ i) := by simp
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow ((X : ℤ[X]) ^ w) 1 i
  have hSj := hSk.trans (sub_dvd_pow_sub_pow _ _ j)
  have key : expand ℤ (1 + w) ((X ^ w - 1 : ℤ[X]) ^ j * y) - ((1 + w : ℕ) : ℤ[X]) ^ j * ((X ^ w - 1) ^ j * y) =
      (X ^ w - 1) ^ j * ((( ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i) ^ j - ((1 + w : ℕ) : ℤ[X]) ^ j) *
        expand ℤ (1 + w) y + ((1 + w : ℕ) : ℤ[X]) ^ j * (expand ℤ (1 + w) y - y)) := by
    rw [map_mul, map_pow, hE, mul_pow]; ring
  rw [key, pow_succ]
  exact mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_left hSj _) (dvd_mul_of_dvd_right (exp_cong w y) _))

private theorem exp_pow (k i : ℕ) : (((expand ℤ k).toLinearMap : Module.End ℤ ℤ[X]) ^ i) X = X ^ k ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Module.End.mul_apply, ih]; simp [← pow_mul, pow_succ']

private theorem exp_dvd (w M : ℕ) : (X ^ w - 1 : ℤ[X]) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
    (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i := by
  have hdeg : (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).natDegree = M := by
    rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hsum : ∑ i ∈ Finset.range (M + 1),
      (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i =
      (aeval ((expand ℤ (1 + w)).toLinearMap : Module.End ℤ ℤ[X])
        (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X])) X := by
    rw [aeval_eq_sum_range, hdeg, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, exp_pow]
  rw [hsum]
  clear hsum hdeg
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ_comm, map_mul, Module.End.mul_apply]
    have h := exp_step w n _ ih
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
      AlgHom.toLinearMap_apply]
    convert h using 3
    rw [zsmul_eq_mul]; push_cast; ring

private theorem nat_dvd (l c ν n : ℕ) (hl : l.Prime) (h0 : n ≠ 0) (hn : n < l ^ c) :
    (n : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ c := by
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  have hac : a ≤ c := by
    by_contra hca
    have h1 : l ^ c ≤ l ^ a := Nat.pow_le_pow_right hl.pos (by omega)
    have h2 : l ^ a ≤ l ^ a * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero l)))
    omega
  have hcop : Nat.Coprime u (l ^ ν) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hu))
  refine ⟨(l : ZMod (l ^ ν)) ^ (c - a) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)), ?_⟩
  have hv : (u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) = 1 :=
    (ZMod.unitOfCoprime u hcop).mul_inv
  calc (l : ZMod (l ^ ν)) ^ c = (l : ZMod (l ^ ν)) ^ a * (l : ZMod (l ^ ν)) ^ (c - a) *
        ((u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν))) := by
        rw [hv, mul_one, ← pow_add, Nat.add_sub_cancel' hac]
    _ = _ := by push_cast; ring

private theorem diff_dvd (l c ν s t : ℕ) (hl : l.Prime) (h : s ≠ t) (hs : s < l ^ c) (ht : t < l ^ c) :
    ((s : ZMod (l ^ ν)) - t) ∣ (l : ZMod (l ^ ν)) ^ c := by
  rcases lt_or_gt_of_ne h with hst | hst
  · have h1 := nat_dvd l c ν (t - s) hl (by omega) (by omega)
    rw [Nat.cast_sub hst.le] at h1
    rw [← neg_sub, neg_dvd]
    exact h1
  · have h1 := nat_dvd l c ν (s - t) hl (by omega) (by omega)
    rwa [Nat.cast_sub hst.le] at h1

private theorem sgl_dvd {q : ℕ} [NeZero q] (a b : ZMod q) (h : a ∣ b) :
    (AddMonoidAlgebra.single a 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ∣ AddMonoidAlgebra.single b 1 - 1 := by
  obtain ⟨c, rfl⟩ := h
  have hc : a * c = c.val • a := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  rw [hc]
  have h1 := sub_dvd_pow_sub_pow (AddMonoidAlgebra.single a (1 : ℤ)) 1 c.val
  rwa [one_pow, AddMonoidAlgebra.single_pow, one_pow] at h1

private theorem alg_dvd (q w M : ℕ) :
    (AddMonoidAlgebra.single (w : ZMod q) 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
      AddMonoidAlgebra.single ((1 + (w : ZMod q)) ^ i)
        ((∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i) := by
  have h := map_dvd (aeval (R := ℤ) (AddMonoidAlgebra.single (1 : ZMod q) (1 : ℤ))) (exp_dvd w M)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, map_pow, map_sub, map_one, aeval_X, AddMonoidAlgebra.single_pow, one_pow,
    nsmul_one, AddMonoidAlgebra.smul_single', mul_one, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h
  simpa only [map_pow] using h

private def push (q : ℕ) (t : ZMod q) : ZMod q × ZMod q →+ ZMod q where
  toFun x := x.1 + t * x.2
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring

theorem UpperTheory.V.ZK.sEta :
    UpperTheory.V.ZK.SEta := by
  intro l c ν M hl hM _ t₀
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hF := alg_dvd (l ^ ν) (l ^ c) M
  simp only [Nat.cast_pow] at hF
  let φ : ZMod (l ^ ν) → AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν)) :=
    fun t => AddMonoidAlgebra.mapDomainRingHom ℤ (push (l ^ ν) t)
  have hφ : ∀ (t : ZMod (l ^ ν)) (η : AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν))),
      φ t η = AddMonoidAlgebra.mapDomain (fun x : ZMod (l ^ ν) × ZMod (l ^ ν) => x.1 + t * x.2) η := by
    intro t η
    simp only [φ, AddMonoidAlgebra.mapDomainRingHom_apply]
    rfl
  have hφs : ∀ (t : ZMod (l ^ ν)) (x : ZMod (l ^ ν) × ZMod (l ^ ν)),
      φ t (AddMonoidAlgebra.single x 1) = AddMonoidAlgebra.single (x.1 + t * x.2) 1 := by
    intro t x; rw [hφ, AddMonoidAlgebra.mapDomain_single]
  let ι : AddMonoidAlgebra ℤ (ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) :=
    AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inl (ZMod (l ^ ν)) (ZMod (l ^ ν)))
  have hφι : ∀ t y, φ t (ι y) = y := by
    intro t y
    refine AddMonoidAlgebra.induction_linear y (by simp) (fun a b ha hb => by rw [map_add (f := _), map_add (f := _), ha, hb])
      (fun m r => ?_)
    simp only [ι, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, hφ]
    simp
  set s : Finset (Fin (M + 1)) := Finset.univ.erase t₀ with hs
  have hdiv : ∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1) ∣
      (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) ^ M := by
    have hcard : s.card = M := by simp [hs, Finset.card_erase_of_mem]
    calc _ ∣ ∏ _t' ∈ s, (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) :=
          Finset.prod_dvd_prod_of_dvd _ _ fun t' ht' => sgl_dvd _ _ (diff_dvd l c ν t₀ t' hp
            (fun h => (Finset.ne_of_mem_erase ht') (Fin.ext h).symm)
            (by have := t₀.isLt; omega) (by have := t'.isLt; omega))
      _ = _ := by rw [Finset.prod_const, hcard]
  obtain ⟨Q, hQ⟩ := hdiv.trans hF
  refine ⟨((∏ t' ∈ s, (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
      AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
      ι (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q)).coeff, ?_, ?_⟩
  · intro t ht
    rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod]
    rw [Finset.prod_eq_zero (i := t) (by simp [hs, ht]) (by rw [map_sub, hφs, hφs]; simp), zero_mul,
      AddMonoidAlgebra.coeff_zero]
  · rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod, hφι]
    have hfac : ∀ t' : Fin (M + 1), φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1) =
        AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ) *
          (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) 1 - 1) := by
      intro t'
      rw [map_sub, hφs, hφs, mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def,
        mul_one]
      simp
    have h1 : (∏ t' ∈ s, AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ)) *
        AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 = 1 := by
      rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, add_neg_cancel,
        Finset.prod_const_one, mul_one, AddMonoidAlgebra.one_def]
    have hmain : (∏ t' ∈ s, φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
        (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q) =
        (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
          ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q := by
      simp only [hfac, Finset.prod_mul_distrib]
      linear_combination (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
        ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q * h1
    rw [hmain, ← hQ]
    simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ExponentLe
namespace UpperTheory.V.ZK.TorsionExponentBound

theorem exponent_le (e n N m D : ℝ) (he : 1 ≤ e) (hn : 1 ≤ n) (hN1 : 1 ≤ N) (hN : N ≤ 4 * e + 6)
    (hm : m ≤ 2 * e + 1) (hD : 1 ≤ D) :
    12 * (m + 1) * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + (m + 1) * (2 * (n * N * N)) + 2 * m ≤
      (2 * e * n) ^ 24 * Real.log (2 * D) := by
  have hD2 : (0 : ℝ) < 2 * D := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ Real.log (2 * D) := Real.log_le_log (by norm_num) (by linarith)
  have hL : (0.69 : ℝ) < Real.log (2 * D) := by linarith
  have ha1 : 1 ≤ e * n := by nlinarith
  have hea : e ≤ e * n := by nlinarith
  have hP1 : 1 ≤ n * N := by nlinarith
  have hP : n * N ≤ 10 * (e * n) := by nlinarith
  have hNa : N ≤ 10 * (e * n) := by linarith
  have hm1 : m + 1 ≤ 4 * (e * n) := by linarith
  have hlogP : Real.log (2 * D * (n * N)) ≤ 16 * (e * n) * Real.log (2 * D) := by
    rw [Real.log_mul (ne_of_gt hD2) (ne_of_gt (by linarith))]
    have := Real.log_le_sub_one_of_pos (show 0 < n * N by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hL.le) (by linarith : (0 : ℝ) ≤ 16 * (e * n) - 1)]
  have hlogP0 : 0 ≤ Real.log (2 * D * (n * N)) := Real.log_nonneg (by nlinarith)
  have hA0 : 0 ≤ 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) := by
    have : 0 ≤ n * N := by linarith
    positivity
  have hA : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) ≤
      1920300 * (e * n) ^ 5 * Real.log (2 * D) := by
    have h3 : (n * N) ^ 3 ≤ (10 * (e * n)) ^ 3 := pow_le_pow_left₀ (by linarith) hP 3
    have t1 : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) ≤
        12 * (10 * (e * n)) ^ 3 * (10 * (e * n)) * (16 * (e * n) * Real.log (2 * D)) := by
      have : 0 ≤ (n * N) ^ 3 := by positivity
      have : 0 ≤ N := by linarith
      gcongr
    have t2 : 2 * (n * N * N) ≤ 300 * (e * n) ^ 5 * Real.log (2 * D) := by
      have q1 : n * N * N ≤ 10 * (e * n) * (10 * (e * n)) := by
        apply mul_le_mul hP hNa (by linarith) (by linarith)
      have q2 : (e * n) ^ 2 ≤ (e * n) ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
      have q3 : 0 ≤ (e * n) ^ 5 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL.le q3]
    have q4 : 0 ≤ Real.log (2 * D) := by linarith
    nlinarith [t1, t2]
  have hE : (2 * e * n) ^ 24 = 2 ^ 24 * (e * n) ^ 24 := by ring
  have hp6 : (e * n) ^ 6 ≤ (e * n) ^ 24 := pow_le_pow_right₀ ha1 (by norm_num)
  have hp1 : e * n ≤ (e * n) ^ 6 := by
    calc e * n = (e * n) ^ 1 := (pow_one _).symm
      _ ≤ (e * n) ^ 6 := pow_le_pow_right₀ ha1 (by norm_num)
  have hLpos : 0 ≤ Real.log (2 * D) := by linarith
  have k1 : (m + 1) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) ≤
      4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) := by
    calc _ ≤ 4 * (e * n) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) :=
          mul_le_mul_of_nonneg_right hm1 hA0
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by linarith)
  have k2 : 2 * m ≤ 12 * (e * n) ^ 6 * Real.log (2 * D) := by
    nlinarith [mul_le_mul_of_nonneg_right hp1 hLpos]
  have k3 : (e * n) ^ 6 * Real.log (2 * D) ≤ (e * n) ^ 24 * Real.log (2 * D) :=
    mul_le_mul_of_nonneg_right hp6 hLpos
  rw [hE]
  have k4 : 4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) =
      7681200 * ((e * n) ^ 6 * Real.log (2 * D)) := by ring
  nlinarith [k1, k2, k3, k4]

end UpperTheory.V.ZK.TorsionExponentBound

open NumberField UpperTheory.V

namespace UpperTheory.V.ZK

theorem torsAll : ∃ C : ℝ, ∀ (L) [Field L] [NumberField L], IsTotallyComplex L →
    ∀ e N m : ℕ, 1 ≤ e → 1 ≤ N → N ≤ 4 * e + 6 → m ≤ 2 * e + 1 →
      Finite (UpperTheory.V.K.torsHGL L N m) ∧
        Real.log (Nat.card (UpperTheory.V.K.torsHGL L N m)) ≤
          UpperTheory.V.kBound C e (Module.finrank ℚ L) (discr L).natAbs := by
  refine ⟨24, ?_⟩
  intro L _ _ hL e N m he hN1 hN hm
  haveI := hL
  have ht := UpperTheory.V.KT.tors_le L N m
  refine ⟨ht.1, ?_⟩
  have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
  have hD : 1 ≤ (discr L).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero L)
  have hdd : 1 ≤ Module.finrank ℚ L * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hA := UpperTheory.V.KT.orbnum L N m hN1
  have hBn : 0 < 2 * (discr L).natAbs * (Module.finrank ℚ L * N) := by positivity
  have hB : (0 : ℝ) < ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) := by exact_mod_cast hBn
  have hAexp : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
      Real.exp (12 * ((m : ℝ) + 1) * ((Module.finrank ℚ L : ℝ) * N) ^ 3 * N *
        Real.log (2 * ((discr L).natAbs : ℝ) * ((Module.finrank ℚ L : ℝ) * N))) := by
    have h1 : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
        ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) ^
          (12 * (m + 1) * (Module.finrank ℚ L * N) ^ 3 * N) := by exact_mod_cast hA
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hB] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hsexp : (((3 ^ (UpperTheory.V.KT.dd L N * N) : ℕ)) : ℝ) ≤
      Real.exp (2 * ((Module.finrank ℚ L : ℝ) * N * N)) := by
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    push_cast
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    push_cast
    have : (0 : ℝ) ≤ (Module.finrank ℚ L : ℝ) * N * N := by positivity
    nlinarith
  have hs1 : 1 ≤ 3 ^ (UpperTheory.V.KT.dd L N * N) := Nat.one_le_pow _ _ (by norm_num)
  have key := ht.log_le_exp hs1 hAexp hsexp
  refine key.trans ?_
  unfold UpperTheory.V.kBound
  apply Real.exp_le_exp.2
  have hE := UpperTheory.V.ZK.TorsionExponentBound.exponent_le (e : ℝ) (Module.finrank ℚ L : ℝ) (N : ℝ) (m : ℝ)
    ((discr L).natAbs : ℝ) (by exact_mod_cast he) (by exact_mod_cast hn) (by exact_mod_cast hN1)
    (by exact_mod_cast hN) (by exact_mod_cast hm) (by exact_mod_cast hD)
  refine hE.trans (le_of_eq ?_)
  rw [show ((24 : ℝ)) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end UpperTheory.V.ZK

theorem UpperTheory.V.ZK.sTors :
    UpperTheory.V.ZK.STors := by
  obtain ⟨C, h⟩ := UpperTheory.V.ZK.torsAll
  exact ⟨C, fun L _ _ hL E hE m hm => (h L hL E (4 * E + 6) m hE (by omega) le_rfl hm).2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.FProd
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

noncomputable section

namespace UpperTheory.V.ZK.Coc

variable {A K : Type} [CommRing A] [CommGroup K]

private def F (u : K → K → A) (v : K → A) : (n : ℕ) → (Fin n → K) → A
  | 0, _ => 1
  | 1, g => v (g 0)
  | n + 2, g => u (g 0) (g 1) * F u v n fun i => g i.succ.succ

private theorem F_coc (u : K → K → A) (v : K → A) (hu : ∀ a b c, u b c - u (a * b) c + u a (b * c) - u a b = 0)
    (hv : ∀ a b, v (a * b) = v a + v b) : ∀ (n : ℕ) (g : Fin (n + 1) → K),
    F u v n (fun i => g i.succ) + ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) * F u v n (Fin.contractNth j (· * ·) g) = 0
  | 0, g => by simp [F]
  | 1, g => by
    simp [F, Fin.sum_univ_two, Fin.contractNth, hv]
  | n + 2, g => by
    have ih := F_coc u v hu hv n fun i => g i.succ.succ
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h2 : ∀ j : Fin (n + 1), F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := fun j => by
      rw [F]
      congr 2
      funext i
      simp only [Fin.contractNth, Fin.val_succ, Nat.add_lt_add_iff_right,
        Nat.add_right_cancel_iff]
      rfl
    have h0 : F u v (n + 2) (Fin.contractNth 0 (· * ·) g) = u (g 0 * g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h1 : F u v (n + 2) (Fin.contractNth (Fin.succ 0) (· * ·) g) =
        u (g 0) (g 1 * g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h3 : F u v (n + 2) (fun i => g i.succ) = u (g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h4 : ∑ j : Fin (n + 1), (-1 : A) ^ ((j.succ.succ : ℕ) + 1) * F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) *
          F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2, Fin.val_succ, Fin.val_succ]; ring
    rw [h4, h0, h1, h3, eq_neg_of_add_eq_zero_right ih]
    simp only [Fin.val_zero, Fin.val_succ]
    linear_combination (F u v n fun i => g i.succ.succ.succ) * hu (g 0) (g 1) (g 2)

private theorem F_ins (u : K → K → A) (v : K → A) (hs : ∀ a b, u a b = u b a) (x : K) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    ∑ i : Fin (2 * E + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1) (Fin.insertNth (α := fun _ => K) i x g) =
      F u v (2 * E) g * v x := by
  intro E
  induction E with
  | zero =>
    intro g
    simp [F]
  | succ E ih =>
    intro g
    obtain ⟨a, b, rest, rfl⟩ : ∃ (a b : K) (rest : Fin (2 * E) → K),
        g = (Fin.cons a (Fin.cons b rest) : Fin (2 * E + 1 + 1) → K) := by
      let tail := Fin.tail (n := 2 * E + 1) (α := fun _ => K) g
      let rest := Fin.tail (n := 2 * E) (α := fun _ => K) tail
      refine ⟨g 0, tail 0, rest, ?_⟩
      calc
        g = Fin.cons (g 0) tail :=
          (Fin.cons_self_tail (α := fun _ => K) g).symm
        _ = Fin.cons (g 0) (Fin.cons (tail 0) rest) :=
          congrArg (Fin.cons (α := fun _ => K) (g 0))
            (Fin.cons_self_tail (α := fun _ => K) tail).symm
    have hpair (n : ℕ) (c d : K) (f : Fin n → K) :
        F u v (n + 2) (Fin.cons c (Fin.cons d f) : Fin (n + 2) → K) = u c d * F u v n f := by
      rw [F]
      simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ]
    change (∑ i : Fin (2 * E + 1 + 1 + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1 + 2)
      (Fin.insertNth (α := fun _ => K) i x (Fin.cons a (Fin.cons b rest)))) =
      F u v (2 * E + 2) (Fin.cons a (Fin.cons b rest)) * v x
    rw [hpair (2 * E) a b rest, Fin.sum_univ_succ, Fin.sum_univ_succ, mul_assoc (u a b),
      ← ih rest, Finset.mul_sum]
    simp only [Fin.insertNth_succ_cons, Fin.insertNth_zero', hpair, Fin.val_zero, Fin.val_succ, hs x a]
    rw [← add_assoc]
    refine (congrArg₂ (· + ·) (by ring : _ = (0 : A)) (Finset.sum_congr rfl fun j _ => by ring)).trans (zero_add _)

private theorem F_prod (u : K → K → A) (v : K → A) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    F u v (2 * E) g = ∏ s : Fin E, u (g ⟨2 * s, by omega⟩) (g ⟨2 * s + 1, by omega⟩)
  | 0, g => by simp [F]
  | E + 1, g => by
    rw [Fin.prod_univ_succ]
    exact congrArg (u _ _ * ·) (F_prod u v E fun i => g i.succ.succ)

private theorem ex_log [Finite K] [IsCyclic K] (q : ℕ) (ζ : K) (hζ : orderOf ζ = q) :
    ∃ (r : ℕ) (lg : K → ℤ), 0 < r ∧ (∀ a b, ((q * r : ℕ) : ℤ) ∣ lg a + lg b - lg (a * b)) ∧
      ∀ x : ℕ, ((q * r : ℕ) : ℤ) ∣ lg (ζ ^ x) - r * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := K)
  choose y hy using hg
  simp only at hy
  have hN : 0 < orderOf g := orderOf_pos g
  have hd : ∀ m n : ℕ, g ^ m = g ^ n → (orderOf g : ℤ) ∣ (m : ℤ) - n := fun m n h =>
    (pow_eq_pow_iff_modEq.1 h).symm.dvd
  set r := (orderOf g).gcd (y ζ) with hr
  have hr0 : 0 < r := Nat.gcd_pos_of_pos_left _ hN
  have hq : q * r = orderOf g := by
    rw [← hζ, ← congrArg orderOf (hy ζ), orderOf_pow, hr, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  have hb := Nat.gcd_eq_gcd_ab (orderOf g) (y ζ)
  refine ⟨r, fun a => (orderOf g).gcdB (y ζ) * y a, hr0, fun a b => ?_, fun x => ?_⟩
  · rw [hq]
    have := hd (y a + y b) (y (a * b)) (by rw [pow_add, hy, hy, hy])
    push_cast at this
    simpa [mul_sub, mul_add] using this.mul_left ((orderOf g).gcdB (y ζ))
  · rw [hq]
    have := hd (y (ζ ^ x)) (y ζ * x) (by rw [pow_mul, hy, hy])
    push_cast at this
    have h2 := (this.mul_left ((orderOf g).gcdB (y ζ))).sub (dvd_mul_right (orderOf g : ℤ) ((orderOf g).gcdA (y ζ) * x))
    refine h2.trans (dvd_of_eq ?_)
    rw [hr, hb]; ring

end UpperTheory.V.ZK.Coc

open UpperTheory.V.ZK.Coc in
theorem UpperTheory.V.ZK.sCoc : UpperTheory.V.ZK.SCoc := by
  intro k _ _ q _ e ζ hζ v
  obtain ⟨r, lg, hr, h1, h2⟩ := ex_log q ζ hζ.eq_orderOf.symm
  have hN : ((q * r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos (NeZero.pos q) hr).ne'
  choose U hU using h1
  have hs : ∀ a b, U a b = U b a := fun a b => mul_left_cancel₀ hN (by rw [← hU, ← hU, mul_comm a b]; ring)
  have hc : ∀ a b c, U b c - U (a * b) c + U a (b * c) - U a b = 0 := fun a b c =>
    mul_left_cancel₀ hN (by simp only [mul_sub, mul_add, ← hU, mul_assoc a b c]; ring)
  set u : kˣ → kˣ → ZMod q := fun a b => (U a b : ZMod q) with hu
  set w : kˣ → ZMod q := fun a => Multiplicative.toAdd (v a) with hw
  refine ⟨Finsupp.linearCombination _ (F u w _), ?_, fun x g => ?_⟩
  · rintro _ ⟨z, rfl⟩
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
    | single g c =>
      have := F_coc u w (fun a b c => by simp only [hu]; exact_mod_cast congrArg (Int.cast : ℤ → ZMod q) (hc a b c))
        (fun a b => by simp [hw]) _ g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [bd, Finsupp.linearCombination_single, map_smul, map_add (f := _), map_sum, one_smul, smul_eq_mul, one_mul]
      exact mul_eq_zero_of_right _ this
  · have key : ∑ j : ZMod q, u (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd j))
        (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd 1)) = x := by
      set χ := chi q ζ hζ.pow_eq_one x with hχ
      have e1 : ((q * r : ℕ) : ℤ) * ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          q * lg (χ (Multiplicative.ofAdd 1)) := by
        simp only [Finset.mul_sum, ← hU, ← map_mul, ← ofAdd_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have := Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) fun j => lg (χ (Multiplicative.ofAdd j))
        simp only [Equiv.coe_addRight] at this
        rw [this]; simp
      obtain ⟨m, hm⟩ := h2 (x * (1 : ZMod q).val)
      have e2 : lg (χ (Multiplicative.ofAdd 1)) = r * ((x * (1 : ZMod q).val : ℕ) + q * m) := by
        have : χ (Multiplicative.ofAdd 1) = ζ ^ (x * (1 : ZMod q).val) := rfl
        rw [this]; push_cast at hm ⊢; linear_combination hm
      have e3 : ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          (x * (1 : ZMod q).val : ℕ) + q * m := mul_left_cancel₀ hN (by rw [e1, e2]; push_cast; ring)
      have := congrArg (Int.cast : ℤ → ZMod q) e3
      simpa [hu] using this
    have hp : ∀ h : Fin (2 * e + 1 + 1) → kˣ, Finsupp.linearCombination (ZMod q) (F u w _)
        (prism (ZMod q) g _ (Finsupp.single h 1)) = F u w (2 * (e + 1)) h * w g := fun h => by
      rw [← F_ins u w (fun a b => by simp only [hu, hs a b]) g (e + 1) h]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [prism, Finsupp.linearCombination_single, one_smul, map_sum, map_smul, smul_eq_mul, mul_one, one_mul,
        inv_mul_cancel_comm, ite_self]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [zc, map_sum, cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hp, F_prod]
    rw [← Finset.sum_mul, ← key, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine congrArg (· * w g) (Finset.sum_congr rfl fun j _ => Finset.prod_congr rfl fun s _ => ?_)
    have a1 : 2 * (s : ℕ) % 2 = 0 := by omega
    have a2 : ¬(2 * (s : ℕ) + 1) % 2 = 0 := by omega
    have a3 : 2 * (s : ℕ) / 2 = s := by omega
    simp only [a1, a2, a3, if_true, if_false, Fin.eta]

end
end

open Formalism.GaloisCohomology

namespace UpperTheory.V.ZK

theorem lemmaK (hB : BOdd) (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) :
    ∃ CK, LemmaK CK :=
  lemmaK_of_steps hB hP hF hT
    sChain sPrism sPrismMul sZc LateralTheory.Fin.SRel.intersectionNumber_baseChange sTrans sCoc sThetaOf sPhi sEta LateralTheory.Fin.SStein.intersectionNumber_baseChange sClassOf sUpperOf LateralTheory.Fin.SDetect.intersectionNumber_baseChange sCount LateralTheory.Fin.SFewOf.intersectionNumber_baseChange PositivityTheory.QuaternionShaBounds.sSha LateralTheory.Fin.SLayer.intersectionNumber_baseChange sTors sNum sFinal

end UpperTheory.V.ZK
