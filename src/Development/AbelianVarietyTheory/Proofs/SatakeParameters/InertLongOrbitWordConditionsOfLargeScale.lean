module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeParametersRoundedSizeBoundStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeRoundedSizeBound
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem mul_small_le_bHat {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ) (hR : Roomy L C') (hC : 0 ≤ C)
    (hCC : 2 * C ≤ C') (hj : 2 * j + 2 ≤ D.host.Lw) :
    C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  have hlow := (GlobalTheory.T.roundedSizeBound_window L C' hR).1
  obtain ⟨-, hw2, hG⟩ := GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C' hR
  obtain ⟨h100, -, -, -, -, hbig⟩ := hR
  have hw0 : (0 : ℝ) ≤ (wHat D : ℝ) := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hhalf : ((D.R.t : ℝ) + 1) / 2 ≤ L.sc.b' := by linarith
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hjN : (j + 1) * 2 ≤ D.host.Lw := by omega
  have hjL : ((j : ℝ) + 1) * 2 ≤ (D.host.Lw : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  push_cast
  have s1 : C * ((j : ℝ) + 1) * ((wHat D : ℝ) + sHat L + etaHat L + 1)
      ≤ C * ((j : ℝ) + 1) * (2 * L.sc.b') :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hC hj0)
  have s2 : C * ((j : ℝ) + 1) * (2 * L.sc.b') ≤ C' * ((j : ℝ) + 1) * L.sc.b' := by
    have := mul_le_mul_of_nonneg_right hCC (mul_nonneg hj0 hb0)
    nlinarith
  have s3 : C' * ((j : ℝ) + 1) * L.sc.b' + L.sc.b' ≤ C' * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
    have hk : C' * ((j : ℝ) + 1) + 1 ≤ C' * ((D.host.Lw : ℝ) + 1) := by nlinarith
    nlinarith
  linarith

end GlobalTheory.HTW
end

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_smallBounds_le_roundedSizeBound : ∀ {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ), Roomy L C' → 0 ≤ C → 2 * C ≤ C' → 2 * j + 2 ≤ D.host.Lw → C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  first | exact @GlobalTheory.HTW.mul_small_le_bHat | exact GlobalTheory.HTW.mul_small_le_bHat | (intros; apply GlobalTheory.HTW.mul_small_le_bHat <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersLeastPowerDepthSpecStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeastPowerDepthSpec
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem depth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l →
    LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧
      ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  intro D L P l hl
  obtain ⟨j, hj, hjL⟩ := P.Lw_j l hl
  have hne : ({j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} : Set ℕ).Nonempty := ⟨j, hj⟩
  have hmem : LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l := Nat.sInf_mem hne
  have hle : depth L l ≤ j := Nat.sInf_le hj
  refine ⟨hmem, by omega, fun hlt => ?_⟩
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  by_contra hc
  push_neg at hc
  interval_cases h : depth L l
  · simp at hmem
    linarith
  · simp at hmem
    linarith

end GlobalTheory
end

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leastPowerDepth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l → LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧ ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  first | exact @GlobalTheory.depth_spec | exact GlobalTheory.depth_spec | (intros; apply GlobalTheory.depth_spec <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersClusterDepthAtPrimeEqLeastPowerDepthStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClusterDepthAtPrimeEqLeastPowerDepth
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jA_eq_depth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  intro D L l hl hlA
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : (1 : ℝ) < (l : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) < LevelStarExponents.lA L := by linarith
  have key : ∀ j : ℕ, LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j ↔ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ ≤ j := by
    intro j
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow hx hA, Real.rpow_natCast]
  have hlog : 1 < Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L) := by
    rw [Real.lt_logb_iff_rpow_lt hx hA, Real.rpow_one]; linarith
  have hc : 1 ≤ ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hset : {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} = Set.Ici ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊ := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_Ici]; exact key j
  unfold jA depth
  rw [hset, csInf_Ici, max_eq_right hc]

end GlobalTheory.HTW.Rec
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  first | exact @GlobalTheory.HTW.Rec.jA_eq_depth | exact GlobalTheory.HTW.Rec.jA_eq_depth | (intros; apply GlobalTheory.HTW.Rec.jA_eq_depth <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLength
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindow
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem winClusters_exists_step {n : ℕ} (th : ZMod n → Prop) (j : ℕ) (x : ZMod n) :
    ∃ s : ℕ, s ≤ j ∧ (s = 0 → ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x + q)) ∧ (0 < s → th (x + s)) ∧
      ∀ q : ℕ, 0 < q → q < s → ¬ th (x + q) := by
  classical
  by_cases h : ∃ q : ℕ, 1 ≤ q ∧ q ≤ j ∧ th (x + q)
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
    refine ⟨Nat.find h, h2, fun h0 => absurd h0 (by omega), fun _ => h3, ?_⟩
    intro q hq hqs hth
    exact Nat.find_min h hqs ⟨hq, by omega, hth⟩
  · push_neg at h
    refine ⟨0, Nat.zero_le _, fun _ q hq hqj hth => absurd hth (h q hq hqj), fun h0 => absurd h0 (lt_irrefl 0),
      fun q hq hq0 => absurd hq0 (by omega)⟩

theorem winClusters : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n →
    WindowTwo th L → Clusters th j := by
  intro n th L j _ hL hn hW
  choose sp hsp using winClusters_exists_step th j
  set F : Set (ZMod n) := {x | th x ∧ ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q)} with hFdef
  have key : ∀ x1 x2 : ZMod n, x1 ∈ F → x2 ∈ F → ∀ s1 s2 : ℕ, s1 ≤ s2 → s2 ≤ j →
      x1 + s1 = x2 + s2 → x1 = x2 := by
    intro x1 x2 hx1 hx2 s1 s2 hs hs2 he
    rcases Nat.lt_or_ge s1 s2 with hlt | hge
    · exfalso
      apply hx1.2 (s2 - s1) (by omega) (by omega)
      have : x1 - ((s2 - s1 : ℕ) : ZMod n) = x2 := by
        rw [Nat.cast_sub hs]
        linear_combination he
      rw [this]; exact hx2.1
    · have : s1 = s2 := le_antisymm hs hge
      subst this
      exact add_right_cancel he
  have ofCl : ∀ x y : ZMod n, (y = x ∨ y = x + (sp x : ZMod n)) → ∃ s : ℕ, s ≤ j ∧ y = x + s := by
    intro x y h
    rcases h with h | h
    · exact ⟨0, Nat.zero_le _, by simp [h]⟩
    · exact ⟨sp x, (hsp x).1, h⟩
  refine ⟨F, sp, ?_, ?_⟩
  · rintro x ⟨hx, hxF⟩
    obtain ⟨h1, _, h3, h4⟩ := hsp x
    refine ⟨hx, h1, by omega, ?_, h4, hxF⟩
    rcases Nat.eq_zero_or_pos (sp x) with h | h
    · rw [h]; simpa using hx
    · exact h3 h
  · intro y hy
    have ex : ∃ x, x ∈ F ∧ (y = x ∨ y = x + (sp x : ZMod n)) := by
      by_cases hyF : ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (y - q)
      · exact ⟨y, ⟨hy, hyF⟩, Or.inl rfl⟩
      · push_neg at hyF
        obtain ⟨q, hq1, hqj, hq⟩ := hyF
        have hxF : y - (q : ZMod n) ∈ F := by
          refine ⟨hq, ?_⟩
          intro q' hq'1 hq'j hth
          apply hW (y - q - q') 0 q' (q' + q) (by omega) (by omega) (by omega)
          refine ⟨by simpa using hth, ?_, ?_⟩
          · have : y - (q : ZMod n) - q' + (q' : ℕ) = y - q := by ring
            rw [this]; exact hq
          · have : y - (q : ZMod n) - q' + ((q' + q : ℕ) : ZMod n) = y := by push_cast; ring
            rw [this]; exact hy
        have hyx : y - (q : ZMod n) + (q : ZMod n) = y := by ring
        obtain ⟨h1, h2, h3, h4⟩ := hsp (y - q)
        have hspq : sp (y - q) = q := by
          rcases Nat.eq_zero_or_pos (sp (y - q)) with h0 | hpos
          · exact absurd (by rw [hyx]; exact hy) (h2 h0 q hq1 hqj)
          rcases lt_trichotomy (sp (y - q)) q with hlt | heq | hgt
          · exfalso
            apply hW (y - q) 0 (sp (y - q)) q hpos hlt (by omega)
            refine ⟨by simpa using hq, h3 hpos, ?_⟩
            rw [hyx]; exact hy
          · exact heq
          · exact absurd (by rw [hyx]; exact hy) (h4 q (by omega) hgt)
        refine ⟨y - q, hxF, Or.inr ?_⟩
        rw [hspq, hyx]
    obtain ⟨x, hxF, hx⟩ := ex
    refine ⟨x, ⟨hxF, hx⟩, ?_⟩
    rintro z ⟨hzF, hz⟩
    obtain ⟨s1, hs1, e1⟩ := ofCl z y hz
    obtain ⟨s2, hs2, e2⟩ := ofCl x y hx
    rcases le_total s1 s2 with h | h
    · exact key z x hzF hxF s1 s2 h hs2 (e1.symm.trans e2)
    · exact (key x z hxF hzF s2 s1 h hs1 (e2.symm.trans e1)).symm

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindowStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n → WindowTwo th L → Clusters th j := by
  first | exact @GlobalTheory.HTW.winClusters | exact GlobalTheory.HTW.winClusters | (intros; apply GlobalTheory.HTW.winClusters <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLength
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem long_clusters : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j →
    2 * j + 2 ≤ H.Lw →
    Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  intro R H τ φ j h4 hj hjL
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hdvd : orderOf φ.2 ∣ orderOf φ := orderOf_snd_dvd_orderOf
  have hle : orderOf φ.2 ≤ orderOf φ := Nat.le_of_dvd hpos hdvd
  have hw := GlobalTheory.T.atMostTwoThick_in_window_long_orbit H τ φ h4
  refine ⟨GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow _ H.Lw j hj (by omega) (by omega) hw, by omega⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LongOrbitThickLettersClustersAndLengthStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.longOrbit_thickLetters_clusters_and_length : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j → 2 * j + 2 ≤ H.Lw → Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  first | exact @GlobalTheory.long_clusters | exact GlobalTheory.long_clusters | (intros; apply GlobalTheory.long_clusters <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbit
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_hypA_depth_of_long_orbit {D : D7} (L : SizeData₂ D) (hP : ParameterChoice' D L) (C : ℝ)
    (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ) (hR : Roomy L C) (hl : 11 ≤ l)
    (hlA : (l : ℝ) < LevelStarExponents.lA L) (ho : 4 * D.host.Lw < orderOf φ.2) :
    (pageWord L j ε τ φ).HypA (depth L l) := by
  obtain ⟨-, hLw, h2⟩ := GlobalTheory.T.leastPowerDepth_spec L hP l hl
  have h1 : 1 ≤ depth L l := le_trans (by norm_num) (h2 hlA)
  obtain ⟨hcl, hn⟩ := GlobalTheory.T.longOrbit_thickLetters_clusters_and_length D.host τ φ (depth L l) ho h1 hLw
  have hbox := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR
  have hth : (pageWord L j ε τ φ).thick = fun i : ZMod (orderOf φ) => Thick D.host (letter τ φ i) :=
    funext fun i => propext (GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i)
  have hpar := GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L 40 C (depth L l) hR (by norm_num) (by linarith [hR.1]) hLw
  refine ⟨fun i => ?_, h1, hn, fun _ => ?_, ?_⟩
  · have := hbox.2.2.2.2.2 i
    have h0 : (0 : ℤ) ≤ ((pageWord L j ε τ φ).η : ℤ) := Int.natCast_nonneg _
    linarith
  · show 40 * (depth L l + 1) * (wHat D + sHat L + etaHat L + 1) ≤ bHat L
    exact_mod_cast hpar
  · rw [hth]; exact hcl

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbitStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf φ.2 → (pageWord L j ε τ φ).HypA (depth L l) := by
  first | exact @GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | exact GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | (intros; apply GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrime
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordsB_recWord_of_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m)
    (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C →
    11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  intro D L hP C C₂ j ε n g ψ l hR hO hC hl hlA hord
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := by
    funext a
    rw [hg a]
    rfl
  generalize g 0 = τ at hgl
  subst hgl
  have hjA : jA L l = depth L l := GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth L l hl hlA
  have hA := GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit L hP C j ε τ ψ l hR hl hlA hord
  obtain ⟨_, _, hjn, _, hcl⟩ := hA
  have hD := GlobalTheory.T.leastPowerDepth_spec L hP l hl
  have hth : ThickN (recWord L j ε (letter τ ψ)).b
      (recWord L j ε (letter τ ψ)).η (recWord L j ε (letter τ ψ)).sz =
      (pageWord L j ε τ ψ).thick := by
    funext a
    exact propext (GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hjA]; exact hjn
  · rcases le_or_gt 0 C₂ with h0 | h0
    · rw [hjA]
      exact GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L C₂ C (depth L l) hR h0 hC hD.2.1
    · have h1 : (0 : ℝ) ≤ ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) := by
        positivity
      have h2 : C₂ * ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg h0.le h1
      exact h2.trans (Nat.cast_nonneg _)
  · rw [hth, hjA]; exact hcl

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrimeStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualSizeWord_long_orbit_small_prime : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit | exact GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit | (intros; apply GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwise
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwise
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem clusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  intro n th j hC t ht
  obtain ⟨F, sp, hF, huniq⟩ := hC
  obtain ⟨x, ⟨hxF, hxt⟩, -⟩ := huniq t ht
  obtain ⟨hthx, hspj, -, -, hbetween, hbefore⟩ := hF x hxF
  rcases hxt with rfl | rfl
  · exact Or.inl hbefore
  · by_cases hsp0 : sp x = 0
    · left
      rw [hsp0, Nat.cast_zero, add_zero]
      exact hbefore
    · right
      refine ⟨sp x, Nat.one_le_iff_ne_zero.2 hsp0, hspj, by simpa using hthx, fun k hk1 hk2 hkd => ?_⟩
      rcases lt_or_gt_of_ne hkd with hlt | hgt
      · have e : x + (sp x : ZMod n) - k = x + ((sp x - k : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hlt.le]
          ring
        rw [e]
        exact hbetween (sp x - k) (by omega) (by omega)
      · have e : x + (sp x : ZMod n) - k = x - ((k - sp x : ℕ) : ZMod n) := by
          rw [Nat.cast_sub hgt.le]
          ring
        rw [e]
        exact hbefore (k - sp x) (by omega) (by omega)

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwiseStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicWordMarkedClusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨ ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  first | exact @GlobalTheory.HTW.Rec.clusters_letterwise | exact GlobalTheory.HTW.Rec.clusters_letterwise | (intros; apply GlobalTheory.HTW.Rec.clusters_letterwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScale
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointB_of_large : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  intro eps ez C₂ A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.HTW.roomy_of_large eps (max 100 (2 * C₂)) A heps (le_max_left _ _)
  obtain ⟨x2, h2⟩ := GlobalTheory.InertPrimeEleven.eleven_le ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW hE hZ hA hx hadm hfont hJ i hin hrow r ρ π hPt w hw
  have hR : Roomy L (max 100 (2 * C₂)) := h1 D L Pm hE hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i :=
    h2 D L (D.nd.l i) hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L _ HW i r ρ π w hw Cx hG hR hadm hfont hJ hPt hin.1 hin.2.1 hin.2.2.1
  have hWB : WordsB L (D.nd.l i) C₂ (recWord L (liftIdx D i) ε g) := by
    refine GlobalTheory.T.twistedDualSizeWord_long_orbit_small_prime L Pm _ C₂ _ ε g _ (D.nd.l i) hR hg (le_max_right _ _) h11 hrow.1 ?_
    rw [Prod.snd_inv, orderOf_inv]
    exact hrow.lt_orderOf
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hin.ne_two hB, h11, hWB.j_lt, hWB.par, ?_⟩
  intro t ht
  exact GlobalTheory.T.cyclicWordMarkedClusters_letterwise _ _ hWB.clusters t ht

end GlobalTheory.HTW.RecS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScaleStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  first | exact @GlobalTheory.HTW.RecS.jointB_of_large | exact GlobalTheory.HTW.RecS.jointB_of_large | (intros; apply GlobalTheory.HTW.RecS.jointB_of_large <;> assumption)
end
