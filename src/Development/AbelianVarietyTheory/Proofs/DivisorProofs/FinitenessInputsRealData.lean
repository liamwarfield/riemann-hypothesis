module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftMemCuspFormMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProducts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMassLowerBoundOfOrthonormalLatticeFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftScalarOfInnerProductFormulaBis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRank
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRowAnti

variable {D : D7}

theorem lam_step (τ : D.what₂.Tau) (n : ℕ) (hn : n + 1 < D.R.r) :
    Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1) + 1 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n := by
  have h := Formalism.L2.NTheta.lamAt_lt (D.hc τ) n hn
  obtain ⟨a, ha⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (n + 1)
  obtain ⟨b, hb⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  rw [ha, hb] at h ⊢
  have : a < b := by exact_mod_cast h
  have : a + 1 ≤ b := this
  exact_mod_cast this

theorem pq_eq (i : Fin D.R.m) (ρ : D.what₂.Tau) : pW D i ρ + qW D i ρ = D.R.r := by
  have h := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2] at h
  exact h

theorem aPl_anti (i : Fin D.R.m) (p : ℕ) (τ : D.what₂.Tau) (hp : p ≤ D.R.r) : Antitone (aPl D i p τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aPl
  by_cases h1 : n + 1 < p
  · rw [if_pos h1, if_pos (by omega : n < p)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have := lam_step τ n (by omega)
    push_cast
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

theorem aMi_anti (i : Fin D.R.m) (p q : ℕ) (τ : D.what₂.Tau) (hpq : p + q = D.R.r) : Antitone (aMi D i p q τ) := by
  refine antitone_nat_of_succ_le fun n => ?_
  unfold aMi
  by_cases h1 : n + 1 < q
  · rw [if_pos h1, if_pos (by omega : n < q)]
    apply Int.toNat_le_toNat
    apply Int.floor_le_floor
    have e1 : p + (q - n) - 1 = (p + (q - (n + 1)) - 1) + 1 := by omega
    have := lam_step τ (p + (q - (n + 1)) - 1) (by omega)
    rw [e1]
    have e2 : ((q - n : ℕ) : ℚ) = ((q - (n + 1) : ℕ) : ℚ) + 1 := by
      rw [show q - n = (q - (n + 1)) + 1 by omega]; push_cast; ring
    rw [e2]
    linarith
  · rw [if_neg h1]; exact Nat.zero_le _

end GlobalTheory.LowRowAnti

open GlobalTheory.LowRowAnti in
theorem GlobalTheory.LowRow.lift_rows_antitone : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau),
    Antitone (aPlAt D i σ ρ) ∧ Antitone (aMiAt D i σ ρ) ∧ pW D i ρ + qW D i ρ = (Wc D i).rank ∧
      (Wc D i).rank ≤ (Vc D i).rank := by
  intro D i σ ρ
  have hpq := pq_eq (D := D) i ρ
  refine ⟨?_, ?_, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i ρ, ?_⟩
  · exact aPl_anti i _ _ (by omega)
  · exact aMi_anti i _ _ _ hpq
  · rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact r_le_V i
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRankStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftRows_antitone_signature_rank : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), Antitone (aPlAt D i σ ρ) ∧ Antitone (aMiAt D i σ ρ) ∧ pW D i ρ + qW D i ρ = (Wc D i).rank ∧ (Wc D i).rank ≤ (Vc D i).rank := by
  first | exact @GlobalTheory.LowRow.lift_rows_antitone | exact GlobalTheory.LowRow.lift_rows_antitone | (intros; apply GlobalTheory.LowRow.lift_rows_antitone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelParameterDecreasingHalfIntegralWidth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelParameterDecreasingHalfIntegralWidth
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ParWidth

theorem mem_holPar_kapW {Rk : Ranks} (h : HCParam Rk) (p q : ℕ) (hpq : Odd (p + q)) {x : ℚ} {b : Bool}
    (hx : (x, b) ∈ Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    ∃ n < p + q, x = Formalism.L2.NTheta.lamAt h n := by
  unfold Formalism.L2.NTheta.holPar at hx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx
  have e := Formalism.L2.NTheta.holEnt_kapW h p q hpq a
  have hx' : x = Formalism.L2.NTheta.holEnt p q (Formalism.L2.NTheta.kapW h p q) a := (congrArg Prod.fst ha).symm
  rcases a with i | c
  · exact ⟨i, by omega, hx'.trans (by simpa using e)⟩
  · exact ⟨p + c, by omega, hx'.trans (by simpa using e)⟩

theorem lamAt_anti {Rk : Ranks} (h : HCParam Rk) {n n' : ℕ} (hnn : n ≤ n') (hn : n' < Rk.r) :
    Formalism.L2.NTheta.lamAt h n' ≤ Formalism.L2.NTheta.lamAt h n := by
  have mono : ∀ d : ℕ, n + d < Rk.r → Formalism.L2.NTheta.lamAt h (n + d) ≤ Formalism.L2.NTheta.lamAt h n := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (n + d) (by omega)).le.trans (ih (by omega))
  have := mono (n' - n) (by omega)
  rwa [show n + (n' - n) = n' by omega] at this

theorem lamAt_b {Rk : Ranks} (h : HCParam Rk) (c : ℕ) (hc : c < Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

theorem le_toNat_floor (x : ℚ) : x ≤ ((⌊x⌋.toNat : ℕ) : ℚ) + 1 := by
  have h1 := Int.lt_floor_add_one x
  have h2 : ((⌊x⌋ : ℤ) : ℚ) ≤ (((⌊x⌋.toNat : ℕ) : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
  rw [Int.cast_natCast] at h2
  linarith

end GlobalTheory.LowRow.ParWidth

namespace GlobalTheory.LowRow.ParWidth

theorem width_le (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) 0 - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) (D.R.r - 1) ≤
      (degAt D i σ ρ : ℚ) + D.R.nV + 1 := by
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hp : pW D i ρ = D.R.k + i := by simp only [pW, hsig, Ranks.sigW]; omega
  have hq : qW D i ρ = D.R.m - (i + 1) := by simp only [qW, hsig, Ranks.sigW]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  set h := D.hc (lab σ ρ) with hh
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hnV : (D.R.nV : ℚ) = (D.R.k : ℚ) + D.R.m - 1 + D.R.t := by
    simp only [Ranks.nV, Ranks.r]; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring

  have hP0 : (aPlAt D i σ ρ 0 : ℚ) + 1 ≥
      Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - (0 + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    have := le_toNat_floor (Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - ((0 : ℕ) + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2)
    unfold aPlAt aPl
    rw [hp, if_pos (by omega)]
    simpa using this
  have hdeg : (aPlAt D i σ ρ 0 : ℚ) + (if 0 < qW D i ρ then (aMiAt D i σ ρ 0 : ℚ) else 0) ≤ degAt D i σ ρ := by
    have e1 : aPlAt D i σ ρ 0 ≤ ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n :=
      Finset.single_le_sum (f := aPlAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    have e2 : (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) ≤ ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n := by
      split_ifs with hq0
      · exact Finset.single_le_sum (f := aMiAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hq0)
      · exact Nat.zero_le _
    have e3 := Nat.add_le_add e1 e2
    unfold degAt
    have : ((aPlAt D i σ ρ 0 + (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) : ℕ) : ℚ) ≤
        ((∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n : ℕ) : ℚ) := by
      exact_mod_cast e3
    push_cast at this
    split_ifs at this ⊢ <;> simpa using this
  by_cases hq0 : (i : ℕ) + 1 < D.R.m
  · have hqpos : 0 < qW D i ρ := by rw [hq]; omega
    rw [if_pos hqpos] at hdeg
    have hM0 : (aMiAt D i σ ρ 0 : ℚ) + 1 ≥
        -(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
      have := le_toNat_floor (-(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2))
      unfold aMiAt aMi
      rw [hp, hq, if_pos (by omega), show D.R.k + ↑i + (D.R.m - (↑i + 1) - 0) - 1 = D.R.r - 1 by omega]
      simpa using this
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    have c2 : (((D.R.m - (i + 1) : ℕ) : ℚ)) = D.R.m - (i : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [c1] at hP0
    rw [c2] at hM0
    rw [hnV]
    linarith
  · have him : (i : ℕ) = D.R.m - 1 := by omega
    rw [if_neg (by rw [hq]; omega), add_zero] at hdeg
    have hb : Formalism.L2.NTheta.lamAt h (D.R.r - 1) = -h.b i := by
      rw [show D.R.r - 1 = D.R.k - 1 + (i : ℕ) by omega, lamAt_b h i i.2]
    have hg := h.gap_be i
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    rw [c1] at hP0
    have hmi : (i : ℚ) = D.R.m - 1 := by
      rw [him, Nat.cast_sub (by omega)]; simp
    rw [hnV, hb]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith

end GlobalTheory.LowRow.ParWidth


open GlobalTheory.LowRow.ParWidth in
theorem GlobalTheory.LowRow.lam_par_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _hC i σ s hσ ρ
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hσ.2
  have hat : labE σ (lab σ ρ) = tauE D ρ := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  obtain ⟨hanti, qv, hqv, hS⟩ := (R.MW i σ).enum ρ
  have hpar : parAt (Wc D i) σ ρ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) := if_pos hat
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hr : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    rw [hsig]; simp only [Ranks.sigW, Ranks.r]; omega
  have hrodd : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hodd : Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := hr ▸ hrodd
  have hent : ∀ a, ∃ n < D.R.r, (R.MW i σ).lam ρ a = ((Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n : ℚ) : ℝ) := by
    intro a
    have hmem : (qv a, (R.MW i σ).ε ρ a) ∈ parAt (Wc D i) σ ρ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hpar] at hmem
    obtain ⟨n, hn, e⟩ := mem_holPar_kapW _ _ _ hodd hmem
    exact ⟨n, hr ▸ hn, by rw [hqv a, e]⟩
  have hrank : (Wc D i).rank = D.R.r := by
    rw [← hr]; exact (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _).symm
  refine ⟨hanti, fun a => ?_, fun a b => ?_⟩
  · obtain ⟨n, -, e⟩ := hent a
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) n
    obtain ⟨w, hw⟩ := hrodd
    refine ⟨z - w, ?_⟩
    rw [e, hz, hrank, hw]
    push_cast
    ring
  · obtain ⟨n, hn, ea⟩ := hent a
    obtain ⟨n', hn', eb⟩ := hent b
    have hW := width_le D i σ ρ
    have l1 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n) hn
    have l2 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n') hn'
    have u1 := lamAt_anti (D.hc (lab σ ρ)) (show n ≤ D.R.r - 1 by omega) (by omega)
    have u2 := lamAt_anti (D.hc (lab σ ρ)) (show n' ≤ D.R.r - 1 by omega) (by omega)
    have key : |Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n'| ≤
        (degAt D i σ ρ : ℚ) + D.R.nV + 3 := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    rw [ea, eb, ← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelParameterDecreasingHalfIntegralWidthStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  first | exact @GlobalTheory.LowRow.lam_par_width | exact GlobalTheory.LowRow.lam_par_width | (intros; apply GlobalTheory.LowRow.lam_par_width <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDua
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDua
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

section Perm

variable {p q n : ℕ} {ε : Fin n → Bool}

def permFrame (e : Fin p ⊕ Fin q ≃ Fin n) : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
  (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix id e.symm

theorem mul_permFrame (e : Fin p ⊕ Fin q ≃ Fin n) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    X * permFrame e = X.submatrix id e.symm := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply]

theorem permFrame_conjTranspose_mul (e : Fin p ⊕ Fin q ≃ Fin n) (Y : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) :
    (permFrame e)ᴴ * Y = Y.submatrix e.symm id := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

theorem permFrame_herm {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e) :
    (permFrame e)ᴴ * Formalism.UG.Jpq p q * permFrame e = Formalism.REAL.Jm ε := by
  rw [Matrix.mul_assoc, mul_permFrame, permFrame_conjTranspose_mul, ← h.reindex_Jpq, Matrix.reindex_apply,
    Matrix.submatrix_submatrix]
  rfl

theorem frameInv_permFrame {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e)
    (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    frameInv ε (permFrame e) * X * permFrame e = Matrix.reindex e e X := by
  have : frameInv ε (permFrame e) * X * permFrame e =
      Formalism.REAL.Jm ε * ((permFrame e)ᴴ * (Formalism.UG.Jpq p q * X * permFrame e)) := by
    simp only [frameInv, Matrix.mul_assoc]
  rw [this, mul_permFrame, permFrame_conjTranspose_mul, Matrix.submatrix_submatrix,
    show (e.symm ∘ id : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    show (id ∘ e.symm : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    ← Matrix.submatrix_mul_equiv (Formalism.UG.Jpq p q) X e.symm e.symm e.symm,
    ← Matrix.reindex_apply, h.reindex_Jpq, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul,
    Matrix.reindex_apply]

end Perm

theorem map_frameEquiv_cd (cd : CDHaar) {p q n : ℕ} {ε : Fin n → Bool} (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) :
    (cd.cd p q).map (frameEquiv B hB hn) = (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
  classical
  let e₀ : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let ε₀ : Fin n → Bool := fun i => (e₀.symm i).isLeft
  have h₀ : Sorts ε₀ e₀ := ⟨fun i => by simp [ε₀], fun j => by simp [ε₀]⟩
  have hC : (B.submatrix e₀.symm id)ᴴ * Formalism.REAL.Jm ε₀ * B.submatrix e₀.symm id = Formalism.REAL.Jm ε := by
    rw [← h₀.reindex_Jpq, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hB]
    rfl
  have hcount : Nat.card {a // ε a = true} = p := (GlobalTheory.SignCount.card_true_eq _ hC).symm.trans h₀.card_true
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  have hP : P = p := he.card_true.symm.trans hcount
  have hQ : Q = q := by have := Sorts.add_eq e; omega
  subst hP hQ
  have hBp := permFrame_herm he
  have hfun : (frameEquiv (permFrame e) hBp hn : UpqT P Q → Formalism.REAL.UJ ε) = he.equiv := funext fun b =>
    umat_injective (by rw [umat_frameEquiv, frameInv_permFrame he, he.umat_equiv])
  have hmap0 : (cd.cd P Q).map (frameEquiv (permFrame e) hBp hn) =
      (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
    rw [hfun]
    ext A hA
    rw [Measure.map_apply he.measurable_equiv hA, ← he.set_eq]
    exact (cdScaleIs_trueScale cd n ε P Q e he.1 he.2 A hA).symm
  exact map_frameEquiv hBp hB hn (cd.cd P Q) _ hmap0

end GlobalTheory.LowRow.CompactDualCoef

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

theorem inv_integral_coef_sq : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  intro hHC cd D W S M Fr hFr hsig ρ hanti hhalf w hw
  classical
  haveI : BorelSpace (Upq W ρ) := ⟨rfl⟩
  have hn := hsig ρ
  have hmap := map_frameEquiv_cd cd _ (frame_herm M hFr ρ) hn
  have hme : MeasurableEmbedding (frameEquiv _ (frame_herm M hFr ρ) hn) :=
    (frameEquiv _ (frame_herm M hFr ρ) hn).toHomeomorph.measurableEmbedding
  have hk : (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) =
      (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘ frameEquiv _ (frame_herm M hFr ρ) hn :=
    funext fun b => by simp only [Function.comp_apply, rep_realMat M hFr ρ hn b]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hpr := hHC cd (trueScale cd) (cdScaleIs_trueScale cd) W.rank (M.ε ρ) (M.lam ρ) ⟨hanti, hhalf⟩ (M.H ρ)
    (M.σ ρ) w (M.ds ρ) hw0
  rw [hw, one_pow, one_div] at hpr
  have hpos : 0 < (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) /
      ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
      (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    · exact abs_pos.2 (sub_ne_zero.2 (hanti.injective.ne (ne_of_lt (Finset.mem_filter.1 hb).2)))
    · have := (Finset.mem_filter.1 hb).2
      exact sub_pos.2 (by exact_mod_cast this)
  have hint : Integrable (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2)
      ((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) := by
    by_contra hni
    rw [integral_undef hni, _root_.inv_zero] at hpr
    exact hpos.ne hpr
  rw [← hmap] at hint
  rw [hk]
  refine ⟨hme.integrable_map_iff.1 hint, ?_⟩
  rw [show (∫ b, ((fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘
      frameEquiv _ (frame_herm M hFr ρ) hn) b ∂(cd.cd _ _)) =
      ∫ g, ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2 ∂((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) by
    rw [← hmap, hme.integral_map]; rfl]
  exact hpr

end GlobalTheory.LowRow.CompactDualCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDuaStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | exact GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | (intros; apply GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem volU_ge_inv_pow_of_formalDeg (r : ℕ) (hr : 1 ≤ r) :
    (((r : ℝ) ^ r)⁻¹) ^ r ≤ ReciprocityTheory.ChartRestriction.DS.volU r := by
  unfold ReciprocityTheory.ChartRestriction.DS.volU
  have hrpos : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  rw [show (((r : ℝ) ^ r)⁻¹) ^ r = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ by
    rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have hfac : (i.factorial : ℝ) ≤ (r : ℝ) ^ r := by
      have h1 : i.factorial ≤ r.factorial := Nat.factorial_le hi'.le
      have h2 : r.factorial ≤ r ^ r := Nat.factorial_le_pow r
      exact_mod_cast h1.trans h2
    have hfpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hpi : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by
      have : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
      linarith
    calc ((r : ℝ) ^ r)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := inv_anti₀ hfpos hfac
      _ = 1 / (i.factorial : ℝ) := by rw [one_div]
      _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by gcongr

theorem formalDeg_div_volU_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  intro r n d lam hr hn hd hlam hbd
  set P : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b| with hPdef
  set D : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) with hDdef
  set V : ℝ := ReciprocityTheory.ChartRestriction.DS.volU r with hVdef
  set M : ℝ := d + n + 3 with hMdef
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hVlow := volU_ge_inv_pow_of_formalDeg r hr
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  have hD1 : 1 ≤ D := by
    have : (∏ _a : Fin r, ∏ _b ∈ Finset.univ.filter (fun b : Fin r => _a < b), (1 : ℝ)) ≤ D := by
      apply Finset.prod_le_prod₀
      · intro a _; positivity
      · intro a _
        apply Finset.prod_le_prod₀
        · intro b _; positivity
        · intro b hb
          have hab : a < b := (Finset.mem_filter.mp hb).2
          have : (a : ℕ) + 1 ≤ (b : ℕ) := hab
          have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast this
          linarith
    simpa using this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hPle : P ≤ M ^ (r * r) := by
    have : P ≤ ∏ _a : Fin r, M ^ r := by
      apply Finset.prod_le_prod₀
      · intro a _; exact Finset.prod_nonneg (fun b _ => abs_nonneg _)
      · intro a _
        calc (∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|)
            ≤ ∏ _b ∈ Finset.univ.filter (fun b : Fin r => a < b), M :=
              Finset.prod_le_prod₀ (fun b _ => abs_nonneg _) (fun b _ => hbd a b)
          _ = M ^ (Finset.univ.filter (fun b : Fin r => a < b)).card := Finset.prod_const _
          _ ≤ M ^ r := by
              apply pow_le_pow_right₀ hM1
              calc (Finset.univ.filter (fun b : Fin r => a < b)).card ≤ (Finset.univ : Finset (Fin r)).card :=
                    Finset.card_filter_le _ _
                _ = r := by simp
    calc P ≤ ∏ _a : Fin r, M ^ r := this
      _ = M ^ (r * r) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hVinv : V⁻¹ ≤ (r : ℝ) ^ (r * r) := by
    have h := inv_anti₀ (by positivity) hVlow
    rw [inv_pow, inv_inv, ← pow_mul] at h
    exact h
  have hQpos : 0 < P / D / V := by positivity
  have hQle : P / D / V ≤ (M * r) ^ (r * r) := by
    calc P / D / V ≤ P / V := by
          gcongr
          exact div_le_self hPpos.le hD1
      _ = P * V⁻¹ := div_eq_mul_inv _ _
      _ ≤ M ^ (r * r) * (r : ℝ) ^ (r * r) := by
          apply mul_le_mul hPle hVinv (by positivity) (by positivity)
      _ = (M * r) ^ (r * r) := (mul_pow _ _ _).symm
  refine ⟨hVpos, div_pos hPpos hDpos, ?_⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hMn : M ≤ n * (d + 2) := by
    rw [hMdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n - 1) hd]
  have hr2 : (r : ℝ) ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 := by nlinarith
  have hX : M * r ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by
    calc M * r ≤ (n * (d + 2)) * (2 * Real.sqrt 2 * (r : ℝ) ^ 2) :=
          mul_le_mul hMn hr2 (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by ring
  have hMr : 0 < M * r := by positivity
  calc Real.log (P / D / V) ≤ Real.log ((M * r) ^ (r * r)) := Real.log_le_log hQpos hQle
    _ = ((r * r : ℕ) : ℝ) * Real.log (M * r) := Real.log_pow _ _
    _ = (r : ℝ) ^ 2 * Real.log (M * r) := by push_cast; ring
    _ ≤ (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
        gcongr
    _ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by linarith

end GlobalTheory.LowRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBoundStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  first | exact @GlobalTheory.LowRow.formalDeg_div_volU_log_bound | exact GlobalTheory.LowRow.formalDeg_div_volU_log_bound | (intros; apply GlobalTheory.LowRow.formalDeg_div_volU_log_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandra
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem formalDegreeUpperC_of_hypotheses : GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FormalDegreeUpperC R F := by
  intro hp D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  obtain ⟨hcore, -, hσ, -⟩ := hL
  have h5 : GlobalTheory.Core5 R F := ⟨hcore.lev, hcore.grp, hcore.fam, hcore.models, hcore.thP⟩
  intro Fr hFr ρ mR hmR e he
  dsimp only
  obtain ⟨hanti, hhalf, hwid⟩ := GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width R F h5 i σ s hσ ρ
  have hsig : ∀ ρ', ((Wc D i).sig (tauE D ρ')).1 + ((Wc D i).sig (tauE D ρ')).2 = (Wc D i).rank :=
    fun ρ' => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ').2.2.1
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have h1 : 1 ≤ (Wc D i).rank := by
    rw [hrk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]; omega
  have h3 : 3 ≤ D.R.nV := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m; have := D.R.three_m_lt_t
    simp only [Formalism.BasicNotions.Ranks.nV, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨hint, hinv⟩ := GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual hp D.cd (Wc D i) _ (R.MW i σ) Fr hFr hsig ρ hanti hhalf _ he
  have hm := GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual D.cd _ _ mR hmR
  rw [hsig ρ] at hm
  obtain ⟨hvol, hQpos, hlog⟩ := GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound (Wc D i).rank D.R.nV (degAt D i σ ρ) ((R.MW i σ).lam ρ) h1 h3
    (by positivity) hanti hwid
  have e1 : (((Wc D i).rank : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  rw [e1] at hlog
  subst hm
  refine ⟨hint.smul_measure ENNReal.ofReal_ne_top, ?_, ?_⟩
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul]
    refine mul_pos hvol ?_
    have : 0 < (∫ b : Upq (Wc D i) ρ, ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(D.cd.cd _ _))⁻¹ := by
      rw [hinv]; exact hQpos
    exact inv_pos.mp this
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul, mul_inv, hinv, mul_comm, ← div_eq_mul_inv]
    exact hlog

end GlobalTheory.LowRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandraStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegreeRealPlaceUpperBound_of_harishChandra : GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FormalDegreeUpperC R F := by
  first | exact @GlobalTheory.LowRow.formalDegreeUpperC_of_hypotheses | exact GlobalTheory.LowRow.formalDegreeUpperC_of_hypotheses | (intros; apply GlobalTheory.LowRow.formalDegreeUpperC_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteZetaIntegralEulerProductOfPartialL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteZetaIntegralEulerProductOfPartialL
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ZetaProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_fin_getD_list (f : ℂˣ → ℂ) : ∀ l : List ℂˣ, ∏ a : Fin l.length, f (l.getD a 1) = (l.map f).prod
  | [] => by simp
  | b :: l => by
    rw [List.length_cons, Fin.prod_univ_succ]
    simp [prod_fin_getD_list f l]

theorem prod_fin_getD (m : Multiset ℂˣ) {n : ℕ} (hn : m.card = n) (f : ℂˣ → ℂ) :
    ∏ a : Fin n, f (m.toList.getD a 1) = (m.map f).prod := by
  have hl : m.toList.length = n := (Multiset.length_toList m).trans hn
  subst hl
  rw [prod_fin_getD_list]
  conv_rhs => rw [← Multiset.coe_toList m]
  rw [Multiset.map_coe, Multiset.prod_coe]

variable {D : D7}


open Classical in
def zetaParams (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (cμ : (AE D)ˣ →* Circle) :
    HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ := fun w a =>
  if OffS D S w then
    (((B w).toList.getD a 1 : ℂˣ) : ℂ) * ((((GlobalTheory.LFun.val cμ)⁻¹ w : ℂˣ)) : ℂ) * GlobalTheory.LFun.npow w (-((1 + (D.R.t : ℂ)) / 2))
  else 0

theorem re_neg_half : (-((1 + (D.R.t : ℂ)) / 2)).re = -((1 + (D.R.t : ℝ)) / 2) := by
  rw [show -((1 + (D.R.t : ℂ)) / 2) = ((-((1 + (D.R.t : ℝ)) / 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

theorem norm_zetaParams_le {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.r) :
    ‖zetaParams S B cμ w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2) := by
  unfold zetaParams
  split_ifs with hw
  · have ha : (a : ℕ) < (B w).toList.length := by rw [Multiset.length_toList, hcard w hw]; exact a.2
    have hβ : (B w).toList.getD a 1 ∈ B w := by
      rw [List.getD_eq_getElem _ _ ha]
      exact Multiset.mem_toList.1 (List.getElem_mem ha)
    have hN : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
      have := two_le_absNorm w
      linarith
    rw [norm_mul, norm_mul, Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one, mul_one,
      GlobalTheory.LFun.norm_npow, re_neg_half, sub_eq_add_neg, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_right (hb w hw _ hβ) (Real.rpow_nonneg hN.le _)
  · rw [norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem eulerOff_zetaParams {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) :
    eulerOff D S (zetaParams S B cμ) = GlobalTheory.LFun.LSD D S B cμ ((1 + (D.R.t : ℂ)) / 2) := by
  set x := zetaParams S B cμ with hxdef
  have hx := norm_zetaParams_le cμ hcard hb
  obtain ⟨h1, h2, -⟩ := sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by
    refine (hx _ _).trans ?_
    have ht : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have := two_le_absNorm a.1.1
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hm : Multipliable fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ := by
    have := multipliable_one_add_of_summable (f := fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ - 1)
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (h2.mul_left 2))
    · simpa using this
    · have hx2 : ‖x p.1.1 p.2‖ ≤ 1 / 2 := h1 p
      have h3 : 1 / 2 ≤ ‖1 - x p.1.1 p.2‖ := by
        have := norm_sub_norm_le (1 : ℂ) (x p.1.1 p.2)
        rw [norm_one] at this
        linarith
      have hne : 1 - x p.1.1 p.2 ≠ 0 := fun h => by rw [h, norm_zero] at h3; linarith
      have e : (1 - x p.1.1 p.2)⁻¹ - 1 = x p.1.1 p.2 * (1 - x p.1.1 p.2)⁻¹ := by
        field_simp
        ring
      have h4 : ‖1 - x p.1.1 p.2‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
      rw [e, norm_mul, norm_inv]
      nlinarith [norm_nonneg (x p.1.1 p.2)]
  have hp := hm.hasProd.prod_fiberwise fun b => hasProd_fintype _
  rw [eulerOff, ← hp.tprod_eq]
  show _ = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2)
  rw [GlobalTheory.LFun.eulerProd]
  let e : {w // OffS D S w} ≃ {w // w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))} :=
    Equiv.subtypeEquivRight fun w => (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff S w).trans (by simp [GlobalTheory.LFun.above])
  rw [← e.tprod_eq]
  refine tprod_congr fun w => ?_
  show _ = GlobalTheory.LFun.locL _ w.1 _
  rw [GlobalTheory.LFun.locL_twist, ← prod_fin_getD (B w.1) (hcard w.1 w.2)]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [hxdef, zetaParams, if_pos w.2]

end GlobalTheory.LowRow.ZetaProd

namespace GlobalTheory.LowRow

theorem finiteZetaC_of_finiteZetaL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    FiniteZetaL R F → FiniteZetaC R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨B, hsys, hb, -, hsum⟩ := hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  have hcard : ∀ w, OffS D (finS R t) w → (B w).card = D.R.r := fun w hw => by
    have hv : w.under (𝓞 D.host.F) ∉ ((finS R t : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
      simpa using (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff _ w).1 hw
    rcases hsys _ hv w rfl with ⟨-, h, -⟩ | ⟨-, τ, ϖ, α, -, -, h, -⟩
    · exact h
    · rw [h]
      exact GlobalTheory.LGrp.card_bcParam _ α
  refine ⟨ZetaProd.zetaParams (finS R t) B cμ, ZetaProd.norm_zetaParams_le cμ hcard hb, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  rw [ZetaProd.eulerOff_zetaParams cμ hcard hb]
  exact hsum U₁ h₁ U₂ h₂ v₁ v₂

end GlobalTheory.LowRow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteZetaIntegralEulerProductOfPartialLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F → FiniteZetaC R F := by
  first | exact @GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL | exact GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL | (intros; apply GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowAdel

theorem deltaNorm_all (D : D7) : DeltaNorm D := by
  intro i σ
  have h := GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ)
    (fun ρ => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.2.1.le)
    (fun ρ => by
      obtain ⟨-, -, hpq, hWV⟩ := GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ
      exact ⟨by omega, by omega⟩)
    (fun ρ => ⟨(GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).1, (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.1⟩)
  simpa [deltaAtEmb] using h

end GlobalTheory.LowRowAdel
