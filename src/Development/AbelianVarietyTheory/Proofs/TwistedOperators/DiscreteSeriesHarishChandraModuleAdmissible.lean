module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAdaptedBasisUnitarySubstitution
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsRealPlaceActAsFockPolynomials
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelParamShiftedWeightOfCoverDisc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelIsometryUnitHighestVectorIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModelsOfCoversRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockJointHarmonicVectorsIffPolynomials
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondencePairingLawOfTensorLaw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIntegralModelOfCover
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatio
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapExistsOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapHarmonicOfDiscreteSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfHarishChandra
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfHarishChandra
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchRec

theorem itLine_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D :=
  GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries

end GlobalTheory.ArchRec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfHarishChandraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiners_proportional_of_harishChandra : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  first | exact @GlobalTheory.ArchRec.itLine_of_hypotheses | exact GlobalTheory.ArchRec.itLine_of_hypotheses | (intros; apply GlobalTheory.ArchRec.itLine_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splittingHeckeChar_exists_archimedeanExponent : ∀ (D : D7) (θ : InfFam D) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau), IsInfFam θ → IsHeckeChar D χ → ResEta D χ n → ∃ a : ℚ, HasInfExp D χ τ a := by
  first | exact @GlobalTheory.SplitCharExp.exists_hasInfExp | exact GlobalTheory.SplitCharExp.exists_hasInfExp | (intros; apply GlobalTheory.SplitCharExp.exists_hasInfExp <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteSourcePairCentredBlockParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteSourcePairCentredBlockParameters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

open Formalism.L2.NTheta

namespace GlobalTheory.ArchRec.ParPair

section HC

variable {R : Ranks} (h : HCParam R)

theorem lamAt_tail (n : ℕ) (c : Fin R.m) (hn : n + 1 = R.k + c) : lamAt h n = -h.b c := by
  have hk := R.m_add_three_le_k
  have hc := c.2
  unfold lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

theorem lamAt_head (n : Fin (R.k - 1)) : lamAt h n = h.v n := by
  unfold lamAt
  rw [dite_eq_left n.2]

theorem lamAt_lt_of_lt {a b : ℕ} (hab : a < b) (hb : b < R.r) : lamAt h b < lamAt h a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have := lamAt_add_add_le h (d + 1) a (by omega)
  rw [← add_assoc] at this
  have h0 : (0 : ℚ) ≤ d := by positivity
  push_cast at this
  linarith

theorem lamAt_le_of_le {a b : ℕ} (hab : a ≤ b) (hb : b < R.r) : lamAt h b ≤ lamAt h a := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  · exact (lamAt_lt_of_lt h hab hb).le

variable (i : Fin R.m)

def al : List ℚ := (List.range (R.k + i)).map fun n => lamAt h n + h.e i

def de : List ℚ := (List.range (R.m - (i + 1))).map fun c => lamAt h (R.k + i + c) + h.e i

theorem mem_al {x : ℚ} : x ∈ al h i ↔ ∃ n < R.k + i, lamAt h n + h.e i = x := by
  simp only [al, List.mem_map, List.mem_range]

theorem mem_de {x : ℚ} : x ∈ de h i ↔ ∃ c < R.m - (i + 1), lamAt h (R.k + i + c) + h.e i = x := by
  simp only [de, List.mem_map, List.mem_range]

theorem length_al : (al h i).length = R.k + i := by simp [al]

theorem length_de : (de h i).length = R.m - (i + 1) := by simp [de]

theorem le_of_mem_al {x : ℚ} (hx : x ∈ al h i) : h.e i - h.b i ≤ x := by
  obtain ⟨n, hn, rfl⟩ := (mem_al h i).1 hx
  have hk := R.m_add_three_le_k
  have hi := i.2
  have h1 := lamAt_tail h (R.k + i - 1) i (by omega)
  have h2 := lamAt_le_of_le h (a := n) (b := R.k + i - 1) (by omega) (by unfold Ranks.r; omega)
  linarith

theorem le_of_mem_de {x : ℚ} (hx : x ∈ de h i) :
    ∃ hi : i.1 + 1 < R.m, x ≤ h.e i - h.b ⟨i.1 + 1, hi⟩ := by
  obtain ⟨c, hc, rfl⟩ := (mem_de h i).1 hx
  have hk := R.m_add_three_le_k
  have hi : i.1 + 1 < R.m := by omega
  refine ⟨hi, ?_⟩
  have h1 := lamAt_tail h (R.k + i) ⟨i.1 + 1, hi⟩ (by simp only; omega)
  have h2 := lamAt_le_of_le h (a := R.k + i) (b := R.k + i + c) (by omega) (by unfold Ranks.r; omega)
  linarith

theorem al_far {x : ℚ} (hx : x ∈ al h i) : ((R.t : ℚ) + 3) / 2 ≤ x :=
  (h.gap_be i).trans (le_of_mem_al h i hx)

theorem de_far {x : ℚ} (hx : x ∈ de h i) : ((R.t : ℚ) + 3) / 2 ≤ -x := by
  obtain ⟨hi, hx⟩ := le_of_mem_de h i hx
  have := h.gap_eb i hi
  linarith

theorem far {x : ℚ} (hx : x ∈ al h i ++ [] ++ [] ++ de h i) : ((R.t : ℚ) + 3) / 2 ≤ |x| := by
  simp only [List.append_nil, List.mem_append] at hx
  rcases hx with hx | hx
  · exact (al_far h i hx).trans (le_abs_self x)
  · exact (de_far h i hx).trans (neg_le_abs x)

theorem al_pairwise : (al h i).Pairwise (· > ·) := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  unfold al
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b _ hb hab
  have := lamAt_lt_of_lt h hab (by have := List.mem_range.1 hb; unfold Ranks.r; omega)
  show lamAt h b + h.e i < lamAt h a + h.e i
  linarith

theorem de_pairwise : (de h i).Pairwise (· > ·) := by
  have hk := R.m_add_three_le_k
  unfold de
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b _ hb hab
  have := lamAt_lt_of_lt h (a := R.k + i + a) (b := R.k + i + b) (by omega)
    (by have := List.mem_range.1 hb; unfold Ranks.r; omega)
  show lamAt h (R.k + i + b) + h.e i < lamAt h (R.k + i + a) + h.e i
  linarith

theorem hypA : HypA R.t (al h i) [] [] (de h i) := by
  have hk := R.m_add_three_le_k
  have ht : (0 : ℚ) < ((R.t : ℚ) + 3) / 2 := by positivity
  have hp : ∀ x ∈ al h i, 0 < x := fun x hx => ht.trans_le (al_far h i hx)
  have hn : ∀ x ∈ de h i, x < 0 := fun x hx => neg_pos.1 (ht.trans_le (de_far h i hx))
  refine ⟨R.t_odd.pos, by rw [length_al]; omega, al_pairwise h i, List.Pairwise.nil, List.Pairwise.nil,
    de_pairwise h i, ?_, ?_, ?_, ?_, fun x hx => le_trans (by linarith) (far h i hx)⟩
  · simp only [List.append_nil]
    exact List.nodup_append.2 ⟨(al_pairwise h i).imp ne_of_gt, (de_pairwise h i).imp ne_of_gt,
      fun a ha b hb => ((hn b hb).trans (hp a ha)).ne'⟩
  · simpa using hp
  · simpa using hn
  · intro x hx
    simp only [List.append_nil, List.mem_append, mem_al, mem_de] at hx
    obtain ⟨n, rfl⟩ : ∃ n, lamAt h n + h.e i = x := by
      rcases hx with ⟨n, -, hx⟩ | ⟨n, -, hx⟩ <;> exact ⟨_, hx⟩
    obtain ⟨z, hz⟩ := lamAt_int h n
    obtain ⟨e, he⟩ := h.e_int i
    obtain ⟨s, hs⟩ := R.t_odd
    refine ⟨z + e - s - 1, ?_⟩
    rw [hz, he, hs]
    push_cast
    ring

theorem num_bound {n q m N : ℕ} (hn : n ≤ N) (hq : q ≤ m) (hN : 8 * m ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · simp
    · rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq0) (by norm_num)
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hq' : 8 * (q : ℝ) ≤ N := by exact_mod_cast (by omega : 8 * q ≤ N)
  have h2 : 60 * (q : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    have : (8 * (q : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by gcongr
    nlinarith [sq_nonneg (q : ℝ)]
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (q : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) * (60 * (q : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

theorem getD_mem (l : List ℚ) {n : ℕ} (hn : n < l.length) : l.getD n 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hn]
  exact List.getElem_mem hn

theorem gapGe {g : ℚ} (hg : ∀ hi : i.1 + 1 < R.m, g ≤ h.b ⟨i.1 + 1, hi⟩ - h.b i) :
    GapGe (lamA (al h i) [] [] (de h i)) (g : ℝ) := by
  have key : ∀ (a : Fin ((al h i).length + ([] : List ℚ).length)) (b : Fin (([] : List ℚ).length + (de h i).length)),
      g ≤ lamA (al h i) [] [] (de h i) (.inl a) - lamA (al h i) [] [] (de h i) (.inr b) := by
    intro a b
    have ha := le_of_mem_al h i (getD_mem (al h i) (n := a) (by simpa using a.2))
    obtain ⟨hi, hb⟩ := le_of_mem_de h i (getD_mem (de h i) (n := b) (by simpa using b.2))
    have := hg hi
    simp only [lamA, ofBlocks, List.append_nil, List.nil_append]
    linarith
  rintro (a | a) (b | b) hab
  · exact absurd (by simp [sameBlock]) hab
  · exact le_abs.2 (Or.inl (by exact_mod_cast key a b))
  · refine le_abs.2 (Or.inr ?_)
    rw [← Rat.cast_neg, neg_sub]
    exact_mod_cast key b a
  · exact absurd (by simp [sameBlock]) hab

theorem hypG {N : ℕ} (hN : R.rankX' + 1 ≤ N)
    (hg : ∀ hi : i.1 + 1 < R.m, (R.t : ℚ) + 2 * (N : ℚ) ^ 3 + 1 ≤ h.b ⟨i.1 + 1, hi⟩ - h.b i) :
    HypG R.t (al h i) [] [] (de h i) := by
  have G := gapGe h i hg
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hi := i.2
  have ht := R.rank_add_five_le
  unfold Ranks.rankX' Ranks.r at hN
  have h1 : 1 * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (by omega)
  have h2 : R.m * 8 ≤ R.m * R.t := Nat.mul_le_mul_left _ (by omega)
  have ht0 : (0 : ℝ) ≤ R.t := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hl1 := length_al h i
  have hl2 := length_de h i
  refine ⟨fun a b hab => lt_of_lt_of_le ?_ (G a b hab), ?_, fun a b hab => le_trans ?_ (G a b hab)⟩
  · have : (((al h i).length + ([] : List ℚ).length + ([] : List ℚ).length + (de h i).length + R.t : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (by simp only [List.length_nil]; omega)
    have h3 := pow_le_pow_left₀ (by positivity) this 3
    refine h3.trans_lt ?_
    push_cast
    linarith
  · rintro (a | a) (b | b) hab
    · exact absurd (by simp [sameBlock]) hab
    · exact absurd b.2 (by simp)
    · exact absurd a.2 (by simp)
    · exact absurd a.2 (by simp)
  · refine (num_bound (m := R.m) (N := N) (by simp only [List.length_nil]; omega)
      ((min_le_right _ _).trans (by simp only [List.length_nil]; omega)) (by omega)).trans ?_
    push_cast
    linarith

theorem holPar_eq {p q : ℕ} (hp : p = R.k + i) (hq : q = R.m - (i + 1)) :
    holPar p q (kapW h p q) = signed (al h i ++ []) ([] ++ de h i) (-h.e i) := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  have ho : Odd (p + q) := by
    rw [show p + q = R.r by unfold Ranks.r; omega]; exact odd_r R
  subst hp hq
  ext ⟨x, s⟩
  simp only [holPar, holEnt_kapW h _ _ ho, signed, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union,
    List.mem_toFinset, List.mem_map, List.append_nil, List.nil_append, mem_al, mem_de, Prod.mk.injEq]
  constructor
  · rintro ⟨a | a, rfl, rfl⟩
    · exact Or.inl ⟨_, ⟨a, a.2, rfl⟩, by simp, rfl⟩
    · exact Or.inr ⟨_, ⟨a, a.2, rfl⟩, by simp, rfl⟩
  · rintro (⟨_, ⟨n, hn, rfl⟩, rfl, rfl⟩ | ⟨_, ⟨n, hn, rfl⟩, rfl, rfl⟩)
    · exact ⟨.inl ⟨n, hn⟩, by simp, rfl⟩
    · exact ⟨.inr ⟨n, hn⟩, by simp, rfl⟩

theorem mem_al_or_de {x : ℚ} :
    (x ∈ al h i ∨ x ∈ de h i) ↔ (∃ a, h.v a + h.e i = x) ∨ ∃ l, -h.b l + h.e i = x := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  rw [mem_al, mem_de]
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨c, hc, rfl⟩)
    · by_cases h1 : n < R.k - 1
      · exact Or.inl ⟨⟨n, h1⟩, by rw [← lamAt_head]⟩
      · exact Or.inr ⟨⟨n + 1 - R.k, by omega⟩, by rw [← lamAt_tail h n _ (by simp only; omega)]⟩
    · exact Or.inr ⟨⟨i + c + 1, by omega⟩, by rw [← lamAt_tail h (R.k + i + c) _ (by simp only; omega)]⟩
  · rintro (⟨a, rfl⟩ | ⟨l, rfl⟩)
    · exact Or.inl ⟨a, by have := a.2; omega, by rw [lamAt_head]⟩
    · have hl := l.2
      by_cases h1 : l.1 ≤ i.1
      · exact Or.inl ⟨R.k + l - 1, by omega, by rw [lamAt_tail h _ l (by omega)]⟩
      · exact Or.inr ⟨l - i - 1, by omega, by rw [lamAt_tail h _ l (by omega)]⟩

end HC

theorem mem_block {t : ℕ} {x : ℚ} : x ∈ block t ↔ ∃ a < t, ((t : ℚ) - 1) / 2 - (a : ℚ) = x := by
  simp [block]

theorem parDef_eq (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) :
    parDef D i τ = signed (al (D.hc τ) i ++ block D.R.t ++ de (D.hc τ) i) ([] ++ []) (-(D.hc τ).e i - 1 / 2) := by
  ext ⟨x, s⟩
  simp only [parDef, signed, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union,
    List.mem_toFinset, List.mem_map, List.append_nil, List.mem_append, Prod.mk.injEq, List.map_nil, List.not_mem_nil,
    or_false, TPar.block, mem_block, Finset.mem_range, or_right_comm (c := _ ∈ de (D.hc τ) i), mem_al_or_de]
  constructor
  · rintro ⟨_, (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, ha, rfl⟩, rfl, rfl⟩
    · exact ⟨_, Or.inl (Or.inl ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inl (Or.inr ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inr ⟨a, ha, rfl⟩, by ring, rfl⟩
  · rintro ⟨_, (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, ha, rfl⟩, rfl, rfl⟩
    · exact ⟨_, Or.inl (Or.inl ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inl (Or.inr ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inr ⟨a, ha, rfl⟩, by ring, rfl⟩

theorem centred_pair : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ∃ al de : List ℚ, Centred D al [] [] de ∧
    parHol D i τ = signed (al ++ []) ([] ++ de) (-(D.hc τ).e i) ∧
    parDef D i τ = signed (al ++ block D.R.t ++ de) ([] ++ []) (-(D.hc τ).e i - 1 / 2) := by
  intro D i τ
  refine ⟨al (D.hc τ) i, de (D.hc τ) i, ⟨hypA _ i, fun x hx => far _ i hx, ?_⟩, ?_, parDef_eq D i τ⟩
  · rintro ⟨N, hN, hg⟩
    exact hypG _ i hN (hg τ i)
  · have hs : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
      D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
    exact holPar_eq (D.hc τ) i (by rw [hs]; simp [Ranks.sigW]) (by rw [hs]; rfl)

end GlobalTheory.ArchRec.ParPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteSourcePairCentredBlockParametersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteSource_pair_centred_block_parameters : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ∃ al de : List ℚ, Centred D al [] [] de ∧ parHol D i τ = signed (al ++ []) ([] ++ de) (-(D.hc τ).e i) ∧ parDef D i τ = signed (al ++ block D.R.t ++ de) ([] ++ []) (-(D.hc τ).e i - 1 / 2) := by
  first | exact @GlobalTheory.ArchRec.ParPair.centred_pair | exact GlobalTheory.ArchRec.ParPair.centred_pair | (intros; apply GlobalTheory.ArchRec.ParPair.centred_pair <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchRec

theorem isGK_fock (p q r s : ℕ) : IsGK (fockAct1 p q r s) ∧ IsGK (fockAct2 p q r s) := by
  obtain ⟨-, h1, h2, -⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  have hw := GlobalTheory.FockPolGK.pol_locFin_weights p q r s
  exact ⟨⟨h1, fun v => (hw.1 v).1, fun v => (hw.1 v).2⟩, ⟨h2, fun v => (hw.2 v).1, fun v => (hw.2 v).2⟩⟩

theorem discreteSeries_harishChandraModule_admissible {X : ProvA} (h5 : admQ5 X) {p q : ℕ} (hn : 1 ≤ p + q) (lam : Ix p q → ℚ) : AdmGK (X.ds p q lam).HK := by
  exact ((h5 p q hn).1 (X.ds p q lam).U ⟨(X.ds p q lam).2, (X.ds p q lam).3⟩).2.2 (X.ds p q lam).HK (X.ds p q lam).ι
    ⟨(X.ds p q lam).9, (X.ds p q lam).10, (X.ds p q lam).11⟩ |>.1

theorem CJoint.symm {p q r s : ℕ} {σ : Type} {a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    {a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} {Λ₁ Λ₂ Φ} (h : CJoint a₁ a₂ Λ₁ Λ₂ Φ) : CJoint a₂ a₁ Λ₂ Λ₁ Φ := by
  obtain ⟨⟨d, h0, h1, h2⟩, hw1, hw2⟩ := h
  exact ⟨⟨d, h0, h2, h1⟩, hw2, hw1⟩

theorem frame_of_adapted {n : ℕ} {G s B : Mn n} (h : IsAdapted G s B) : ∃ ε, IsFrameOf G s ε B⁻¹ := by
  obtain ⟨ε, h1, h2⟩ := h
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hBd : IsUnit B.det := by
    have hu : IsUnit (Bᴴ * G * B).det := by
      rw [h1]
      exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, _, hJ, hJ⟩, rfl⟩
    rw [Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hBHd : IsUnit Bᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hBd.star
  refine ⟨ε, Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_iff_isUnit_det B).mpr hBd), ?_, ?_⟩
  · rw [← h1, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBHd, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_nonsing_inv _ hBd, ← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBd, Matrix.mul_one]

section Transport

variable {ι ι' σ σ' Z : Type} {n p q : ℕ} {A : Mn n → (Z → ℂ) → (Z → ℂ)} {φ : Mat p q → Mn n} {c : ℚ}

theorem Side.comp {pt : MvPolynomial ι ℂ → (Z → ℂ)} {pt' : MvPolynomial ι' ℂ → (Z → ℂ)}
    {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ} {a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    (h : Side A pt κ φ c a) (ς : MvPolynomial ι' ℂ ≃ₗ[ℂ] MvPolynomial ι ℂ) (hς : ∀ P, pt' P = pt (ς P)) :
    Side A pt' (ς.trans κ) φ c a := by
  refine ⟨?_, ?_⟩
  · intro Y hY P P'
    have e : PolDer A pt' (φ Y) P P' ↔ PolDer A pt (φ Y) (ς P) (ς P') := by simp only [PolDer, hς]
    rw [e]
    exact h.der Y hY (ς P) (ς P')
  · intro μ P
    simp only [hς]
    exact h.wt μ (ς P)

theorem Side.trans {pt : MvPolynomial ι ℂ → (Z → ℂ)} {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ}
    {a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} {a' : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ' ℂ)}
    (h : Side A pt κ φ c a) (w : MvPolynomial σ ℂ ≃ₗ[ℂ] MvPolynomial σ' ℂ) (hw : ∀ Y P, w (a Y P) = a' Y (w P)) :
    Side A pt (κ.trans w) φ c a' := by
  refine ⟨?_, ?_⟩
  · intro Y hY P P'
    rw [h.der Y hY P P']
    simp only [LinearEquiv.trans_apply]
    constructor
    · intro e
      rw [e, map_add (f := _), map_smul, hw]
    · intro e
      apply w.injective
      rw [e, map_add (f := _), map_smul, hw]
  · intro μ P
    rw [← h.wt μ P]
    simp only [LinearEquiv.trans_apply, wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    refine forall_congr' fun i => ?_
    rw [← hw, ← LinearEquiv.map_smul, ← map_sub, LinearEquiv.map_eq_zero_iff]

theorem L2UnitaryRepresentationData.comp {G : Mn n} {pt : MvPolynomial ι ℂ → (Z → ℂ)} {pt' : MvPolynomial ι' ℂ → (Z → ℂ)} {ip Θ}
    (h : L2UnitaryRepresentationData G A pt ip Θ) (ς : MvPolynomial ι' ℂ ≃ₗ[ℂ] MvPolynomial ι ℂ) (hς : ∀ P, pt' P = pt (ς P)) :
    L2UnitaryRepresentationData G A pt' ip Θ := by
  have hd : ∀ X P P', PolDer A pt' X P P' ↔ PolDer A pt X (ς P) (ς P') := fun X P P' => by
    simp only [PolDer, hς]
  exact
  { mem := fun P => by rw [hς]; exact h.mem _
    pt_lin := fun z P Q => by
      simp only [hς, map_add (f := _), map_smul]
      exact h.pt_lin z (ς P) (ς Q)
    ip_lin := h.ip_lin
    ip_symm := h.ip_symm
    ip_pos := h.ip_pos
    stable := h.stable
    lin := h.lin
    one := h.one
    mul := h.mul
    unit := h.unit
    cont := h.cont
    der := fun X hX P P' hPP E hE => by
      simp only [hς]
      exact h.der X hX _ _ ((hd X P P').1 hPP) E hE }

theorem Graded.trans {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial ι' ℂ} {w : MvPolynomial ι' ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ}
    (h : Graded κ) (h' : Graded w) : Graded (κ.trans w) := by
  intro d P
  exact (h' d (κ P)).trans (h d P)

def swp (α β : Type) : MvPolynomial (α × β) ℂ ≃ₗ[ℂ] MvPolynomial (β × α) ℂ :=
  (MvPolynomial.renameEquiv ℂ (Equiv.prodComm α β)).toLinearEquiv

theorem swp_apply {α β : Type} (P : MvPolynomial (α × β) ℂ) : swp α β P = MvPolynomial.rename Prod.swap P := rfl

theorem graded_swp (α β : Type) : Graded (swp α β) := by
  intro d P
  rw [swp_apply]
  exact MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Prod.swap_injective

theorem fockIp_swp {α β : Type} (P Q : MvPolynomial (α × β) ℂ) : fockIp (swp α β P) (swp α β Q) = fockIp P Q := by
  classical
  simp only [swp_apply, fockIp]
  rw [MvPolynomial.support_rename_of_injective Prod.swap_injective,
    Finset.sum_image (fun x _ y _ hxy => Finsupp.mapDomain_injective Prod.swap_injective hxy)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ Prod.swap_injective, MvPolynomial.coeff_rename_mapDomain _ Prod.swap_injective,
    Finsupp.prod_mapDomain_index_inj Prod.swap_injective]

end Transport

variable {D : D7}

structure Reads {ι Z : Type} {n n' p q r s : ℕ} (G : Mn n) (G' : Mn n') (A : Mn n → (Z → ℂ) → (Z → ℂ))
    (B : Mn n' → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (IP : ((Z → ℂ) → (Z → ℂ) → ℂ) → Prop)
    (φ : Mat p q → Mn n) (φ' : Mat r s → Mn n') (c c' : ℚ) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) : Prop where
  gr : Graded κ
  s₁ : Side A pt κ φ c (fockAct1 p q r s)
  s₂ : Side B pt κ φ' c' (fockAct2 p q r s)
  l2 : ∀ ip, IP ip → ∃ N Θ, Fischer pt ip κ N ∧ L2UnitaryRepresentationData G A pt ip Θ ∧ L2UnitaryRepresentationData G' B pt ip Θ

theorem Reads.swap {ι Z : Type} {n n' p q r s : ℕ} {G : Mn n} {G' : Mn n'} {A : Mn n → (Z → ℂ) → (Z → ℂ)}
    {B : Mn n' → (Z → ℂ) → (Z → ℂ)} {pt : MvPolynomial ι ℂ → (Z → ℂ)} {IP : ((Z → ℂ) → (Z → ℂ) → ℂ) → Prop}
    {φ : Mat p q → Mn n} {φ' : Mat r s → Mn n'} {c c' : ℚ} {κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s}
    (h : Reads G G' A B pt IP φ φ' c c' κ) : Reads G' G B A pt IP φ' φ c' c (κ.trans (swp _ _)) := by
  refine ⟨h.gr.trans (graded_swp _ _), ?_, ?_, ?_⟩
  · exact h.s₂.trans (swp _ _) fun Y P => by rw [swp_apply, swp_apply, GlobalTheory.FockSwap.rename_fockAct2]
  · exact h.s₁.trans (swp _ _) fun Y P => by rw [swp_apply, swp_apply, GlobalTheory.FockSwap.rename_fockAct1]
  · intro ip hip
    obtain ⟨N, Θ, hF, h1, h2⟩ := h.l2 ip hip
    refine ⟨N, Θ, ⟨hF.1, fun P Q => ?_⟩, h2, h1⟩
    rw [hF.2 P Q, LinearEquiv.trans_apply, LinearEquiv.trans_apply, fockIp_swp]

def IsIp (S T : HSp D) (ip : (WO S T → ℂ) → (WO S T → ℂ) → ℂ) : Prop :=
  ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) 𝓕 μ ∧ ip = ipTh μ 𝓕

theorem exists_real {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {τ : D.what₂.Tau} (hω : IsWeilDatumO ψ S T χS χT ω)
    {aS aT : ℚ} (hS : HasInfExp D χS τ aS) (hT : HasInfExp D χT τ aT) {sS frS εS sT frT εT}
    (fS : IsFrameOf (gramAt D S τ) sS εS frS) (fT : IsFrameOf (gramAt D T τ) sT εT frT) {BS BT f}
    (hf : IsFockAt ψ θ S T τ sS sT BS BT f) {p q r s : ℕ} {e : Ix p q ≃ Fin S.rank} {e' : Ix r s ≃ Fin T.rank}
    (he : SignCompat εS e) (he' : SignCompat εT e') :
    ∃ κ, Reads (gramAt D S τ) (gramAt D T τ) (actSrc θ ω τ) (actTgt θ ω τ) (ptAt ψ θ S T τ sS sT BS BT f) (IsIp S T)
      (phiFr frS true e) (phiFr frT false e') aT aS κ := by
  have hψ : IsStdChar D ψ (-1) := hω.std
  obtain ⟨ς, hςg, -, hςpt⟩ := GlobalTheory.T.fockVectors_adaptedBasis_unitary_substitution D ψ θ S T τ hψ hf.inf sS frS εS sT frT εT fS fT BS BT hf.onS hf.onT
  obtain ⟨κ₀, hκp, hκg, hκip⟩ := GlobalTheory.T.exists_fockPolynomialIso_graded_isometry p q r s S.rank T.rank εS εT e e' he he'
  have hL := GlobalTheory.T.lieAlgebrasAtPlace_act_fockVectors_by_fockOperators D ψ θ S T χS χT ω τ hf.inf hω aS aT hS hT sS frS εS sT frT εT fS fT f hf.theta hf.vac
  obtain ⟨hth, hrest⟩ := GlobalTheory.T.fockVectors_at_one_realPlace_over_vacuum D ψ θ S T τ hψ hf.inf sS frS εS sT frT εT fS fT f hf.theta hf.vac
  obtain ⟨hinj, hfis⟩ := hrest hf.ne
  let L : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ) :=
    pureTensorL (fun k : Fin T.rank × Fin S.rank => aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap frS⁻¹ frT⁻¹ k.1 k.2)) f
  have hLpt : ∀ P, L P = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P := fun P => rfl
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.fockVectors_realPlace_act_as_fockPolynomials D ψ θ S T ω τ hf.inf sS frS εS sT frT εT fS fT aS aT L hinj hL p q r s e e' he he' κ₀ hκp
  have hσ := hςpt f hf.theta
  refine ⟨ς.trans κ₀, hςg.trans hκg, hs1.comp ς hσ, hs2.comp ς hσ, ?_⟩
  rintro ip ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
  obtain ⟨N, hN⟩ := hfis μ 𝓕 hμ h𝓕
  obtain ⟨Θ, hΘ1, hΘ2⟩ := GlobalTheory.T.realPlaceGroups_act_unitarily_weakly_on_theta D ψ θ S T χS χT ω τ hf.inf hω frS εS frT εT aS aT L hth hL μ 𝓕 hμ h𝓕
  refine ⟨N, Θ, ⟨hN.1, fun P Q => ?_⟩, hΘ1.comp ς hσ, hΘ2.comp ς hσ⟩
  rw [hσ P, hσ Q, hN.2, LinearEquiv.trans_apply, LinearEquiv.trans_apply, hκip]
  rfl

structure Good (D : D7) (X : ProvA) : Prop where
  par : ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam
  ds : DiscreteSeriesBlattner X
  hc : admQ5 X
  br : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D

theorem exists_ktie {X : ProvA} (h : Good D X) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {p q : ℕ} {l₁ l₂ : List ℚ} {c : ℚ} (br cj : Bool) (hn : 1 ≤ p + q) (h₁ : l₁.length = p) (h₂ : l₂.length = q)
    (hp : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ)) (hS : S τ = parOf br cj l₁ l₂ c) :
    (∃ m : ℤ, (m : ℚ) = 2 * c) ∧
      ∃ e u, KTie (X.ds p q (ofBlocks l₁ l₂)) M τ (ofBlocks l₁ l₂) c br cj e u := by
  have hpar := h.par p q _ hp
  have hfin := (h.ds p q _ hp).1
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_signCompatible_numbering_decreasing_enumeration V.rank p q l₁ l₂ c br cj (M.ε τ) (M.lam τ) h₁ h₂ hp (by rw [← hS]; exact M.enum τ)
  obtain ⟨m, hm, U, hU⟩ : ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∃ U, Comparison₂ (X.ds p q (ofBlocks l₁ l₂)) M τ br cj e m U := by
    cases br <;> cases cj
    · obtain ⟨m, hm, hU⟩ := GlobalTheory.T.discreteSeriesModelParamShiftedWeight_of_coverDiscreteSeries D h.br X V S M τ p q l₁ l₂ c hn h₁ h₂ hp hpar (by rw [hS]; rfl)
      exact ⟨m, hm, hU e he.1 false⟩
    · obtain ⟨-, m, hm, hU⟩ := h.br.2 X V S M τ p q l₁ l₂ c ⟨hn, h₁, h₂, hp, hpar, by rw [hS]; rfl⟩
      obtain ⟨U, hU⟩ := hU e he.1
      exact ⟨m, hm, U, fun x y => U.map_add x y, fun z x => U.map_smulₛₗ z x, U.bijective, fun x => U.norm_map x,
        hU.grp, hU.kfin⟩
    · obtain ⟨-, m, hm, hU⟩ := h.br.1 X V S M τ p q l₁ l₂ c ⟨hn, h₁, h₂, hp, hpar, by rw [hS]; rfl⟩
      obtain ⟨U, hU⟩ := hU e he.1
      exact ⟨m, hm, U, fun x y => U.map_add x y, fun z x => U.map_smul z x, U.bijective, fun x => U.norm_map x,
        hU.grp, hU.kfin⟩
    · obtain ⟨m, hm, hU⟩ := GlobalTheory.T.discreteSeriesModelParamShiftedWeight_of_coverDiscreteSeries D h.br X V S M τ p q l₁ l₂ c hn h₁ h₂ hp hpar (by rw [hS]; rfl)
      exact ⟨m, hm, hU e he.1 true⟩
  have hhi := GlobalTheory.T.discreteSeriesModelIsometry_unit_highestVector_iff D V S M τ p q _ (X.ds p q (ofBlocks l₁ l₂)) _ c br cj e m U hp he hm hU hfin
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_kFiniteIsometry_discreteSeriesModel_detCover D V S M τ p q _ (X.ds p q (ofBlocks l₁ l₂)) _ c br cj e m U hp he hm hU hhi
  exact ⟨⟨m, hm⟩, e, u, hu⟩

section Core

variable {X : ProvA} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {N : DSModel W S'} {τ : D.what₂.Tau}
  {ι Z : Type} {A : Mn V.rank → (Z → ℂ) → (Z → ℂ)} {B : Mn W.rank → (Z → ℂ) → (Z → ℂ)} {pt : MvPolynomial ι ℂ → (Z → ℂ)}
  {IP : ((Z → ℂ) → (Z → ℂ) → ℂ) → Prop} {t : ℕ} {al be ga de : List ℚ} {c c' : ℚ} {b b' : Bool}
  {e : Ix (al.length + be.length) (ga.length + de.length) ≃ Fin V.rank}
  {e' : Ix (al.length + de.length + t) (ga.length + be.length) ≃ Fin W.rank} {κ}

theorem rank_pos (hd : HypA t al be ga de) :
    1 ≤ al.length + be.length + (ga.length + de.length) ∧ 1 ≤ al.length + de.length + t + (ga.length + be.length) := by
  obtain ⟨ht, hl, -⟩ := hd
  constructor <;> omega

theorem lift_up (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de)
    {u u'} (hM : KTie (X.ds _ _ (lamA al be ga de)) M τ (lamA al be ga de) c b true e u)
    (hN : KTie (X.ds _ _ (lamA' t al be ga de)) N τ (lamA' t al be ga de) c' b' false e' u')
    (hR : Reads (gramAt D V τ) (gramAt D W τ) A B pt IP (phiFr (M.fr τ) b e) (phiFr (N.fr τ) b' e') c c' κ) :
    LiftLaw M τ A pt N B := by
  have hJ := GlobalTheory.T.fockJointHarmonic_vectors_iff_polynomials _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM hN hR.s₁ hR.s₂ hR.gr
  obtain ⟨hU, hD, hLn⟩ := h3.1 t al be ga de hd
  have hT := (GlobalTheory.T.thetaCorrespondenceTensorLaw_both_orders_of_covers X _ _ _ _ _ _ (h1.1 t al be ga de hd) hU hD hLn).1
  have hPL := GlobalTheory.T.thetaCorrespondence_pairingLaw_of_tensorLaw _ _ _ _ _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).1 (isGK_fock _ _ _ _).2 (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd.1).1 _)
    (h.ds _ _ _ hM.par).1 hT
  exact GlobalTheory.T.thetaCorrespondence_models_of_covers_realPlace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM hN hR.s₁ hR.s₂ hJ hPL

theorem lift_down (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X)
    (hd : Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de) {u u'} (hm : ∃ m : ℤ, (m : ℚ) = 2 * c)
    (hM : KTie (X.ds _ _ (lamA al be ga de)) M τ (lamA al be ga de) c b false e u)
    (hN : KTie (X.ds _ _ (lamA' t al be ga de)) N τ (lamA' t al be ga de) c' b' true e' u')
    (hR : Reads (gramAt D V τ) (gramAt D W τ) A B pt IP (phiFr (M.fr τ) b e) (phiFr (N.fr τ) b' e') c c' κ) :
    LiftLaw N τ B pt M A ∧ ∀ ip, IP ip → ZetaLaw N τ B pt M A ip := by
  have hJ := GlobalTheory.T.fockJointHarmonic_vectors_iff_polynomials _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hN hM hR.s₂ hR.s₁ hR.gr
  obtain ⟨hU, hD, hLn⟩ := h3.1 t al be ga de hd
  have hT := (GlobalTheory.T.thetaCorrespondenceTensorLaw_both_orders_of_covers X _ _ _ _ _ _ (h1.1 t al be ga de hd) hU hD hLn).2
  have hPL := GlobalTheory.T.thetaCorrespondence_pairingLaw_of_tensorLaw _ _ _ _ _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).2 (isGK_fock _ _ _ _).1 (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd.1).2 _)
    (h.ds _ _ _ hN.par).1 hT
  refine ⟨GlobalTheory.T.thetaCorrespondence_models_of_covers_realPlace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hN hM hR.s₂ hR.s₁ hJ hPL, fun ip hip => ?_⟩
  obtain ⟨m, hm⟩ := hm
  obtain ⟨K, Θ, hF, hL1, -⟩ := hR.l2 ip hip
  have hC : Coef (X.fock _ _ _ _) A pt ip κ (phiFr (M.fr τ) b e) m K := GlobalTheory.T.fockVectors_matrixCoefficients_eq_fockRepresentation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rank_pos hd.1).1 (M.fr_unit τ) (M.fr_gram τ) hM.ord.1 hm hR.s₁ hL1 hF
  refine GlobalTheory.T.zetaIntegral_model_of_cover _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h1.1 t al be ga de hd) ?_ hM hN.ord.1 hm hC fun Φ hΦ => ((hJ Φ).1 hΦ).symm
  intro v hv
  obtain ⟨-, -, hgap⟩ := hd.2
  have hq7 : Formalism.MainNotions.SchurIrreducible.admQ7 := GlobalTheory.TensorHW.highestWeight_tensor
  have hds2 := GlobalTheory.SphJet.lowest_type_positive_and_decays X h.ds h.hc hq7 GlobalTheory.InducedPBW.pbw_induced
  have hds3 := GlobalTheory.T.discreteSeries_integrableCoefficient_projector X hds2 (GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X)
  refine (hds3 _ _ _ hM.par _ hgap ?_ v hv).1
  unfold Formalism.MainNotions.SchurIrreducible.rangeOfSeventhSum
  rw [show al.length + be.length + (ga.length + de.length) = al.length + be.length + ga.length + de.length by omega]

theorem tie_small (h : Good D X) (hd : HypA t al be ga de) (M : DSModel V S) (τ : D.what₂.Tau) (b j : Bool)
    (hS : S τ = parOf b j (al ++ be) (ga ++ de) c) :
    (∃ m : ℤ, (m : ℚ) = 2 * c) ∧ ∃ e u, KTie (X.ds _ _ (lamA al be ga de)) M τ (lamA al be ga de) c b j e u := by
  have hl := (GlobalTheory.LowestTypes.lowest_types t al be ga de hd).2.1
  obtain ⟨-, hn, -⟩ := hd
  exact exists_ktie h M τ (p := al.length + be.length) (q := ga.length + de.length) b j (by omega) (by simp) (by simp) hl hS

theorem tie_large (h : Good D X) (hd : HypA t al be ga de) (M : DSModel V S) (τ : D.what₂.Tau) (b j : Bool)
    (hS : S τ = parOf b j (al ++ block t ++ de) (ga ++ be) c) :
    ∃ e u, KTie (X.ds _ _ (lamA' t al be ga de)) M τ (lamA' t al be ga de) c b j e u := by
  have hl := (GlobalTheory.LowestTypes.lowest_types t al be ga de hd).2.2.1
  obtain ⟨ht, -⟩ := hd
  exact (exists_ktie h M τ (p := al.length + de.length + t) (q := ga.length + be.length) b j (by omega)
    (by simp [block]; omega) (by simp) hl hS).2

theorem noLowerTarget {T : HSp D} {p q r s : ℕ} {lam : Ix p q → ℚ} {aT : ℚ} {pS pT : SPar}
    (hS : ∀ {P} (M : DSModel V P), P τ = pS → ∃ e u, KTie (X.ds p q lam) M τ lam aT true true e u)
    (hT : ∀ {P} (M : DSModel T P), P τ = pT → ∃ e : Ix r s ≃ Fin T.rank, SignCompat (M.ε τ) e)
    (hno : ∀ i, 1 ≤ i → i ≤ r → i ≤ s → PairNo (fockAct1 p q (r - i) (s - i)) (X.ds p q lam)) :
    NoLowerTarget τ V T aT pS pT := by
  intro PS PT MS MT hPS hPT T' i hi hW ψ θ χS χT ω hω hχT sT BS BT f hf
  obtain ⟨e, u, hu⟩ := hS MS hPS
  obtain ⟨e₀, he₀⟩ := hT MT hPT
  obtain ⟨εT, fT⟩ := frame_of_adapted hf.onT
  obtain ⟨hir, his, e', he'⟩ := GlobalTheory.T.signCompatibleNumbering_of_wittTower_lower D T T' i τ (MT.fr τ) (MT.ε τ) BT⁻¹ εT r s e₀ hW (MT.fr_gram τ)
    (MT.fr_unit τ) fT.2.1 fT.1 he₀
  obtain ⟨aS, haS⟩ := GlobalTheory.T.splittingHeckeChar_exists_archimedeanExponent D θ χS _ τ hf.inf hω.hecS hω.resS
  obtain ⟨κ, hR⟩ := exists_real hω haS hχT (isFrameOf_model MS τ) fT hf hu.ord.1 he'
  exact GlobalTheory.T.noThetaMap_models_of_noPairing_covers _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hR.s₁ (hno i hi hir his)

theorem noLowerSource {T : HSp D} {p q r s : ℕ} {lam : Ix r s → ℚ} {aS : ℚ} {pS pT : SPar}
    (hS : ∀ {P} (M : DSModel V P), P τ = pS → ∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e)
    (hT : ∀ {P} (M : DSModel T P), P τ = pT → ∃ e u, KTie (X.ds r s lam) M τ lam aS false true e u)
    (hno : ∀ i, 1 ≤ i → i ≤ p → i ≤ q → PairNo (fockAct2 (p - i) (q - i) r s) (X.ds r s lam)) :
    NoLowerSource τ V T aS pS pT := by
  intro PS PT MS MT hPS hPT S' i hi hW ψ θ χS χT ω hω hχS sS BS BT f hf
  obtain ⟨e', u, hu⟩ := hT MT hPT
  obtain ⟨e₀, he₀⟩ := hS MS hPS
  obtain ⟨εS, fS⟩ := frame_of_adapted hf.onS
  obtain ⟨hip, hiq, e, he⟩ := GlobalTheory.T.signCompatibleNumbering_of_wittTower_lower D V S' i τ (MS.fr τ) (MS.ε τ) BS⁻¹ εS p q e₀ hW (MS.fr_gram τ)
    (MS.fr_unit τ) fS.2.1 fS.1 he₀
  obtain ⟨aT, haT⟩ := GlobalTheory.T.splittingHeckeChar_exists_archimedeanExponent D θ χT _ τ hf.inf hω.hecT hω.resT
  obtain ⟨κ, hR⟩ := exists_real hω hχS haT fS (isFrameOf_model MT τ) hf he hu.ord.1
  exact GlobalTheory.T.noThetaMap_models_of_noPairing_covers _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hR.s₂ (hno i hi hip hiq)

theorem pairNo_small (h : Good D X) (hd : HypA t al be ga de) (i : ℕ) (hi : 1 ≤ i) (h1 : i ≤ al.length + de.length + t)
    (h2 : i ≤ ga.length + be.length) :
    PairNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (X.ds _ _ (lamA al be ga de)) := by
  have hT := (GlobalTheory.T.noThetaTensorIntertwiner_lowerTowerMembers X h.ds h.hc t al be ga de hd i hi).1 h1 h2
  exact GlobalTheory.T.no_invariant_theta_pairing_of_no_tensor_intertwiner _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).1 (isGK_fock _ _ _ _).2 (GlobalTheory.T.fockOperators_lie_representation_commute _ _ _ _).2.2.2
    (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd).1 _) hT

theorem pairNo_large (h : Good D X) (hd : HypA t al be ga de) (hf : ∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|)
    (i : ℕ) (hi : 1 ≤ i) (h1 : i ≤ al.length + be.length) (h2 : i ≤ ga.length + de.length) :
    PairNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (X.ds _ _ (lamA' t al be ga de)) := by
  have hT := (GlobalTheory.T.noThetaTensorIntertwiner_lowerTowerMembers X h.ds h.hc t al be ga de hd i hi).2 hf h1 h2
  exact GlobalTheory.T.no_invariant_theta_pairing_of_no_tensor_intertwiner _ _ _ _ _ _ _ _ _ (isGK_fock _ _ _ _).2 (isGK_fock _ _ _ _).1
    (fun Y Z => ((GlobalTheory.T.fockOperators_lie_representation_commute _ _ _ _).2.2.2 Z Y).symm) (discreteSeries_harishChandraModule_admissible h.hc (rank_pos hd).2 _) hT

theorem PairNo.swap {p q r s : ℕ} {T : GrpData r s} {R : DSRep T} (h : PairNo (fockAct2 p q r s) R) :
    PairNo (fockAct1 r s p q) R := by
  intro U _ _ B hB
  have key := h U (B ∘ₗ (swp (Ix p q) (Ix r s)).toLinearMap) (by
    intro Z hZ P v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, swp_apply, GlobalTheory.FockSwap.rename_fockAct2]
    exact hB Z hZ _ v)
  refine LinearMap.ext fun P => ?_
  have := LinearMap.congr_fun key ((swp (Ix p q) (Ix r s)).symm P)
  simpa using this

end Core

variable {X : ProvA}

theorem chainLower (h : Good D X) : ChainLower D := by
  intro k τ V W
  obtain ⟨al, be, ga, de, ⟨hA, hF, -⟩, h1, h2⟩ := GlobalTheory.T.thetaChainStep_centred_block_parameters D k τ
  refine ⟨noLowerTarget (fun M hM => ?_) (fun M hM => ?_) (fun i hi hr hs => pairNo_small h hA i hi hr hs),
    noLowerSource (fun M hM => ?_) (fun M hM => ?_) (fun i hi hp hq => pairNo_large h hA hF i hi hp hq)⟩
  · obtain ⟨-, e, u, hu⟩ := tie_small h hA M τ true true (hM.trans h1)
    exact ⟨e, u, hu⟩
  · obtain ⟨e, u, hu⟩ := tie_large h hA M τ false false (hM.trans h2)
    exact ⟨e, hu.ord.1⟩
  · obtain ⟨-, e, u, hu⟩ := tie_small h hA M τ true false (by rw [hM, parB, ← parA, h1]; rfl)
    exact ⟨e, hu.ord.1⟩
  · obtain ⟨e, u, hu⟩ := tie_large h hA M τ false true (by rw [hM, parB, ← parA, h2]; rfl)
    exact ⟨e, u, hu⟩

theorem pairLower (h : Good D X) : PairLower D := by
  intro i τ
  obtain ⟨al, de, ⟨hA, hF, -⟩, h1, h2⟩ := GlobalTheory.T.definiteSource_pair_centred_block_parameters D i τ
  refine noLowerTarget (fun M hM => ?_) (fun M hM => ?_)
    (fun j hj hr hs => PairNo.swap (pairNo_large h hA hF j hj hr hs))
  · obtain ⟨e, u, hu⟩ := tie_large h hA M τ true true (hM.trans h2)
    exact ⟨e, u, hu⟩
  · obtain ⟨-, e, u, hu⟩ := tie_small h hA M τ false false (hM.trans h1)
    exact ⟨e, hu.ord.1⟩

theorem chainTop (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hg : NodeGap D) : ChainTop D := by
  intro k τ V W
  obtain ⟨al, be, ga, de, ⟨hA, -, hG⟩, e1, e2⟩ := GlobalTheory.T.thetaChainStep_centred_block_parameters D k τ
  have hd : Formalism.MainNotions.SchurIrreducible.DataAR D.R.t al be ga de := ⟨hA, hG hg⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨-, e, u, hu⟩ := tie_small h hA MS τ true true (hPS.trans e1)
    obtain ⟨e', u', hu'⟩ := tie_large h hA MT τ false false (hPT.trans e2)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact lift_up h h1 h3 hd hu hu' hR
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨hm, e, u, hu⟩ := tie_small h hA MS τ true false (by rw [hPS, parB, ← parA, e1]; rfl)
    obtain ⟨e', u', hu'⟩ := tie_large h hA MT τ false true (by rw [hPT, parB, ← parA, e2]; rfl)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu hu' hR).1
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf μ 𝓕 hμ h𝓕
    obtain ⟨hm, e, u, hu⟩ := tie_small h hA MS τ true false (by rw [hPS, parB, ← parA, e1]; rfl)
    obtain ⟨e', u', hu'⟩ := tie_large h hA MT τ false true (by rw [hPT, parB, ← parA, e2]; rfl)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu hu' hR).2 _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩

theorem pairTop (h : Good D X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (hg : NodeGap D) : PairTop D := by
  intro i τ
  obtain ⟨al, de, ⟨hA, -, hG⟩, e1, e2⟩ := GlobalTheory.T.definiteSource_pair_centred_block_parameters D i τ
  have hd : Formalism.MainNotions.SchurIrreducible.DataAR D.R.t al [] [] de := ⟨hA, hG hg⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨e, u, hu⟩ := tie_large h hA MS τ true true (hPS.trans e2)
    obtain ⟨hm, e', u', hu'⟩ := tie_small h hA MT τ false false (hPT.trans e1)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu' hu hR.swap).1
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf
    obtain ⟨e, u, hu⟩ := tie_large h hA MS τ true false (by rw [hPS, e2]; rfl)
    obtain ⟨-, e', u', hu'⟩ := tie_small h hA MT τ false true (by rw [hPT, e1]; rfl)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact lift_up h h1 h3 hd hu' hu hR.swap
  · intro ψ θ χS χT ω hω hS hT PS PT MS MT hPS hPT BS BT f hf μ 𝓕 hμ h𝓕
    obtain ⟨e, u, hu⟩ := tie_large h hA MS τ true true (hPS.trans e2)
    obtain ⟨hm, e', u', hu'⟩ := tie_small h hA MT τ false false (hPT.trans e1)
    obtain ⟨κ, hR⟩ := exists_real hω hS hT (isFrameOf_model MS τ) (isFrameOf_model MT τ) hf hu.ord.1 hu'.ord.1
    exact (lift_down h h1 h3 hd hm hu' hu hR.swap).2 _ ⟨μ, 𝓕, hμ, h𝓕, rfl⟩

theorem alS_eq (k : Fin D.R.m) (τ : D.what₂.Tau) : alS D k τ = GlobalTheory.Chain.expS D k τ := by
  unfold alS GlobalTheory.Chain.expS
  rcases Nat.even_or_odd (k : ℕ) with h | h
  · rw [if_pos h.add_one, if_pos h]
  · rw [if_neg (Nat.not_odd_iff_even.mpr h.add_one), if_neg (Nat.not_even_iff_odd.mpr h)]
    ring

theorem alT_eq (k : Fin D.R.m) (τ : D.what₂.Tau) : alT D k τ = GlobalTheory.Chain.expT D k τ := by
  unfold alT GlobalTheory.Chain.expT
  rcases Nat.even_or_odd (k : ℕ) with h | h
  · rw [if_pos h.add_one, if_pos h]
    ring
  · rw [if_neg (Nat.not_odd_iff_even.mpr h.add_one), if_neg (Nat.not_even_iff_odd.mpr h)]

theorem itLaw (hP : GlobalTheory.Chain.ItPair D) (hL : GlobalTheory.Chain.ItLine D) (hg : NodeGap D) : ItLaw D := by
  intro k V W P P' M M' hPe hPe' ψ θ χS χT ω hω hχ f hf
  subst hPe hPe'
  have hθ : IsInfFam θ := fun ρ => (hf ρ).inf ρ
  have hC : GlobalTheory.Chain.ChainPar D k := by
    intro τ
    obtain ⟨al, be, ga, de, ⟨hA, hF, hG⟩, h1, h2⟩ := GlobalTheory.T.thetaChainStep_centred_block_parameters D k τ
    refine ⟨al, be, ga, de, ⟨hA, hG hg⟩, hF, ?_, ?_⟩
    · rw [h1, alT_eq]
    · rw [h2, alS_eq]
  have hW : GlobalTheory.Chain.IsStepWeil k ψ V W ω := ⟨χS, χT, hω, fun τ => by rw [← alS_eq, ← alT_eq]; exact hχ τ⟩
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    have hc : Fintype.card D.what₂.Tau = D.R.f := D.what₂.10
    have h8 : 2 ≤ D.R.m := D.R.8
    have h12 : D.R.m ≤ 2 * D.R.ord := D.R.12
    rw [← Fintype.card_pos_iff, hc]
    unfold Ranks.f Ranks.n
    omega
  have hV : GlobalTheory.Chain.IsVacVec ψ θ M M' f := ⟨(hf τ₀).theta, (hf τ₀).ne, fun τ => (hf τ).vac⟩
  obtain ⟨It, -, hIt⟩ := hP k V W M M' θ ψ hθ hC
  exact ⟨It, hIt ω f hW hV, fun It' h' => hL k V W M M' θ ψ hθ hC ω f hW hV It It' (hIt ω f hW hV) h'⟩

theorem ioLaw (h1 : IoEx D) (h2 : IoUniq D) (h3 : IoHarm D) : IoLaw D := by
  intro i P P' M M' hP hP' ψ θ χS χT ω hω hχ c hc hpr BV f hf
  subst hP hP'
  have hθ : IsInfFam θ := fun ρ => (hf ρ).inf ρ
  obtain ⟨io, hio⟩ := h1 i M M' ψ θ χS χT ω hθ hω hχ c hc hpr BV f hf
  exact ⟨io, hio, fun io' h' => h2 i M M' ψ θ χS χT ω hθ hω hχ c hc hpr BV f hf io io' hio h',
    h3 i M M' ψ θ χS χT ω hθ hω hχ c hc hpr BV f hf io hio⟩

theorem archOnRecord_of_cover (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) (D : D7)
    (X : ProvA) (hX : GlobalTheory.Chain.RealIt.ChosenSeries X) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) :
    ArchOnRecord D := by
  obtain ⟨Y, hpar, hds, hq5, hy1, -, hy3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hDS hHC
  have hG : Good D Y := ⟨hpar, hds, hq5, GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hDS hHC D⟩
  exact ⟨⟨chainLower hG, pairLower hG⟩, fun hg => ⟨chainTop hG hy1 hy3 hg, pairTop hG hy1 hy3 hg,
    itLaw (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep hDS hHC D) (GlobalTheory.T.realThetaIntertwiners_proportional_of_harishChandra hDS hHC D) hg,
    ioLaw (GlobalTheory.T.lowestKTypeFockMap_exists_of_discreteSeries hDS hHC D) (GlobalTheory.T.lowestKTypeFockMap_unique_of_discreteSeries hDS hHC D) (GlobalTheory.T.lowestKTypeFockMap_harmonic_of_discreteSeries hDS hHC D)⟩⟩

theorem archOnRecord (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) (D : D7) :
    ArchOnRecord D := by
  obtain ⟨X, hpar, -, -, h1, -, h3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hDS hHC
  exact archOnRecord_of_cover hDS hHC D X hpar h1 h3

end GlobalTheory.ArchRec

end
