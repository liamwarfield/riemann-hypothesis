module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivHomDivisibleByPowOfKillsPowTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PassIn3OfRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarCoeffEisensteinSeriesReversePoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEveryEmbeddingThirdKind
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDifferentFromIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionFlatWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponent
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatUnitProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)

def IsBddUnit (G : WTZ E) (s t : Rul Xo c) : Prop :=
  Even G.2 ∧ s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw G) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw G) ∧
    GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧
    (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z,
      GlobalTheory.AllWt.homN (U σ) x G s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) x (-G) t z ≤ C) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)

theorem exZ_zero' : Formalism.L2.Pj.exZ Dw (0 : WTZ E) = 0 := by
  funext i; cases i <;> rfl

theorem exZ_add_eq' (G G' : WTZ E) : Formalism.L2.Pj.exZ Dw (G + G') = Formalism.L2.Pj.exZ Dw G + Formalism.L2.Pj.exZ Dw G' :=
  funext fun i => exZ_add _ _ i

theorem exZ_neg_eq' (G : WTZ E) : Formalism.L2.Pj.exZ Dw (-G) = -Formalism.L2.Pj.exZ Dw G := by
  funext i; cases i <;> rfl

theorem homN_idem_le {σ : c.F →+* ℂ} (V : Unf Xo c σ r) {z} (hz : z ∈ framesOn V Z) :
    GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z ≤ 1 := by
  obtain ⟨hd, hl⟩ := hz
  rcases eq_or_ne (GlobalTheory.AllWt.homN V x 0 (GlobalTheory.FlatLine.idem Z) z) 0 with h | h
  · rw [h]; exact zero_le_one
  · rw [GlobalTheory.FlatLine.homN_idem V x hd hl (GlobalTheory.FlatLine.tested_of_homN_ne V x hd h)]

theorem isBddUnit_zero : IsBddUnit U x Z 0 (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z) := by
  have hm : GlobalTheory.FlatLine.idem Z ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (0 : WTZ E)) := by
    rw [exZ_zero']; exact GlobalTheory.FlatLine.idem_mem_secZ Z
  refine ⟨by simp, hm, by rwa [exZ_zero', neg_zero, ← exZ_zero' (Dw := Dw)], GlobalTheory.FlatLine.idem_mul_idem Z,
    GlobalTheory.FlatLine.idem_mul_idem Z, GlobalTheory.FlatLine.idem_mul_idem Z, fun σ _ => ⟨1, fun z hz => ?_⟩, 1, one_pos,
    fun la v hv => ?_⟩
  · rw [neg_zero]; exact ⟨homN_idem_le x Z (U σ) hz, homN_idem_le x Z (U σ) hz⟩
  · rw [Nat.cast_one, one_smul, GlobalTheory.FlatLine.val_idem hv]; exact ⟨le_rfl, le_rfl⟩

variable {U x Z}

theorem IsBddUnit.mul {G G' : WTZ E} {s t s' t' : Rul Xo c} (h : IsBddUnit U x Z G s t)
    (h' : IsBddUnit U x Z G' s' t') : IsBddUnit U x Z (G + G') (s * s') (t * t') := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  obtain ⟨hG', hs', ht', his', hit', hst', hb', m', hm', hv'⟩ := h'
  refine ⟨hG.add hG', ?_, ?_, by rw [← mul_assoc, his], by rw [← mul_assoc, hit], ?_,
    fun σ hσ => ?_, m * m', Nat.mul_pos hm hm', fun la v hw => ?_⟩
  · rw [exZ_add_eq']; exact GlobalTheory.AllWt.mul_mem_secZ hs hs'
  · rw [exZ_add_eq', neg_add]; exact GlobalTheory.AllWt.mul_mem_secZ ht ht'
  · rw [mul_mul_mul_comm, hst, hst', GlobalTheory.FlatLine.idem_mul_idem]
  · obtain ⟨C, hC⟩ := hb σ hσ
    obtain ⟨C', hC'⟩ := hb' σ hσ
    refine ⟨max C 0 * max C' 0, fun z hz => ⟨?_, ?_⟩⟩
    · rw [GlobalTheory.AllWt.homN_mul (U σ) x hG hG' s s' z hz.1]
      exact mul_le_mul ((hC z hz).1.trans (le_max_left _ _)) ((hC' z hz).1.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
    · rw [neg_add, GlobalTheory.AllWt.homN_mul (U σ) x (G := -G) (G' := -G') hG.neg hG'.neg t t' z hz.1]
      exact mul_le_mul ((hC z hz).2.trans (le_max_left _ _)) ((hC' z hz).2.trans (le_max_left _ _))
        (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _) (le_max_right _ _)
  · have hV := GlobalTheory.FlatLine.isVal_valOn hw
    rw [Nat.cast_mul, ← smul_mul_smul_comm, ← smul_mul_smul_comm, hV.mul, hV.mul]
    exact ⟨add_nonneg (hv la v hw).1 (hv' la v hw).1, add_nonneg (hv la v hw).2 (hv' la v hw).2⟩

theorem IsBddUnit.swap {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) : IsBddUnit U x Z (-G) t s := by
  obtain ⟨hG, hs, ht, his, hit, hst, hb, m, hm, hv⟩ := h
  refine ⟨hG.neg, by rwa [exZ_neg_eq'], by rwa [exZ_neg_eq', neg_neg], hit, his,
    by rw [mul_comm, hst], fun σ hσ => ?_, m, hm, fun la v hw => (hv la v hw).symm⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  exact ⟨C, fun z hz => ⟨(hC z hz).2, by rw [neg_neg]; exact (hC z hz).1⟩⟩

theorem exists_nsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (k : ℕ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (k • G) s' t' := by
  induction k with
  | zero => exact ⟨_, _, by rw [zero_nsmul]; exact isBddUnit_zero U x Z⟩
  | succ k ih =>
    obtain ⟨s', t', h'⟩ := ih
    exact ⟨_, _, by rw [succ_nsmul]; exact h'.mul h⟩

theorem exists_zsmul {G : WTZ E} {s t : Rul Xo c} (h : IsBddUnit U x Z G s t) (n : ℤ) :
    ∃ s' t' : Rul Xo c, IsBddUnit U x Z (n • G) s' t' := by
  cases n with
  | ofNat k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h k
    exact ⟨s', t', by rw [Int.ofNat_eq_natCast, natCast_zsmul]; exact h'⟩
  | negSucc k =>
    obtain ⟨s', t', h'⟩ := exists_nsmul h (k + 1)
    exact ⟨t', s', by rw [negSucc_zsmul]; exact h'.swap⟩

theorem exists_sum {ι : Type} (G : ι → WTZ E) (hu : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t)
    (n : ι → ℤ) (S : Finset ι) : ∃ s t : Rul Xo c, IsBddUnit U x Z (∑ i ∈ S, n i • G i) s t := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨_, _, by rw [Finset.sum_empty]; exact isBddUnit_zero U x Z⟩
  | insert a S ha ih =>
    obtain ⟨s, t, h⟩ := ih
    obtain ⟨s₀, t₀, h₀⟩ := hu a
    obtain ⟨s₁, t₁, h₁⟩ := exists_zsmul h₀ (n a)
    exact ⟨_, _, by rw [Finset.sum_insert ha]; exact h₁.mul h⟩

end GlobalTheory.FlatUnitProd


open GlobalTheory.FlatUnitProd in
theorem GlobalTheory.FlatUnitProd.exists_unit_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ι : Type) [Fintype ι] (G : ι → WTZ E), (∀ i, Even (G i).2) → (∀ i, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)) → ∀ n : ι → ℤ, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (∑ i, n i • G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(∑ i, n i • G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t) := by
  intro E _ _ _ H Dw l Xo c r U x Z ι _ G hev hu n
  have hu' : ∀ i, ∃ s t : Rul Xo c, IsBddUnit U x Z (G i) s t := fun i => by
    obtain ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩ := hu i
    exact ⟨s, t, hev i, h1, h2, h3, h4, h5, h6, m, hm, hv⟩
  obtain ⟨s, t, -, h1, h2, h3, h4, h5, h6, m, hm, hv⟩ := exists_sum G hu' n Finset.univ
  exact ⟨s, t, ⟨h1, h2, h3, h4, h5, h6⟩, m, hm, hv⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedUnitSumComponentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boundedUnit_sum_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (ι : Type) [Fintype ι] (G : ι → WTZ E), (∀ i, Even (G i).2) → (∀ i, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t)) → ∀ n : ι → ℤ, ∃ s t : Rul Xo c, (s ∈ GlobalTheory.AllWt.secZ Xo c (Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ t ∈ GlobalTheory.AllWt.secZ Xo c (-Formalism.L2.Pj.exZ Dw (∑ i, n i • G i)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) (x) (∑ i, n i • G i) s z ≤ C ∧ GlobalTheory.AllWt.homN (U σ) (x) (-(∑ i, n i • G i)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : c.F) • s) ∧ 0 ≤ v ((m : c.F) • t) := by
  first | exact @GlobalTheory.FlatUnitProd.exists_unit_sum | exact GlobalTheory.FlatUnitProd.exists_unit_sum | (intros; apply GlobalTheory.FlatUnitProd.exists_unit_sum <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine

theorem val_sum_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) {ι : Type}
    (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, 0 ≤ v (f i)) : 0 ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hv.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) (hv.add _ _)

theorem val_nsmul_nonneg {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    {la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : Formalism.L2.Pj.IsVal la v) (n : ℕ) {f : R}
    (h : 0 ≤ v f) : 0 ≤ v (n • f) := by
  have := val_sum_nonneg hv (Finset.range n) (fun _ => f) (fun _ _ => h)
  simpa [Finset.sum_const, Finset.card_range] using this

theorem pnorm_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {ι : Type} (s : Finset ι) (P : ι → ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ)
    (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : X.pnorm la (∑ i ∈ s, P i) y ≤ ∑ i ∈ s, X.pnorm la (P i) y := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _)
  rw [Finset.sum_apply]
  exact norm_sum_le _ _

end GlobalTheory.FlatUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackFiniteFlatDegreeBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackFiniteFlatDegreeBounds
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich_flat : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackFiniteFlatDegreeBoundsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_sections_pullback_finite_flat_degree_bounds : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  first | exact @GlobalTheory.finrank_sec_pull_sandwich_flat | exact GlobalTheory.finrank_sec_pull_sandwich_flat | (intros; apply GlobalTheory.finrank_sec_pull_sandwich_flat <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.MulDegree

theorem finrank_mul_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → n ≠ 0 → ∀ [IsFinite (𝟙 B ^ n : B ⟶ B).left] [Flat (𝟙 B ^ n : B ⟶ B).left], ∀ x : B.left, (𝟙 B ^ n : B ⟶ B).left.finrank x = n ^ (2 * g) := by
  intro k _ _ B _ g n hB hg hn0 _ _ x
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hq : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hn0)
  haveI : IsMonHom (𝟙 B ^ n : B ⟶ B) := GlobalTheory.AbLaw.MulN.isMonHom_mulA B n
  haveI : Surjective (𝟙 B ^ n : B ⟶ B).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_grpEnd k B (𝟙 B ^ n)).2
  obtain ⟨D, -, hD⟩ := GlobalTheory.DegKer.exists_mapDeg_of_isFinite _ _ (𝟙 B ^ n : B ⟶ B).left inferInstance inferInstance
  have hrank : ∀ y : B.left, (𝟙 B ^ n : B ⟶ B).left.finrank y = D :=
    fun y => GlobalTheory.SemiAbelianTower.finrank_eq_of_mapDeg _ hD y
  rw [hrank x]
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  obtain ⟨hfin, hmono, c, C, hc1, hgrow⟩ :=
    GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k B.left B.hom g hg H m s hH hs
  have e := GlobalTheory.UU.TorsionCount.nonempty_secEquiv B.hom _ hφ hH (n ^ 2) hiso
  obtain ⟨a, ha⟩ := GlobalTheory.T.finrank_sections_pullback_finite_flat_degree_bounds k B.left B.left B.hom (𝟙 B ^ n).left H m s hH hs D hrank hfin fun t => by
    obtain ⟨e⟩ := e t
    haveI := hfin (n ^ 2 * t)
    exact Module.Finite.equiv e
  rw [pow_mul]
  refine GlobalTheory.UU.degree_eq_pow_of_growth (fun t : ℕ => Module.finrank k (SecOnR B.hom (AbLaw.pw H t) ⊤)) g c C a _ (n ^ 2)
    hc1 hq hmono hgrow fun t => ?_
  obtain ⟨e₁⟩ := e (t + a)
  obtain ⟨e₂⟩ := e t
  exact ⟨(ha t).1.trans e₁.finrank_eq.ge, e₂.finrank_eq.le.trans (ha t).2⟩

end GlobalTheory.UU.MulDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulIsogeny

theorem bcMap_natCast_smul_id (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (n : ℕ) :
    bcMap L ((n : ℤ) • 𝟙 A) = (n : ℤ) • 𝟙 (baseChange L A) := by
  apply Subtype.ext
  simp only [bcMap, mk_hom, zsmul_hom, id_hom, zpow_natCast]
  exact GlobalTheory.MulFiniteFlat.pullback_map_mulA _ A.X n

theorem natCast_algClosed (k : Type) [Field k] [IsAlgClosed k] (A : AbVar k) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  have e : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X ^ n : A.X ⟶ A.X) := by
    rw [zsmul_hom, id_hom, zpow_natCast]
  obtain ⟨hfin, hfl⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp k) A.X A.ab n (Nat.one_le_iff_ne_zero.2 hn)
  have hmon : IsMonHom (𝟙 A.X ^ n : A.X ⟶ A.X) := e ▸ inferInstanceAs (IsMonHom ((n : ℤ) • 𝟙 A).hom)
  have hsurj : Surjective (𝟙 A.X ^ n : A.X ⟶ A.X).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A.X A.ab _ inferInstance hfin).2
  have hiso : IsIsogeny ((n : ℤ) • 𝟙 A) := by
    unfold IsIsogeny
    rw [e]
    exact ⟨hfin, hsurj⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso, e]
  exact GlobalTheory.UU.MulDegree.finrank_mul_eq k A.X A.dim n A.ab A.smooth hn _

theorem natCast (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  obtain ⟨h1, h2⟩ := natCast_algClosed (AlgebraicClosure K) (baseChange (AlgebraicClosure K) A) n hn
  obtain ⟨e1, e2⟩ := GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq K (AlgebraicClosure K) A A ((n : ℤ) • 𝟙 A)
  rw [bcMap_natCast_smul_id] at e1 e2
  exact ⟨e1.1 h1, e2.symm.trans h2⟩

theorem neg_one (K : Type) [Field K] (A : AbVar K) : IsIsogeny (-𝟙 A) ∧ deg (-𝟙 A) = 1 := by
  have hsq : (-𝟙 A) ≫ (-𝟙 A) = 𝟙 A := by simp
  have hsq' : (-𝟙 A).hom.left ≫ (-𝟙 A).hom.left = 𝟙 A.X.left := by
    rw [← Over.comp_left, ← comp_hom, hsq, id_hom, Over.id_left]
  haveI : IsIso (-𝟙 A).hom.left := ⟨⟨(-𝟙 A).hom.left, hsq', hsq'⟩⟩
  have hiso : IsIsogeny (-𝟙 A) := ⟨inferInstance, inferInstance⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

theorem mul_isogeny : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  intro K _ A n hn
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    exact natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
  · have e : n • 𝟙 A = ((n.natAbs : ℤ) • 𝟙 A) ≫ (-𝟙 A) := by
      rw [Preadditive.comp_neg, Category.comp_id, ← neg_smul, ← h]
    obtain ⟨h1, h2⟩ := natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
    obtain ⟨h3, h4⟩ := neg_one K A
    obtain ⟨h5, h6⟩ := GlobalTheory.T.isogeny_comp_and_degree_mul K A A A _ _ h1 h3
    rw [e]
    exact ⟨h5, by rw [h6, h2, h4, _root_.mul_one]⟩

end GlobalTheory.MulIsogeny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegreeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  first | exact @GlobalTheory.MulIsogeny.mul_isogeny | exact GlobalTheory.MulIsogeny.mul_isogeny | (intros; apply GlobalTheory.MulIsogeny.mul_isogeny <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    A.dim = B.dim → B.dim = C.dim →
      (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hAB hBC
  have hleft : (f ≫ g).hom.left = f.hom.left ≫ g.hom.left := by
    rw [comp_hom, Over.comp_left]
  have key : IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g := by
    constructor
    · rintro ⟨hfin, hsurj⟩
      have hs2 : Surjective (f.hom.left ≫ g.hom.left) := by rw [← hleft]; exact hsurj
      have hgs : Surjective g.hom.left := Surjective.of_comp f.hom.left g.hom.left
      have hgf : IsFinite g.hom.left := GlobalTheory.T.isFinite_of_surjective_of_dim_eq' K B C g hBC hgs
      have hker : Finite (ptMap (f ≫ g)).ker := (GlobalTheory.T.isFinite_iff_finite_ker' K A C (f ≫ g)).1 hfin
      have hle : (ptMap f).ker ≤ (ptMap (f ≫ g)).ker := by
        intro x hx
        rw [MonoidHom.mem_ker] at hx ⊢
        have hx' : x ≫ f.hom = 1 := hx
        show x ≫ (f ≫ g).hom = 1
        rw [comp_hom, ← Category.assoc, hx', MonObj.one_comp]
      have hfk : Finite (ptMap f).ker :=
        Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      have hff : IsFinite f.hom.left := (GlobalTheory.T.isFinite_iff_finite_ker' K A B f).2 hfk
      exact ⟨⟨hff, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f hAB hff⟩, ⟨hgf, hgs⟩⟩
    · rintro ⟨hf, hg⟩
      exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g hf hg).1
  refine ⟨key, ?_⟩
  by_cases h : IsIsogeny f ∧ IsIsogeny g
  · exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g h.1 h.2).2
  · have h0 : deg (f ≫ g) = 0 := by
      unfold deg; rw [if_neg (fun h' => h (key.1 h'))]
    rw [h0]
    rcases not_and_or.1 h with hf | hg
    · have : deg f = 0 := by unfold deg; rw [if_neg hf]
      rw [this, zero_mul]
    · have : deg g = 0 := by unfold deg; rw [if_neg hg]
      rw [this, mul_zero]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C), A.dim = B.dim → B.dim = C.dim → (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp | exact GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.FourBoundsAtBundles

end GlobalTheory.Fc.FourBoundsAtBundles

namespace GlobalTheory.Fc.FourBoundsAtBundles

open GlobalTheory.Fc.R1

theorem evW_of_atAll {Bd : BdT} {q : BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} (h : AtAll q 𝒜 σ) : Ind.EvW q 𝒜 σ :=
  Closed.of_all fun Fm _ hc => Ind.ev_of_atAll h Fm (w3_a hc)

end GlobalTheory.Fc.FourBoundsAtBundles
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormStalkIntegralFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistVal

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {T : CDVR} {io : c.F →+* T.Fr} (y' : IntFr Xo c T io)

theorem evI_idem_eq_one (h : evI y' (idem Z) ≠ 0) : evI y' (idem Z) = 1 := by
  have e := evI_mul y' (idem Z) (idem Z)
  rw [idem_mul_idem] at e
  exact mul_left_cancel₀ h (by rw [mul_one]; exact e.symm)

theorem val_inv {G₀ : WTZ E} (s : TwSec U x Z G₀) (he : evI y' (idem Z) = 1) :
    evI y' s.sig ≠ 0 ∧ evI y' s.inv ≠ 0 ∧ vV T.V (evI y' s.sig) + vV T.V (evI y' s.inv) = 0 := by
  have e : evI y' s.sig * evI y' s.inv = 1 := by rw [← evI_mul, s.mul_inv, he]
  have h1 : evI y' s.sig ≠ 0 := left_ne_zero_of_mul_eq_one e
  have h2 : evI y' s.inv ≠ 0 := right_ne_zero_of_mul_eq_one e
  refine ⟨h1, h2, ?_⟩
  rw [← vV_mul h1 h2, e]
  simp [vV]

theorem val_mul {G₀ G₁ : WTZ E} (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) (ht : vV T.V (evI y' t.sig) = 0) : vV T.V (evI y' (s.mul t).sig) = 0 := by
  show vV T.V (evI y' (s.sig * t.sig)) = 0
  rw [evI_mul, vV_mul (val_inv y' s he).1 (val_inv y' t he).1, hs, ht, add_zero]

theorem val_symm {G₀ : WTZ E} (s : TwSec U x Z G₀) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) : vV T.V (evI y' s.symm.sig) = 0 := by
  have h := (val_inv y' s he).2.2
  show vV T.V (evI y' s.inv) = 0
  omega

theorem exists_pow {e : ℤ} (s : TwSec U x Z (wtOf Dw 0 e)) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) : ∀ n : ℕ, ∃ t : TwSec U x Z (wtOf Dw 0 ((n : ℤ) * e)),
      vV T.V (evI y' t.sig) = 0 := by
  intro n
  induction n with
  | zero =>
    exact ⟨(s.mul s.symm).copy (by rw [add_neg_cancel, Nat.cast_zero, zero_mul, wtOf_zero]),
      val_mul y' s s.symm he hs (val_symm y' s he hs)⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero]; push_cast; ring_nf), val_mul y' t s he ht hs⟩

theorem exists_zpow (s : TwSec U x Z (wtOf Dw 0 1)) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) (k : ℤ) : ∃ t : TwSec U x Z (wtOf Dw 0 k), vV T.V (evI y' t.sig) = 0 := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · obtain ⟨t, ht⟩ := exists_pow y' s he hs n
    exact ⟨t.copy (by rw [mul_one]), ht⟩
  · have hneg : -wtOf Dw 0 1 = wtOf Dw 0 (-1) :=
      neg_eq_of_add_eq_zero_right (by rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero])
    obtain ⟨t, ht⟩ := exists_pow y' (s.symm.copy hneg) he (val_symm y' s he hs) n
    exact ⟨t.copy (by rw [mul_neg_one]), ht⟩

end GlobalTheory.TwistVal


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatement
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop.FlatDegProof

theorem flatDegAt_of_st {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) (hS : FlatDegreeSt) : FlatDegAt p i Y := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hL : Laws Y.U (xiR D) := GlobalTheory.LawsDeep.laws_deep D p.T _ Y _ _ p.fw.laws hj hY.1
  obtain ⟨hd, χ, hχ, h1, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q p.fw.laws.pins.1 p.Del p.h0
  have := hS D.host.E p.T.Q.H hH χ hχ (p.T.Q.Dw ((i : ℕ) + 1)) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) hL
  unfold FlatDegAt
  rwa [← h1]

end GlobalTheory.CovTop.FlatDegProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ModulusNorm

theorem absNorm_eq_of_two_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w ≠ w')
    (h : w'.under (𝓞 F) = w.under (𝓞 F)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal := by
  set p := (w.under (𝓞 F)).asIdeal with hp
  have l1 : w.asIdeal.LiesOver p := ⟨rfl⟩
  have l2 : w'.asIdeal.LiesOver p := ⟨by rw [hp, ← h]; rfl⟩
  have f1 := Ideal.absNorm_pow_inertiaDeg p w.asIdeal
  have f2 := Ideal.absNorm_pow_inertiaDeg p w'.asIdeal
  have c1 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have c2 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  have m1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l1.over)
  have m2 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l2.over)
  have cop : w.asIdeal ⊔ w'.asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun e => hne (HeightOneSpectrum.ext e)
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal * w'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_coprime cop]; exact le_inf m1 m2
  have hd := map_dvd Ideal.absNorm (Ideal.dvd_iff_le.2 hle)
  rw [map_mul, Ideal.absNorm_algebraMap, ← f1, ← f2, ← pow_add,
    ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, h2] at hd
  have hq : 1 < Ideal.absNorm p := by
    rcases Nat.lt_or_ge 1 (Ideal.absNorm p) with h' | h'
    · exact h'
    · exfalso
      interval_cases hh : Ideal.absNorm p
      · exact (w.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 hh)
      · exact (w.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 hh)
  have := (Nat.pow_dvd_pow_iff_le_right hq).1 hd
  have e1 : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by omega
  rw [← f1, e1, pow_one]

variable {D : D7}

theorem conjPl_ne_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e w) : Formalism.DivisionValues.conjPl w ≠ w := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  exact GlobalTheory.FunObj.conjPrime_ne_of_isIdempotentAt he

theorem absNorm_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e w) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal :=
  absNorm_eq_of_two_over D.sp.cm.deg2 (conjPl_ne_of_isIdemAt he).symm (GlobalTheory.ChainTw.ParInv.under_conjPl w)

variable {T : Type} {L : LevCh D T}

theorem absNorm_condE (P : Places L) : Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨e, he⟩ := P.w_split v hv
  rw [map_pow, absNorm_of_isIdemAt he, P.under_w hv]

end GlobalTheory.ModulusNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlace
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

section BaseChange

variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}

theorem map_mem_nabAtr_comp (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsFullLattice E M) {x : VV K₀ lam} (hx : x ∈ nabAtr emb lam M) :
    (⟨MvPolynomial.map f x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam _ x.2⟩ : VV K lam) ∈
      nabAtr (fun τ => f.comp (emb τ)) lam M := by
  classical
  unfold nabAtr nabK at hx ⊢
  rw [Submodule.mem_comap] at hx ⊢
  change MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)
  change x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx
  refine GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsFullLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    by
      change IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M))
        (Formalism.UG.bc f (inside₂ K₀ n (C τ)))
      rw [← GlobalTheory.NabBC.invTr_bc]
      refine GlobalTheory.DualWeylDual.isBasisAt_dualFr w
        (tauLatLattice E K ι n _ τ M hM).fg ?_
      rw [GlobalTheory.NabBC.tauLat_comp]
      exact GlobalTheory.NabBC.isBasisAt_span_vmap f w₀ w hw (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  have hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) :=
    GlobalTheory.NabBC.mem_localization_of_mem' _ hx
  rw [L0] at hx0
  obtain ⟨g, ⟨s, hs, hsg⟩, hg⟩ := hx0
  rw [L1]
  refine ⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩
  · refine (congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_
    have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
    have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
    have h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) :=
      Submodule.subset_span ⟨_, hsg, rfl⟩
    rw [h1, ← h2] at h3
    have h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n)) := by
      ext y
      simp [MvPolynomial.map_id]
    rw [h4, Submodule.span_eq] at h3
    exact h3
  · change actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1
    rw [← GlobalTheory.ValCmp.use₂]
    exact congrArg (MvPolynomial.map f) hg

end BaseChange

end GlobalTheory.BigOn.Exp.SerBase

namespace GlobalTheory.BigOn.Exp.SerBase

end GlobalTheory.BigOn.Exp.SerBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_free_baseChange_rigid : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.BaseChange ∧
      GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro hH
  have h : GlobalTheory.Published.AbelianDeRhamStructure ∧
      GlobalTheory.Published.CrystallineDeRham :=
    GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH
  obtain ⟨⟨hfree, -, hbc⟩, hcrys⟩ := h
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hbc, GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocycles
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isCoc_iff_mem_cocycles : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := by
  intro p k _ d G c μ hμ s
  have hcomp : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s :=
    fun n => (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.1 n s
  have hnil := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).1
  have hinj := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).2
  have hcob : ∀ n, evA k _ (hnil n) (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord p k d G c μ hμ n (hnil n)).1 s
  have hswap : ∀ n, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n).2.2.1 s
  constructor
  · rintro ⟨h2, hs⟩ n
    refine ⟨mem_symCocycles.2 ⟨?_, ?_⟩, hcomp n⟩
    · rw [← hcob n, h2, map_zero]
    · rw [← hswap n, hs]
  · intro h
    refine ⟨?_, ?_⟩
    · refine hinj _ fun n hn => ?_
      have e := hcob n
      rw [(mem_symCocycles.1 (h n).1).1] at e
      exact e
    · obtain ⟨t, -, ht⟩ := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => c.ev₂ n s) hcomp
      have h1 := ht (Katz.swap s) fun n => by
        rw [hswap n]; exact (mem_symCocycles.1 (h n).1).2
      have h2 := ht s fun n => rfl
      rw [h1, h2]

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocyclesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := by
  first | exact @GlobalTheory.Katz.isCoc_iff_mem_cocycles | exact GlobalTheory.Katz.isCoc_iff_mem_cocycles | (intros; apply GlobalTheory.Katz.isCoc_iff_mem_cocycles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentity
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree

namespace GlobalTheory.BigTop.Fun.OneSqTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem big_std : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => Formalism.L2.Theta.IsStdChar D ch.W.ψ (-1) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s _ hi _ => by
    show Formalism.L2.Theta.IsStdChar _ _ (-1)
    rw [hi.weil.ψ]; exact s.std⟩⟩

end GlobalTheory.BigTop.Fun.OneSqTie
end
end
