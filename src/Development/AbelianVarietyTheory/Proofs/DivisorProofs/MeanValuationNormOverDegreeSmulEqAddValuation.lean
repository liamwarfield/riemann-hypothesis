module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConvolutionEqDerivativeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum

theorem IsMinPol.scaleRoots_eq {K : Type} [Field K] {σ : K →+* ℂ} {β : ℂ} {u : K} {p q : K[X]}
    (hp : IsMinPol σ β p) (hq : IsMinPol σ (σ u * β) q) (hu : u ≠ 0) : q = p.scaleRoots u := by
  let := σ.toAlgebra
  have ep := hp.eq_minpoly
  have eq := hq.eq_minpoly
  have hr0 : (p.scaleRoots u).eval₂ σ (σ u * β) = 0 := scaleRoots_eval₂_eq_zero σ hp.2.2
  have hs0 : (q.scaleRoots u⁻¹).eval₂ σ β = 0 := by
    have := scaleRoots_eval₂_eq_zero σ (s := u⁻¹) hq.2.2
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul] at this
  have d1 : q ∣ p.scaleRoots u := by
    rw [eq]; exact minpoly.dvd K (σ u * β) hr0
  have d2 : p ∣ q.scaleRoots u⁻¹ := by
    rw [ep]; exact minpoly.dvd K β hs0
  have hq0 : q.scaleRoots u⁻¹ ≠ 0 := scaleRoots_ne_zero hq.1.ne_zero _
  have le1 : p.natDegree ≤ q.natDegree := by
    have := natDegree_le_of_dvd d2 hq0
    rwa [natDegree_scaleRoots] at this
  exact (eq_of_monic_of_dvd_of_natDegree_le hq.1 ((monic_scaleRoots_iff u).2 hp.1) d1
    (by rw [natDegree_scaleRoots]; exact le1)).symm

end GlobalTheory.FunObj.SqNum

theorem GlobalTheory.FunObj.SqNum.meanVal_vw_smul : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  intro K _ _ _ σ β u p q hp hq hβ hu w
  obtain ⟨hc, hd⟩ := hp.ne_zero hβ
  rw [hp.scaleRoots_eq hq hu]
  unfold GlobalTheory.FunObj.SqNum.meanVal_vw
  rw [natDegree_scaleRoots, coeff_scaleRoots, Nat.sub_zero]
  have hm : vw w (p.coeff 0 * u ^ p.natDegree) = vw w (p.coeff 0) + p.natDegree * vw w u := by
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hc)
        (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 (pow_ne_zero _ hu)),
      ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
  rw [hm]
  have : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuationStatement
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_smul | exact GlobalTheory.FunObj.SqNum.meanVal_vw_smul | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousProd
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice

namespace GlobalTheory.ZeroCycleHt

theorem linSubst_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f g : MvPolynomial (Fin B × Fin N) R) : linSubst M (f * g) = linSubst M f * linSubst M g := by
  simp [linSubst]

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Function.Surjective w.mulVec) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  classical
  choose x hx using fun j : Fin N => hw (Pi.single j 1)
  refine ⟨Matrix.of fun k j => x j k, ?_⟩
  ext i j
  have := congrFun (hx j) i
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [this, Pi.single_apply]

theorem formHeight_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ δ' : ℕ)
    {w : Matrix (Fin N) (Fin n) F} {P : Matrix (Fin n) (Fin N) F} (hP : w * P = 1)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (hg : g ≠ 0)
    (ha : IsMultiHomogeneous a f) (ha' : IsMultiHomogeneous a' g) :
    formHeight (δ + δ') w A (f * g) = formHeight δ w A f + formHeight δ' w A g := by
  have hlf := GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hlg := GlobalTheory.HeightUnique.linSubst_ne_zero hP hg
  have hfin : ∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w (f * g))) =
      ∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w f)) +
        ∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w g)) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite _ hlf) (gauss_abs_log_support_finite _ hlg)]
    refine finsum_congr fun v => ?_
    rw [linSubst_mul, gauss_abs_mul v _ _ hlf hlg,
      Real.log_mul (gauss_abs_pos_of_ne_zero v _ hlf).ne' (gauss_abs_pos_of_ne_zero v _ hlg).ne']
  have hne : ∀ (σ : F →+* ℂ) {h : MvPolynomial (Fin B × Fin N) F}, h ≠ 0 →
      linSubst (A σ) (MvPolynomial.map σ h) ≠ 0 := fun σ h hh =>
    GlobalTheory.HeightUnique.linSubst_ne_zero ((A σ).mul_nonsing_inv (hA σ).isUnit) fun h0 =>
      hh (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  have hinf : ∀ σ : F →+* ℂ, blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ (f * g))) =
      blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
        blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ g)) := by
    intro σ
    rw [map_mul, linSubst_mul]
    exact sphere_mean_mul_multihomogeneous Closed.sphereLogIntegrable B N a a' _ _ (hne σ hf) (hne σ hg)
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a f ha σ))
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a' g ha' σ))
  unfold formHeight
  rw [hfin]
  simp only [hinf, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
  ring

theorem formHeight_one {F : Type} [Field F] [NumberField F] {B N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) :
    formHeight 0 w A (1 : MvPolynomial (Fin B × Fin N) F) = 0 := by
  have h1 : ∀ v : FinitePlace F, ReciprocityTheory.MultiplicativeHeights.gaussAbs v (1 : MvPolynomial (Fin B × Fin n) F) = 1 := fun v => by
    simpa using GlobalTheory.HeightUnique.gaussAbs_C (σ := Fin B × Fin n) v (1 : F)
  unfold formHeight
  simp [linSubst, h1, blockSphereMean]

end GlobalTheory.ZeroCycleHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSum
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem nat_card_monoDeg_fin (D a : ℕ) (hD : 1 ≤ D) :
    Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  classical
  rw [Nat.card_eq_fintype_card, MonoDeg.card_eq_card_finsuppAntidiag,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show a + (d + 1) - 1 = a + d by omega, show d + 1 + a - 1 = a + d by omega,
    show d + 1 - 1 = d by omega]
  exact Nat.choose_symm_add

theorem sum_range_choose_mul_sub (d n : ℕ) :
    ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) = (n + d + 1).choose (d + 2) := by
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    have h1 : ∑ a ∈ Finset.range n, (a + d).choose d * (n + 1 - a) =
        ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) +
          ∑ a ∈ Finset.range n, (a + d).choose d := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < n := Finset.mem_range.mp ha
      rw [show n + 1 - a = (n - a) + 1 by omega, Nat.mul_succ]
    rw [Finset.sum_range_succ, h1, ih, show n + 1 - n = 1 by omega, mul_one, add_assoc,
      ← Finset.sum_range_succ, Nat.sum_range_add_choose,
      show n + 1 + d + 1 = (n + d + 1) + 1 by omega, Nat.choose_succ_succ' (n + d + 1) (d + 1)]
    ring_nf

theorem monomial_counts : ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T →
    (∀ a : ℕ, Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1)) ∧
    Nat.card (Σ a : Fin (T - D), MonoDeg (Fin D) a) = (T - 1).choose D ∧
    (D + 1) * ∑ a ∈ Finset.range (T - D), (a + D - 1).choose (D - 1) * (T - a) =
      (T - 1).choose D * (T + D * (D + 1)) := by
  intro D T hD hT
  have h1 := fun a => nat_card_monoDeg_fin D a hD
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, T = d + 2 + m := ⟨T - (d + 2), by omega⟩
  have hTD : d + 2 + m - (d + 1) = m + 1 := by omega
  have hT1 : d + 2 + m - 1 = m + d + 1 := by omega
  have hsub : ∀ a, a + (d + 1) - 1 = a + d := fun a => by omega
  simp only [hsub, show d + 1 - 1 = d by omega] at h1 ⊢
  have hsum : ∑ a ∈ Finset.range (m + 1), (a + d).choose d = (m + d + 1).choose (d + 1) :=
    Nat.sum_range_add_choose m d
  refine ⟨h1, ?_, ?_⟩
  · rw [Nat.card_sigma, hT1]
    simp only [h1]
    rw [← hsum, hTD, Finset.sum_range (fun a => (a + d).choose d)]
  · rw [hTD, hT1]
    have hw : ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (d + 2 + m - a) =
        ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (m + 1 - a) +
          (d + 1) * ∑ a ∈ Finset.range (m + 1), (a + d).choose d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < m + 1 := Finset.mem_range.mp ha
      rw [show d + 2 + m - a = (m + 1 - a) + (d + 1) by omega]
      ring
    rw [hw, sum_range_choose_mul_sub, hsum]
    have key := Nat.add_one_mul_choose_eq (m + d + 1) (d + 1)
    rw [show m + 1 + d + 1 = m + d + 1 + 1 by omega]
    nlinarith [key]

end GlobalTheory.HSShort
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCountsDegreeAndWeightedSumStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_counts_degree_and_weighted_sum : ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T → (∀ a : ℕ, Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1)) ∧ Nat.card (Σ a : Fin (T - D), MonoDeg (Fin D) a) = (T - 1).choose D ∧ (D + 1) * ∑ a ∈ Finset.range (T - D), (a + D - 1).choose (D - 1) * (T - a) = (T - 1).choose D * (T + D * (D + 1)) := by
  first | exact @GlobalTheory.HSShort.monomial_counts | exact GlobalTheory.HSShort.monomial_counts | (intros; apply GlobalTheory.HSShort.monomial_counts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmod
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.CurveDevissage

theorem interNum_one_nonneg {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k (X := V))) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : N.IsLB)
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra k Γ(Z, ⊤)],
      (∀ r : k, i.appTop (algebraMap k Γ(V, ⊤) r) = algebraMap k Γ(Z, ⊤) r) →
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection k (N.pull i) 1)
    (F : V.Modules) (hF : QCoh.IsFiniteQC F) : 0 ≤ interNum k F ![N] := by
  have := isNoetherian_of_isProjOver hp
  have hL : ∀ i, ((![N] : Fin 1 → LB V) i).IsLB := fun i => by fin_cases i; exact hN
  refine QCoh.devissage V (fun F => 0 ≤ interNum k F ![N])
    (fun F hF => (interNum_eq_zero_of_isZero k hF hL).ge) (fun S hS h₁ h₃ p₁ p₃ => ?_)
    (fun Z hZ _ G hG => ?_) F hF
  · rw [interNum_shortExact hS hL
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)]
    exact add_nonneg p₁ p₃
  · have := isIntegral_red hZ
    letI := algebraΓAlong k (redι Z)
    have hi := appTop_algebraMap_along k (redι Z)
    have hpZ : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hM := LB.isLB_pull hN (redι Z)
    have e : (fun i => ((![N] : Fin 1 → LB V) i).pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    have e' : (fun _ : Fin 1 => N.pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    rw [interNum_pushforward_of_isClosedImmersion hi G hL, e]
    have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ 1 :=
      (redι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hd
    rcases hdZ.eq_or_lt with h1 | h1
    · rw [VB.interNum_one_eq_genRank_mul k _ hpZ h1 G _ hM]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      have := h _ (redι Z) hi h1
      rwa [topSelf_def, e'] at this
    · refine (interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom k _) G hpZ ?_
        fun i => by fin_cases i; exact hM).ge
      rw [Fintype.card_fin]
      exact (QCoh.suppDim_le G).trans_lt h1

theorem degOfRank_nonneg : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) (X := V)) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  intro p _ V _ hp hd N hN h
  have := Twist.isFiniteQC_twist (F := structureModule V) hN
  have h1 := interNum_one_nonneg hp hd hN (fun Z i _ _ _ _ hZ => h Z i hZ)
    (twist (structureModule V) N) this
  have h2 := interNum_twist_cons (ZMod p) (structureModule V) (P := ![]) hN isEmptyElim
  have h3 : chi (ZMod p) (twist (structureModule V) N) = chi (ZMod p) (toMod N) :=
    chi_congr _ (Twist.unitTwistIso N)
  have h4 : interNum (ZMod p) (twist (structureModule V) N) ![N] =
    chi (ZMod p) (twist (structureModule V) N) - chi (ZMod p) (structureModule V) :=
    h2.trans (congrArg₂ (· - ·) (interNum_of_isEmpty _ _ _) (interNum_of_isEmpty _ _ _))
  rw [degOfRank]
  push_cast
  linarith

end GlobalTheory.CurveDevissage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmodStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) (X := V)) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  first | exact @GlobalTheory.CurveDevissage.degOfRank_nonneg | exact GlobalTheory.CurveDevissage.degOfRank_nonneg | (intros; apply GlobalTheory.CurveDevissage.degOfRank_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarishChandraReproducingFunctionGLinfinity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarishChandraReproducingFunctionGLinfinity
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic

namespace GlobalTheory.HCAlphaGLC

section

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def topE : glG E a ≃ₜ* GL (Fin a) (Cinf E) where
  toMulEquiv := Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  intro E _ _ _ a L _ W hW X hX N _ _ μ hμ
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨d, b, P, hPm, -, hP⟩ := GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian E a p hp0
  let e := topE E a
  letI : MeasurableSpace (glG E a) := borel _
  haveI : BorelSpace (glG E a) := ⟨rfl⟩
  let μ' : Measure (glG E a) := μ.map e.symm
  have hH : μ'.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  obtain ⟨α', -, hc, hs, hα⟩ := @GlobalTheory.T.exists_smooth_convolution_eq_derivative (Matrix (Fin a) (Fin a) (Cinf E)) _ _ _ _ (glG E a) (glL E a) (glH E a) d b P hPm _ (by exact ⟨rfl⟩) μ' (by exact hH) []
  refine ⟨α' ∘ e.symm, ?_, ?_, fun φ hφ g => ?_⟩
  · exact hc.comp e.symm.continuous
  · exact hs.comp_homeomorph e.symm.toHomeomorph
  obtain ⟨hf, h0⟩ := (mem_solG _ _).1 (hP φ (hp φ hφ) g)
  have h1 := hα ⟨_, hf⟩ h0 1
  have hm : μ' = μ.map e.symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [hm, integral_map_equiv] at h1
  simp only [one_mul, List.foldr_nil] at h1
  exact h1.trans (by simp [glRes])

end

end GlobalTheory.HCAlphaGLC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarishChandraReproducingFunctionGLinfinityStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harishChandra_reproducing_function_GLinfinity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  first | exact @GlobalTheory.HCAlphaGLC.exists_alpha | exact GlobalTheory.HCAlphaGLC.exists_alpha | (intros; apply GlobalTheory.HCAlphaGLC.exists_alpha <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGL
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite →
    ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧
      HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g :=
  GlobalTheory.T.exists_harishChandra_reproducing_function_GLinfinity

end GlobalTheory.HCAlphaGL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGLStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_exists_reproducing_testFunction_GL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  first | exact @GlobalTheory.HCAlphaGL.exists_alpha | exact GlobalTheory.HCAlphaGL.exists_alpha | (intros; apply GlobalTheory.HCAlphaGL.exists_alpha <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenComapProdLev
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.ProdOpen

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := _root_.GlobalTheory.FunObj.inBasis_mem_KO (n := n) β x hx w

theorem tendsto_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ)).1 : Matrix (Fin n') (Fin n') (Kw w))) (𝓝 1) (𝓝 1) := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (GlobalTheory.LocalData.norm_resChar_lt_one w)
  have hN : Formalism.MainNotions.S.Loc.resChar w ^ k ≠ 0 := pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero
  filter_upwards [eventually_cong_mat β hN hf (map_one _)] with κ ⟨z, hz, e⟩
  change (β⁻¹ * Lev.finE V κ * β).1 - 1 = _ at e
  have e2 := congr_fun (congr_fun e (finCongr h i)) (finCongr h j)
  rw [Matrix.sub_apply, Matrix.smul_apply, sub_eq_iff_eq_add] at e2
  have e3 : cpt w ((1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) (finCongr h i) (finCongr h j)) =
      (1 : Matrix (Fin n') (Fin n') (Kw w)) i j := by
    simp only [Matrix.one_apply, (finCongr h).injective.eq_iff]
    split_ifs <;> simp
  have hz1 : ‖cpt w (z (finCongr h i) (finCongr h j))‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((mem_OA_iff _).1 (hz _ _) w)
  rw [dist_eq_norm, inBasis_apply, e2, map_add (f := _), e3, add_sub_cancel_right, map_nsmul, nsmul_eq_mul, norm_mul,
    Nat.cast_pow, norm_pow]
  calc ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * ‖cpt w (z (finCongr h i) (finCongr h j))‖
      ≤ ‖((Formalism.MainNotions.S.Loc.resChar w : ℕ) : Kw w)‖ ^ k * 1 := by gcongr
    _ < ε := by rwa [mul_one]

theorem tendsto_inBasis (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) :
    Tendsto (fun κ : GA D V => inBasis h β w (Lev.finE V κ)) (𝓝 1) (𝓝 1) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hinv : Tendsto (fun κ : GA D V => κ⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv.tendsto (1 : GA D V))
  have h2 : Tendsto (fun κ : GA D V => ((inBasis h β w (Lev.finE V κ))⁻¹).1) (𝓝 1) (𝓝 1) := by
    have := (tendsto_inBasis_val V h β w).comp hinv
    refine this.congr fun κ => ?_
    simp only [Function.comp_apply, map_inv]
  have h3 := (tendsto_inBasis_val V h β w).prodMk_nhds (MulOpposite.continuous_op.tendsto _ |>.comp h2)
  convert h3 using 2
  · ext <;> simp [Units.embedProduct]
  · rw [map_one]; rfl

theorem isOpen_comap_prodLev : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))),
    (∀ w, IsOpen (K w : Set (GL (Fin (n' w)) (Kw w.1)))) →
      IsOpen (((prodLev β P h K).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  intro D V β P n' h K hK
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hP : ∀ w : P, ∀ᶠ κ in 𝓝 (1 : GA D V), inBasis (h w) β w (Lev.finE V κ) ∈ K w := fun w =>
    tendsto_inBasis V (h w) β w.1 ((hK w).mem_nhds (one_mem _))
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β ∅, Filter.eventually_all.2 hP] with κ hh h3
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 h3,
    Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β _ hh.2.1 w'⟩

end GlobalTheory.FunObj.ProdOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem conj_mem_glLatCong {Λ Λ' : Submodule 𝒪[k] (D → k)} {u : kˣ} (G : GL D k)
    (hG : ∀ x, x ᵥ* G.val ∈ Λ' ↔ x ∈ Λ) {g : GL D k} (hg : g ∈ glLatCong u Λ') :
    G * g * G⁻¹ ∈ glLatCong u Λ := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hG, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← vecMul_vecMul, hg.1, hG]
  · have h1 := hg.2 _ ((hG x).2 hx)
    rw [mem_smul_lat] at h1 ⊢
    rw [← hG]
    convert h1 using 1
    rw [Units.smul_def, Units.smul_def, smul_vecMul, vecMul_vecMul, vecMul_vecMul, sub_mul, mul_sub,
      ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, mul_one, one_mul]

theorem vecMul_diagGL_mem (b c d : D → kˣ) (h : ∀ j, d j = b j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat d ↔ x ∈ diagLat b := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem mem_glLatCong_of_smul {Λ : Submodule 𝒪[k] (D → k)} {u v : kˣ} {g : GL D k}
    (hg : g ∈ glLatCong u (v • Λ)) : g ∈ glLatCong u Λ := by
  have hm : ∀ x, v • x ∈ v • Λ ↔ x ∈ Λ := fun x => by rw [mem_smul_lat, inv_smul_smul]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hm, ← hm x, ← hg.1 (v • x), Units.smul_def v x, smul_vecMul, ← Units.smul_def v (x ᵥ* g.val)]
  · have h1 := hg.2 _ ((hm x).2 hx)
    rw [mem_smul_lat, mem_smul_lat] at h1
    rw [mem_smul_lat]
    convert h1 using 1
    rw [smul_comm v⁻¹, Units.smul_def v, smul_vecMul, ← Units.smul_def v, inv_smul_smul]

theorem invT_mem_of_dual {u : kˣ} {c : D → kˣ} {g : GL D k} (hg : g ∈ glLatCong u (dualLat (diagLat c))) :
    invT g ∈ glLatCong u (diagLat c) ∧ gdet (invT g) ∈ unitCong u := by
  rw [dualLat_diagLat] at hg
  have h1 := GlobalTheory.FunObj.GivenAdm.invT_mem_glLatCong (conj_mem_glLatCong (Λ := stdLat k D)
    (diagGL fun j => (c j)⁻¹) (vecMul_diagGL_mem 1 _ _ (by simp)) hg)
  have h2 : invT (diagGL fun j => (c j)⁻¹) = diagGL c := by
    rw [← _root_.inv_inj]
    refine Units.ext ?_
    rw [invT_inv_val, diagGL_val, diagonal_transpose]
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp [diagGL_val]
  rw [map_mul, map_mul, map_inv, h2] at h1
  constructor
  · have h3 := conj_mem_glLatCong (Λ := diagLat c) (diagGL c)⁻¹ (fun x => by
      rw [stdLat, ← vecMul_diagGL_mem 1 c c (by simp), vecMul_vecMul, Units.inv_mul, vecMul_one]) h1
    simpa [mul_assoc] using h3
  · have h3 := GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong h1
    rwa [gdet_mul, gdet_mul, show gdet (diagGL c)⁻¹ = (gdet (diagGL c))⁻¹ from map_inv _ _,
      mul_inv_cancel_comm] at h3

theorem HasDepth.mul_glLatCong {A : Type*} {ϖ : kˣ} {e : ℕ} {Λ : Submodule 𝒪[k] (D → k)}
    {Ψ : Matrix A D k → ℂ} (h : HasDepth ϖ e Λ Ψ) {g : GL D k} (hg : g ∈ glLatCong (ϖ ^ e) Λ)
    (Y : Matrix A D k) : Ψ (Y * g.val) = Ψ Y := by
  have hr : ∀ (M : Matrix D D k) i, (Y * M).row i = Y.row i ᵥ* M := fun M i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  by_cases hY : Y ∈ matLat A Λ
  · rw [show Y * g.val = Y + Y * (g.val - 1) by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]]
    exact h.2 _ _ fun i => by rw [hr]; exact hg.2 _ (hY i)
  · rw [h.1 _ hY, h.1 _ fun H => hY fun i => (hg.1 _).1 (by rw [← hr]; exact H i)]

theorem hasDepth_phiA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype D] [DecidableEq D] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (ϖ : kˣ) (e : ℕ) (c : D → kˣ) (Ψ : Matrix A' D k → ℂ) (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν)
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) :
    HasDepth ϖ e (latA ϖ e (diagLat c)) (phiA μ σ ν ϖ e (diagLat c) Ψ) := by
  have hlt : valuation k ((ϖ ^ e : kˣ) : k) < 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' (hϖ ▸ uniformizer_lt_one) (by omega)
  have key : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → ∃ κ ∈ glLatCong (ϖ ^ e) (latA ϖ e (diagLat c)),
        X + Z = X * κ.val := by
    rw [latA, dualLat_diagLat, smul_diagLat]
    exact GlobalTheory.PrimFrameMove.exists_glLatCong_move k A D _ _ hlt
  have prim : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := by
    intro X Z hX hZ
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    rw [h]
    exact GlobalTheory.SplitFlip.Model.isPrimFrame_mul hX κ hκ.1
  refine ⟨fun X hX => if_neg fun h => hX h.2.1, fun X Z hZ => ?_⟩
  by_cases hX : IsPrimFrame (latA ϖ e (diagLat c)) X
  · unfold phiA
    rw [if_pos hX, if_pos (prim X Z hX hZ)]
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    obtain ⟨h1, h2⟩ := invT_mem_of_dual (mem_glLatCong_of_smul hκ)
    obtain ⟨g, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
    have h3 : X0 k σ * (invT g).val * κ.val = X0 k σ * (invT (g * invT κ)).val := by
      rw [map_mul, invT_invT, Units.val_mul, Matrix.mul_assoc]
    have hf := @splitTheta_fFun_frameFirstBlock_mul k _ _ _ _ A A' D _ _ _ _ _ _ _ _ μ hμ σ ν Ψ
    rw [h, h3, hf, hf, gdet_mul, map_mul, apow_mul, hν _ h2, apow_of_valuation_eq_one h2.1,
      mul_one, mul_one]
    congr 1
    simp only [smallF, Units.val_mul, ← Matrix.mul_assoc, HasDepth.mul_glLatCong hΨ h1]
  · have hX' : ¬ IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := fun h => hX (by
      simpa using prim _ (-Z) h (neg_mem hZ))
    unfold phiA
    rw [if_neg hX, if_neg hX']

end GlobalTheory.FrameDepth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GamOrdNeZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def gfcToGf (V : HSp D) : GfC V →* Bridge.Gf V := (finHom V).rangeRestrict.comp (GfC V).subtype

theorem gfcToGf_surjective (V : HSp D) : Function.Surjective (gfcToGf V) := by
  rintro ⟨_, h, rfl⟩
  obtain ⟨k, hk, e⟩ := GlobalTheory.VolHeckeCompare.exists_finite_part V h
  exact ⟨⟨k, hk⟩, Subtype.ext e⟩

theorem bc_swapAE_injective (n : ℕ) :
    Function.Injective (Formalism.UG.bc (Lev.swapAE D) : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →* _) := by
  intro a b e
  apply Units.ext
  have h := congrArg Units.val e
  exact Matrix.map_injective (f := Lev.swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem finG_injective (V : HSp D) : Function.Injective (finG V) := by
  intro a b e
  have e' : finHom V a.1 = finHom V b.1 := bc_swapAE_injective V.rank e
  have h1 : finHom V (a.1⁻¹ * b.1) = 1 := by rw [map_mul, map_inv, e', inv_mul_cancel]
  have := GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (mul_mem (inv_mem a.2) b.2) h1
  exact Subtype.ext (inv_mul_eq_one.1 this)

def finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (K.comap (Formalism.UG.bc (Lev.swapAE D))).comap (Bridge.Gf V).subtype

theorem mem_finLev_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (g : GfC V) :
    gfcToGf V g ∈ finLev V K ↔ g ∈ K.comap (finG V) := Iff.rfl

theorem isOpenLev_finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsCO V K) :
    GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V (finLev V K) := by
  have e : (((finLev V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) =
      ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
  rw [e]
  exact hK.1

theorem finite_finCl (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) : Finite (FinCl V K) := by
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV (finLev V K) (isOpenLev_finLev V K hK)
  choose x hx using fun a => gfcToGf_surjective V (c a)
  refine Finite.of_surjective (fun a : Fin m => (DoubleCoset.mk (ratFin V) (K.comap (finG V)) (x a) : FinCl V K)) ?_
  intro q
  rw [← DoubleCoset.out_eq' q]
  set y := Quotient.out q
  obtain ⟨a, γ, k, e⟩ := hc (gfcToGf V y)
  obtain ⟨z, hz⟩ := gfcToGf_surjective V (Bridge.ratF V γ)
  refine ⟨a, (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨z, ?_, (x a)⁻¹ * z⁻¹ * y, ?_, by group⟩⟩
  · have hz' : finHom V z.1 = finHom V γ.1 := congrArg Subtype.val hz
    refine ⟨γ.1, γ.2, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V γ.1) = Formalism.UG.bc (Lev.swapAE D) (finHom V z.1)
    rw [hz']
  · refine (mem_finLev_iff V K _).1 ?_
    have h1 : gfcToGf V ((x a)⁻¹ * z⁻¹ * y) = (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y := by
      simp only [map_mul, map_inv]
    have h2 : (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y = (k : Bridge.Gf V) := by
      simp only [hx a, hz, e]; group
    exact (congrArg (· ∈ finLev V K) (h1.trans h2)).mpr k.2

theorem continuous_finHom (V : HSp D) : Continuous (finHom V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  exact (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ

theorem gamOrd_ne_zero (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) (x : GfC V) : gamOrd V K x ≠ 0 := by
  set C : Set (Af D.host.F ⊗[D.host.F] D.host.E) :=
    ⋃ p : Fin V.rank × Fin V.rank, (fun g : GA D V => (finHom V g).1 p.1 p.2) '' (Lev.levA V K : Set (GA D V)) with hCdef
  have hC : IsCompact C := isCompact_iUnion fun p =>
    hK.2.image ((Units.continuous_val.comp (continuous_finHom V)).matrix_elem p.1 p.2)
  have hCJ : ∀ k ∈ finLev V K, ∀ i j, (k : Bridge.Gf V).1.1 i j ∈ C := by
    intro k hk i j
    obtain ⟨g, rfl⟩ := gfcToGf_surjective V k
    exact Set.mem_iUnion.2 ⟨(i, j), g.1, ⟨g.2, (mem_finLev_iff V K g).1 hk⟩, rfl⟩
  have hs := GlobalTheory.RepsObj.finite_stab V hV (finLev V K) hC hCJ (gfcToGf V x)
  have hq : ∀ γ : ratFin V, ∃ q : GQ V, Lev.finE V q.1 = finG V γ.1 := fun γ => by
    obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 γ.2
    exact ⟨⟨q, hq⟩, e⟩
  choose q hq using hq
  have hfin : Finite {γ : ratFin V // finG V (x⁻¹ * γ * x) ∈ K} := by
    refine Finite.of_injective (β := Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x))
      (fun γ => ⟨q γ.1, ?_⟩) ?_
    · have e0 : Bridge.ratF V (q γ.1) = gfcToGf V γ.1.1 :=
        Subtype.ext (bc_swapAE_injective V.rank (hq γ.1))
      have e1 : (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) = gfcToGf V (x⁻¹ * γ.1.1 * x) := by
        simp only [e0, map_mul, map_inv, MulAut.conj_inv_apply]
      show (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) ∈ finLev V K
      exact (congrArg (· ∈ finLev V K) e1).mpr ((mem_finLev_iff V K _).2 γ.2)
    · intro γ γ' e
      have e1 : Lev.finE V (q γ.1).1 = Lev.finE V (q γ'.1).1 := by
        have := congrArg (fun s : Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x) => Lev.finE V s.1.1) e
        exact this
      rw [hq, hq] at e1
      exact Subtype.ext (Subtype.ext (finG_injective V e1))
  refine Nat.card_ne_zero.2 ⟨⟨⟨1, one_mem _⟩, ?_⟩, hfin⟩
  simp only [mul_one, inv_mul_cancel, map_one]
  exact one_mem K

theorem finite_finCl_and_gamOrd : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))),
    (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) → IsCO V K → Finite (FinCl V K) ∧ ∀ x, gamOrd V K x ≠ 0 :=
  fun V K hV hK => ⟨finite_finCl V K (fun τ => hV (tauE _ τ)) hK, gamOrd_ne_zero V K (fun τ => hV (tauE _ τ)) hK⟩

end GlobalTheory.FunObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivs
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.TanVec

theorem exists_coords_derivs {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ (x : Fin D → A) (d : Fin D → A →+ A),
      (∀ c a b, d c (a * b) = a * d c b + b * d c a) ∧
      ∀ a c, d c (x a) = if a = c then 1 else 0 := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  let B := P.basisKaehler.reindex e
  have hB : ∀ i, KaehlerDifferential.D k A (P.val (e.symm i)) = B i := fun i => by
    simp [B]
  refine ⟨fun i => P.val (e.symm i), fun c =>
    { toFun := fun s => B.coord c (KaehlerDifferential.D k A s)
      map_zero' := by simp
      map_add' := fun s t => by simp }, fun c a b => ?_, fun a c => ?_⟩
  · change B.coord c (KaehlerDifferential.D k A (a * b)) =
      a * B.coord c (KaehlerDifferential.D k A b) + b * B.coord c (KaehlerDifferential.D k A a)
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · change B.coord c (KaehlerDifferential.D k A (P.val (e.symm a))) = _
    rw [hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

def jetHom {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (d : A →+ A)
    (hd : ∀ a b, d (a * b) = a * d b + b * d a) : A →+* DualNumber K where
  toFun s := (φ s, φ (d s))
  map_one' := by
    have h1 : d 1 = 0 := by
      have := hd 1 1
      simpa using this
    refine TrivSqZeroExt.ext (map_one φ) ?_
    change φ (d 1) = 0
    rw [h1, map_zero]
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero φ) ?_
    change φ (d 0) = 0
    rw [map_zero, map_zero]
  map_add' s t := by
    refine TrivSqZeroExt.ext (map_add φ s t) ?_
    change φ (d (s + t)) = φ (d s) + φ (d t)
    rw [map_add (f := _), map_add (f := _)]
  map_mul' s t := by
    refine TrivSqZeroExt.ext (map_mul φ s t) ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    change φ (d (s * t)) = φ s * φ (d t) + φ (d s) * φ t
    rw [hd, map_add (f := _), map_mul, map_mul, mul_comm (φ t)]

theorem exists_tangent_matrix : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] {K : Type} [Field K] (z : Sp K ⟶ Y), ∃ (O : Y.Opens) (_ : ⊤ ≤ z ⁻¹ᵁ O) (x : Fin D → Γ(Y, O)) (w : Fin D → (Sp (DualNumber K) ⟶ Y)), (∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z) ∧ ∀ hwO : (∀ b, ⊤ ≤ w b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (x a)).snd).det ≠ 0 := by
  intro k _ Y p D _ K _ z
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top (GlobalTheory.Adelic.ptOf z))
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), GlobalTheory.Adelic.ptOf z ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨x, d, hl, hd⟩ := exists_coords_derivs h₂
  have hO : IsAffineOpen (Y.basicOpen (t : Γ(Y, V))) := IsAffineOpen.basicOpen hV _
  have hzO : ⊤ ≤ z ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := (GlobalTheory.Adelic.le_iff_ptOf_mem z _).2 hxt
  choose w hw he using fun c => exists_evalPt_eq hO (jetHom (evalPt z _ hzO) (d c) (hl c))
  refine ⟨_, hzO, x, w, fun b => ?_, fun hwO => ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw b (Set.mem_univ _)
    refine ext_evalPt hO h' hzO (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ (w b) _ (hw b) h' f).trans ?_
    rw [he]
    rfl
  · have hm : (Matrix.of fun a b => (evalPt (w b) _ (hwO b) (x a)).snd) = (1 : Matrix (Fin D) (Fin D) K) := by
      ext a b
      have e1 : (evalPt (w b) _ (hwO b) (x a)).snd = evalPt z _ hzO (d b (x a)) := by
        rw [he]
        rfl
      rw [Matrix.of_apply, e1, hd, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm, Matrix.det_one]
    exact one_ne_zero

end GlobalTheory.TanVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVectors_functions_invertible_derivs : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] {K : Type} [Field K] (z : Sp K ⟶ Y), ∃ (O : Y.Opens) (_ : ⊤ ≤ z ⁻¹ᵁ O) (x : Fin D → Γ(Y, O)) (w : Fin D → (Sp (DualNumber K) ⟶ Y)), (∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z) ∧ ∀ hwO : (∀ b, ⊤ ≤ w b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (x a)).snd).det ≠ 0 := by
  first | exact @GlobalTheory.TanVec.exists_tangent_matrix | exact GlobalTheory.TanVec.exists_tangent_matrix | (intros; apply GlobalTheory.TanVec.exists_tangent_matrix <;> assumption)
end
end
