module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimesOfChartForm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepth2Run
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunDepthDataLawsAndFiniteLocalDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunDepthDataLawsAndFiniteLocalDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem laws_and_nuFinAt : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)], LawsM T → (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → LawsPi T (depOf T EX Tp hK) ∧ LawsDep T ∧ NuFinAt T (depOf T EX Tp hK) := by
  intro D L Pm Tp hK T EX _ h hs
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn : 2 * D.R.f * D.R.r ≤ Tp.nWn := by
    refine le_trans ?_ Tp.nW_lo.1
    calc 2 * D.R.f * D.R.r = D.R.f * D.R.r * 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hP : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun h EX _ _ _ _ _ fun j _ => hn
  have hD : LawsDep T :=
    ⟨hs, fun j _ => (GlobalTheory.IntChartExists.intChart_exists _ _ _ _ (T.Q.Xo j) T.Q.c).2.1 hs,
      fun j _ => GlobalTheory.ChartCmp.chartIndep_holds _ _ _ _ (T.Q.Xo j) T.Q.c hs⟩
  exact ⟨hP, hD, nuFinAt_of T h.pins _ hP.wts hD.chartEx
    fun j _ => Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds (T.Q.Xo j) T.Q.c⟩

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunDepthDataLawsAndFiniteLocalDepthStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runDepthData_laws_and_finite_local_depth : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)], LawsM T → (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → LawsPi T (depOf T EX Tp hK) ∧ LawsDep T ∧ NuFinAt T (depOf T EX Tp hK) := by
  first | exact @GlobalTheory.RunDepth.laws_and_nuFinAt | exact GlobalTheory.RunDepth.laws_and_nuFinAt | (intros; apply GlobalTheory.RunDepth.laws_and_nuFinAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthLevelRun
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthParamsPlusMinusCountsEqKappa
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthParamsPlusMinusCountsEqKappa
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem numOf_Dplus_Dminus : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → (numOf D L).Dplus j = ((∑ τ, ∑ i, (kaR Tp hK j).aP τ i : ℕ) : ℚ) ∧ (numOf D L).Dminus j = ((∑ τ, ∑ i, (kaR Tp hK j).aM τ i : ℕ) : ℚ) := by
  intro D L Pm Tp hK j hj
  have hb := (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).1
  have h1 := hj.1
  have h2 := hj.2
  constructor
  · have e : (numOf D L).Dplus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (hK j h1 h2 τ).1 i, ← kaWt_big D hK (even_nV Tp) j h1 h2 τ i, Int.cast_natCast]
    rfl
  · have e : (numOf D L).Dminus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := kaWt_small D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).2 (Fin.rev i)
    have e3 := congrArg (fun q : ℤ => (q : ℚ)) e1
    simp only [Int.cast_natCast, Int.cast_neg] at e3
    rw [e2, neg_neg] at e3
    exact e3.symm

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthParamsPlusMinusCountsEqKappaStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthParams_plusMinusCounts_eq_kappa : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → (numOf D L).Dplus j = ((∑ τ, ∑ i, (kaR Tp hK j).aP τ i : ℕ) : ℚ) ∧ (numOf D L).Dminus j = ((∑ τ, ∑ i, (kaR Tp hK j).aM τ i : ℕ) : ℚ) := by
  first | exact @GlobalTheory.RunDepth.numOf_Dplus_Dminus | exact GlobalTheory.RunDepth.numOf_Dplus_Dminus | (intros; apply GlobalTheory.RunDepth.numOf_Dplus_Dminus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RamificationIndexGeOfResCharDvdLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RamificationIndexGeOfResCharDvdLevel
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem resChar_sub_one_le_ramOverZ_of_primitiveRoot {L : Type} [Field L] [NumberField L]
    (la : HeightOneSpectrum (𝓞 L)) (ζ : L) (hζ : IsPrimitiveRoot ζ (resCharOf la)) :
    resCharOf la - 1 ≤ ramOverZ la := by
  have hp := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hpP := Formalism.L2.Pj.Crude.crv_char_mem la
  unfold ramOverZ
  generalize resCharOf la = p at hp hpP hζ ⊢
  have hP := la.isPrime
  have : Fact p.Prime := ⟨hp⟩
  set Z : 𝓞 L := ⟨ζ, hζ.isIntegral hp.pos⟩ with hZdef
  have hZ : IsPrimitiveRoot Z p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hassoc : Associated ((Z - 1) ^ (p - 1)) (p : 𝓞 L) := by
    have h2 : (Polynomial.cyclotomic p (𝓞 L)).eval 1 = p := Polynomial.eval_one_cyclotomic_prime
    rw [← h2, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hZ, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← Nat.totient_prime hp, ← hZ.card_primitiveRoots, ← Finset.prod_const]
    refine Associated.prod _ _ _ fun η hη => ?_
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨i, -, hi, rfl⟩ := hZ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
    simpa using (hZ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right
  have hZP : Z - 1 ∈ la.asIdeal := by
    obtain ⟨u, hu⟩ := hassoc.symm
    exact hP.mem_of_pow_mem _ (hu ▸ la.asIdeal.mul_mem_right _ hpP)
  have hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.span {(p : 𝓞 L)} ≤ la.asIdeal ^ (p - 1) := by
    rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow]
    exact pow_le_pow_left' ((Ideal.span_singleton_le_iff_mem la.asIdeal).mpr hZP) _
  have hne : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hne hP]
  apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
  · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne
  · rw [Ideal.dvd_iff_le, hmap]
    exact hle

theorem resChar_sub_one_le_ramOverZ_of_dvd_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l)
      (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∣ l.M → resCharOf la - 1 ≤ ramOverZ la := by
  intro E _ _ _ H l c la hd
  have hp := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hmem := Formalism.L2.Pj.zeta_mem_of_dvd c (hd.trans (Nat.dvd_lcm_left l.M l.A)) h0
  refine resChar_sub_one_le_ramOverZ_of_primitiveRoot la ⟨_, hmem⟩ ?_
  exact IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp _ hp.ne_zero) Subtype.val_injective

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RamificationIndexGeOfResCharDvdLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationIndex_ge_of_resChar_dvd_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∣ l.M → resCharOf la - 1 ≤ ramOverZ la := by
  first | exact @GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level | exact GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level | (intros; apply GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthLevel_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthLevel N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hL := (GlobalTheory.T.runDepthData_laws_and_finite_local_depth D L Pm Tp hK T EX hM hR.star_eq).1
  refine DepthTie.leafDepthLevel_core T (depOf T EX Tp hK) O ι N (numOf D L) hL hR.E_eq hR.σ_eq hR.nn_eq hR.T_eq
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.conj (fun j => GlobalTheory.T.depthParams_plusMinusCounts_eq_kappa D L Pm Tp hK (ι j) (hR.inR j)) hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) ?_ ?_ ?_
  · intro j
    have h1 : DF (T.Q.Dw (ι j)) ((depOf T EX Tp hK).aL (ι j)) = WeightAlgebra.DF (lR Tp hK (ι j)) :=
      (GlobalTheory.T.weightExponents_embeddings_degree D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    simp only [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h := (GlobalTheory.T.degree_weightKappa_le_pageBound D L Pm Tp hK hx hb (ι j) (hR.inR j)).2
    rw [hR.jets_eq_fact, hR.g2_eq]
    exact ⟨h 0, h 1⟩
  · intro w _ hw
    have key : ∀ v : HeightOneSpectrum (𝓞 K), plc v = plc w → (plc w : ℝ) - 1 ≤ DepthTie.e2 T.Q.c v := by
      intro v hv
      have hc : resCharOf (placeBelow (K := T.Q.c.F) v) = plc w := (DepthTie.resChar_below v).trans hv
      have hd : resCharOf (placeBelow (K := T.Q.c.F) v) ∣ T.Q.l.M := by
        rw [hc, level_M T hM]
        rcases hw with h | h
        · rw [h, hR.jets_eq_fact]; exact Dvd.intro _ rfl
        · rw [h, hR.g2_eq]; exact Dvd.intro_left _ rfl
      have h := GlobalTheory.T.ramificationIndex_ge_of_resChar_dvd_level _ _ T.Q.l T.Q.c _ hd
      rw [hc] at h
      have h' : plc w ≤ DepthTie.e2 T.Q.c v + 1 := by unfold DepthTie.e2; omega
      have h'' : (plc w : ℝ) ≤ (DepthTie.e2 T.Q.c v : ℝ) + 1 := by exact_mod_cast h'
      linarith
    exact ⟨key w rfl, key _ (plc_conjPl w)⟩

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KLeSubOneOfLt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem k_le_sub_one_of_lt (R : Ranks) (l : ℕ) (h : 4 * R.t * R.r + 1 < l) : (R.k : ℝ) ≤ (l : ℝ) - 1 := by
  have h1 : R.k ≤ R.r := by have := R.two_le_m; unfold Ranks.r; omega
  have h2 : 1 ≤ R.t := by have := R.three_m_lt_t; omega
  have h3 : R.r ≤ 4 * R.t * R.r := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : R.k + 1 ≤ l := by omega
  have h5 : ((R.k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast h4
  push_cast at h5
  linarith

theorem leafDepthRam_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthRam N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg hSz hx hb tF
  obtain ⟨hPi, hDep, -⟩ := laws_and_nuFinAt D L Pm Tp hK T EX hM hR.star_eq
  obtain ⟨-, hW⟩ := sizes_le_two_mul D L Pm hx hb
  refine DepthTie.leafDepthRam_core_sat T (depOf T EX Tp hK) O ι N (numOf D L) hPi hM.pins hR.inR hR.E_eq hR.σ_eq
    hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.star_eq (fun j => hDep.chartEx _ (hR.inR j)) hPg hSz tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ⟨?_, hR.k_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) 1 ?_ ?_ ?_ ?_
  · rw [hR.f_eq]
    show ((2 * D.R.n : ℕ) : ℝ) = 2 * ((D.R.n : ℕ) : ℝ)
    push_cast
    ring
  · intro j
    have h1 := (GlobalTheory.WeightExponents.weight_exponents D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (mul_rows_lR_le_kaR D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    show O.T * ((DF (T.Q.Dw (ι j)) (wtA (lR Tp hK (ι j))) : ℕ) : ℝ) ≤ (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)
    rw [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h1 := (DF_kaR_le D L Pm Tp hK hx hb (ι j) (hR.inR j)).1
    unfold OnObj.sB OnObj.Se
    rw [one_mul, hR.k_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
    exact h1
  · unfold PageRam
    rw [one_mul, hR.k_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq]
    exact ⟨k_le_sub_one_of_lt D.R _ D.host.qd_big.1, k_le_sub_one_of_lt D.R _ D.host.qd_big.2⟩
  · intro j t
    obtain ⟨h1, h2, h3⟩ := hW (ι j) (hR.inR j)
    rw [h3, h3, hR.bp_eq]
    exact ⟨(h1 _).1, (h1 _).1, (min_le_left _ _).trans (h2 t)⟩

end GlobalTheory.RunDepth
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth_all_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → (∀ (p : ℕ) [Fact p.Prime], UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → C0 ≤ oc.C → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → LeafDepthGood N O ∧ LeafDepthRam N O ∧ LeafDepth2 N O ∧ LeafDepthLevel N O := by
  intro hAv hHT hUp
  obtain ⟨C0, hG⟩ := GlobalTheory.T.depthTable_goodPrimes_of_chartForm hUp
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg hSz hx hb tF hC hn he
  exact ⟨hG D L Pm Tp hK T hM EX K Bs Df S P oc O ι N hR hC hPg hSz hn he hx hb tF,
    GlobalTheory.RunDepth.leafDepthRam_run D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF,
    GlobalTheory.RunDepth.leafDepth2_run hAv hHT D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF,
    GlobalTheory.RunDepth.leafDepthLevel_run D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF⟩
