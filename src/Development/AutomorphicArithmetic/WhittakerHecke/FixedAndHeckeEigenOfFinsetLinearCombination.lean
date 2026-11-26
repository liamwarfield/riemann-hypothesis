module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
public import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.FixedAndHeckeEigenOfFinsetLinearCombination
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem finsum_Tj_eq {E : Type} [Field E] [NumberField E] {w : H.P E} {ϖ : w.adicCompletion E}
    (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ t : Finset (GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2)),
      ∀ F : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ,
        ∑ᶠ x, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x =
          ∑ x ∈ t, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun x hx => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hx

theorem UpperTheory.fixed_and_heckeEigen_of_finset_linearCombination :
    ∀ (E : Type) [Field E] [NumberField E] (w : H.P E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ) (B : Multiset ℂˣ), s.Nonempty → (∀ i, H.Fix w (φ i)) → (∀ i, EigAt w B (φ i)) → H.Fix w (fun g => ∑ i ∈ s, c i * φ i g) ∧ EigAt w B (fun g => ∑ i ∈ s, c i * φ i g) := by
  intro E _ _ w ι s c φ B hs hF hE
  obtain ⟨i₀, -⟩ := hs
  refine ⟨fun g k hk => ?_, fun g => ⟨(hE i₀ g).card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩⟩
  · simp only [fun i => hF i g k hk]
  · simp only [fun i => (hE i g).inv y k hk]
  · obtain ⟨t, ht⟩ := finsum_Tj_eq (w := w) hϖ j
    rw [ht]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := (hE i g).eig ϖ hϖ j hj y
    rw [ht] at e
    rw [mul_left_comm, ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.UnipotentNatDivMemMaximalCompactOfNotBadPrime
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ Formalism.UG.Ov K v := one_mem _
  have h0 : (0 : H.Kv v) ∈ Formalism.UG.Ov K v := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma map_gl_nU {K : Type} [Field K] [NumberField K] (v : H.P K) (z : A K) :
    Matrix.GeneralLinearGroup.map (H.cp v) (gl (nU z)) = H.nL (H.cp v z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact map_one (H.cp v)
  · rfl
  · exact map_zero (H.cp v)
  · exact map_one (H.cp v)

private lemma val_nat_one {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (hL : (L : 𝓞 E) ∉ w.asIdeal) : Valued.v (L : H.Kv w) = 1 := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) w (L : 𝓞 E)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hL] at h1
  simpa using h1

private lemma val_nat_le {E : Type} [Field E] [NumberField E] (w : H.P E) (a : ℕ) :
    Valued.v (a : H.Kv w) ≤ 1 :=
  show (a : H.Kv w) ∈ w.adicCompletionIntegers E from natCast_mem _ a

private lemma not_mem_of_bad {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (h : ¬ Bad L (w.under (𝓞 ℚ))) : (L : 𝓞 E) ∉ w.asIdeal := by
  intro hm
  apply h
  show (L : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal
  change (L : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 E))
  rw [Ideal.mem_comap, map_natCast]
  exact hm

private lemma cp_iota (v : H.P ℚ) (L : ℕ) : H.cp v (iota L) = (L : H.Kv v)⁻¹ := by
  have h := eq_ratCast ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹
  have e : H.cp v (iota L) = ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹ := rfl
  rw [e, h]
  push_cast
  rfl

private lemma completion_adele_natural {E : Type} [Field E] [NumberField E] (w : H.P E) (L a : ℕ) :
    H.cp w (AdeleBaseChange.adeleMap ℚ E ((a : A ℚ) * iota L)) = (a : H.Kv w) * (L : H.Kv w)⁻¹ := by
  have h : ((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w) =
      (a : H.Kv (AdeleBaseChange.below ℚ w)) * (L : H.Kv (AdeleBaseChange.below ℚ w))⁻¹ := by
    have := map_mul (H.cp (AdeleBaseChange.below ℚ w)) (a : A ℚ) (iota L)
    rw [cp_iota, map_natCast] at this
    exact this
  show SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w)) = _
  rw [h, map_mul, map_inv₀, map_natCast, map_natCast]

theorem UpperTheory.unipotent_natDiv_mem_maximalCompact_of_not_badPrime :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ) (w : H.P E), ¬ Bad L (w.under (𝓞 ℚ)) → Valued.v (H.cp w (rt D.θ)) ≤ 1 → H.KAt w (nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a w hL hθ
  have hL1 := val_nat_one w L (not_mem_of_bad w L hL)
  have hz : Valued.v (H.cp w (D.mkE 0 ((a : A ℚ) * iota L))) ≤ 1 := by
    rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, completion_adele_natural, map_mul, map_inv₀, hL1, inv_one, mul_one]
    calc _ ≤ (1 : _) * 1 := mul_le_mul' (val_nat_le w a) hθ
      _ = 1 := mul_one 1
  show Matrix.GeneralLinearGroup.map (H.cp w) (gl (nU (D.mkE 0 ((a : A ℚ) * iota L)))) ∈ GlobalTheory.LFun.KGL w (n := 2)
  rw [map_gl_nU]
  exact nL_memK hz
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.BaseChangeGL2CongruenceOfLevel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open scoped ValuativeRel

private theorem mem_int_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

private theorem inv_entry_int (v : H.P ℚ) (g : GL (Fin 2) (A ℚ)) (h : H.KAt v g) (i j : Fin 2) :
    Valued.v (((g⁻¹).val i j).2 v) ≤ 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (H.cp v) g ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion ℚ) 2 := by
    rw [← PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.KGL_eq]
    exact h
  have h2 := ((GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ _).1 h1).2 i j
  rw [← map_inv] at h2
  exact (mem_int_iff v _).1 h2

private theorem div_of_dv (N : ℕ) (hN : 0 < N) (x : A ℚ) (h1 : x.1 = 0) (h2 : ∀ v, Dv N v x) :
    ∃ c ∈ Oh ℚ, x = (N : A ℚ) * c := by
  have hcp : ∀ v : H.P ℚ, ((N : A ℚ)).2 v = (N : H.Kv v) := fun v => map_natCast (H.cp v) N
  have hio : ∀ v : H.P ℚ, (iota N).2 v = (N : H.Kv v)⁻¹ := by
    intro v
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h0 : (iota N).2 * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
      change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1
      rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)), ← map_mul, inv_mul_cancel₀ hN', map_one]
    have h3 := congrArg (pLoc ℚ v) h0
    rw [map_mul, map_natCast, map_one] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hne : ∀ v : H.P ℚ, (N : H.Kv v) ≠ 0 := by
    intro v
    have : CharZero (H.Kv v) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 hN.ne'
  refine ⟨x * iota N, ⟨?_, fun v => ?_⟩, ?_⟩
  · change x.1 * (iota N).1 = 0
    rw [h1, zero_mul]
  · change Valued.v (x.2 v * (iota N).2 v) ≤ 1
    rw [hio, map_mul, map_inv₀]
    have hv : Valued.v (N : H.Kv v) ≠ 0 := (Valuation.ne_zero_iff _).2 (hne v)
    exact mul_inv_le_one_of_le₀ (h2 v) zero_le'
  · refine Prod.ext ?_ (FiniteAdeleRing.ext (K := ℚ) fun v => ?_)
    · change x.1 = (N : A ℚ).1 * (x.1 * (iota N).1)
      rw [h1, zero_mul, mul_zero]
    · change x.2 v = (N : A ℚ).2 v * (x.2 v * (iota N).2 v)
      rw [hcp, hio]
      field_simp [hne v]

private theorem oh_add {K : Type} [Field K] [NumberField K] {a b : A K} (ha : a ∈ Oh K) (hb : b ∈ Oh K) :
    a + b ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 + b.1 = 0
    rw [ha.1, hb.1, add_zero]
  · change Valued.v (a.2 v + b.2 v) ≤ 1
    exact (Valuation.map_add _ _ _).trans (max_le (ha.2 v) (hb.2 v))

private theorem oh_neg {K : Type} [Field K] [NumberField K] {a : A K} (ha : a ∈ Oh K) : -a ∈ Oh K := by
  refine ⟨?_, fun v => ?_⟩
  · change -a.1 = 0
    rw [ha.1, neg_zero]
  · change Valued.v (-(a.2 v)) ≤ 1
    rw [Valuation.map_neg]
    exact ha.2 v

private theorem oh_mul (a c : A ℚ) (ha : ∀ v : H.P ℚ, Valued.v (a.2 v) ≤ 1) (hc : c ∈ Oh ℚ) : a * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change a.1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v (a.2 v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (ha v) (hc.2 v)

private theorem oh_map (E : Type) [Field E] [NumberField E] {c : A ℚ} (hc : c ∈ Oh ℚ) :
    AdeleBaseChange.adeleMap ℚ E c ∈ Oh E := by
  refine ⟨?_, fun w => ?_⟩
  · have : (AdeleBaseChange.adeleMap ℚ E c).1 =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) c.1 := rfl
    rw [this, hc.1]
    exact map_zero _
  · rw [GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply, GroundTheory.Global.SemiLocal.valued_completionMap]
    exact pow_le_one' (hc.2 _) _

private theorem entry_map (E : Type) [Field E] [NumberField E] (N : ℕ) (g : GL (Fin 2) (A ℚ)) (i j : Fin 2)
    (h : ∃ c ∈ Oh ℚ, g.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c) :
    ∃ c ∈ Oh E, (em E g).val i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (N : A E) * c := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨AdeleBaseChange.adeleMap ℚ E c, oh_map E hc, ?_⟩
  have h1 : (em E g).val i j = AdeleBaseChange.adeleMap ℚ E (g.val i j) := rfl
  have h2 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j =
      AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h1, h2, ← map_sub, h, map_mul, map_natCast]

theorem UpperTheory.baseChangeGL2_congruence_of_level :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ k : GL (Fin 2) (A ℚ), Lev N k → CongE N (em E k) := by
  intro E _ _ N hN k hk
  have hk1 : ∀ i j, ∃ c ∈ Oh ℚ, k.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * c := by
    intro i j
    refine div_of_dv N hN _ ?_ fun v => (hk.2 v).2 i j
    change (k.val i j).1 - ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 = 0
    rw [hk.1 i j, sub_self]
  choose c hc hkc using hk1
  have hk2 : ∀ i j, ∃ d ∈ Oh ℚ, (k⁻¹).val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j = (N : A ℚ) * d := by
    intro i j
    have hint : ∀ l, (k⁻¹).val i l * c l j ∈ Oh ℚ := fun l =>
      oh_mul _ _ (fun v => inv_entry_int v k (hk.2 v).1 i l) (hc l j)
    refine ⟨-((k⁻¹).val i 0 * c 0 j + (k⁻¹).val i 1 * c 1 j), oh_neg (oh_add (hint 0) (hint 1)), ?_⟩
    have hm : (k⁻¹).val * k.val = 1 := by
      have := congrArg Units.val (inv_mul_cancel k)
      simpa using this
    have hs : ((k⁻¹).val * (k.val - 1)) i j = (1 - (k⁻¹).val) i j := by
      rw [Matrix.mul_sub, hm, Matrix.mul_one]
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
      hkc 0 j, hkc 1 j] at hs
    linear_combination hs
  intro i j
  refine ⟨entry_map E N k i j ⟨c i j, hc i j, hkc i j⟩, ?_⟩
  rw [← map_inv]
  exact entry_map E N k⁻¹ i j (hk2 i j)
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.SumRangeRatAdeleCharIotaMulOneSubEqIte
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem psi_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem psi_eq_one_iff (x : A ℚ) : ψ x = 1 ↔ adelicChar ℚ x = 1 := Circle.coe_eq_one

private theorem psi_neg_of_one {x : A ℚ} (h : ψ x = 1) : ψ (-x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_neg_eq_inv, h, inv_one]

private theorem psi_zsmul (m : ℤ) {x : A ℚ} (h : ψ x = 1) : ψ (m • x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_zsmul_eq_zpow, h, _root_.one_zpow]

private theorem psi_nsmul (a : ℕ) (x : A ℚ) : ψ (a • x) = ψ x ^ a := by
  simp only [ψ, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

private theorem psi_Oh {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ c = 1 := by
  have h : c ∈ invDifferentAdeles ℚ :=
    mem_invDifferentAdeles.2 (mem_finiteInvDifferent.2 fun v =>
      mem_localInvDifferent_of_mem (hc.2 v))
  rw [psi_eq_one_iff, adelicChar_of_mem_invDifferentAdeles h, hc.1]
  simp

private theorem different_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ), NumberField.discr_rat]
  rfl

private theorem mem_inv_iff (v : H.P ℚ) (x : H.Kv v) : x ∈ localInvDifferent v ↔ Valued.v x ≤ 1 := by
  rw [mem_localInvDifferent_iff_valued, different_rat]
  simp [FractionalIdeal.count_one]

private theorem psi_sg_eq (v : H.P ℚ) (x : H.Kv v) : ψ (H.sg v x) = (localAdelicChar ℚ v x : ℂ) := rfl

private noncomputable def eA : A ℚ := (0, 1)

private theorem fin_alg_val {K : Type} [Field K] [NumberField K] (v : H.P K) (a : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) a) v) = v.valuation K a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem nat_val (v : H.P ℚ) (n : ℕ) : Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := by
  have e : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v = (n : H.Kv v) := map_natCast (pLoc ℚ v) n
  rw [e]
  exact natCast_mem (v.adicCompletionIntegers ℚ) n

private theorem decomp (n : ℕ) (hn : 0 < n) {c : A ℚ} (hc : c ∈ Oh ℚ) :
    ∃ (m : ℤ) (c' : A ℚ), c' ∈ Oh ℚ ∧ c = m • eA + (n : A ℚ) * c' := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨k, hk⟩ := exists_sub_mem_finiteInvDifferent (K := ℚ)
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2)
  obtain ⟨f, hf⟩ : ∃ f, f = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2 -
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := ⟨_, rfl⟩
  rw [← hf] at hk
  have hfv : ∀ v : H.P ℚ, Valued.v (f v) ≤ 1 := fun v =>
    (mem_inv_iff v _).1 (mem_finiteInvDifferent.1 hk v)
  have hnn : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) n, ← map_mul, mul_inv_cancel₀ hn0, map_one]
  have key : c.2 = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k) := by
    rw [hf, map_mul, map_natCast, mul_sub, ← mul_assoc, hnn, one_mul, sub_add_cancel]
  have hint : ∀ v : H.P ℚ, v.valuation ℚ ((n : ℚ) * k) ≤ 1 := by
    intro v
    have e : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v = c.2 v - (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v := by
      have h2 : c.2 v = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v + (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v :=
        congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) key
      rw [h2]
      ring
    rw [← fin_alg_val, e]
    refine (Valuation.map_sub _ _ _).trans (max_le (hc.2 v) ?_)
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hfv v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ _ hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (r.2 : IsIntegral ℤ (r : ℚ))
  have hmk : (n : ℚ) * k = (m : ℚ) := by
    exact hr.symm.trans (hm.symm.trans (eq_intCast (algebraMap ℤ ℚ) m))
  refine ⟨m, ((0, f) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ), ⟨rfl, hfv⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · change c.1 = m • (0 : InfiniteAdeleRing ℚ) + (n : A ℚ).1 * 0
    rw [hc.1]
    simp
  · change c.2 = m • (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) + (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f
    rw [key, hmk, map_intCast, zsmul_one, add_comm]

private theorem local_good (v : H.P ℚ) (x : H.Kv v)
    (h : ∀ c : H.Kv v, Valued.v c ≤ 1 → ψ (H.sg v (c * x)) = 1) : Valued.v x ≤ 1 := by
  refine (mem_inv_iff v x).1 ((forall_localAdelicChar_mul_eq_one_iff v x).1 fun a ha => ?_)
  have := h a ha
  rw [psi_sg_eq] at this
  exact Circle.coe_eq_one.1 this

private theorem sg_oh (v : H.P ℚ) (c : H.Kv v) (hc : Valued.v c ≤ 1) : H.sg v c ∈ Oh ℚ := by
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  refine ⟨(hs c).1, fun w => ?_⟩
  by_cases h : w = v
  · subst h
    have : (H.sg w c).2 w = c := hcp c
    rw [this]
    exact hc
  · rw [(hs c).2 w h, map_zero]
    exact zero_le'

private theorem oh_nat_mul (n : ℕ) {c : A ℚ} (hc : c ∈ Oh ℚ) : (n : A ℚ) * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change (n : A ℚ).1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hc.2 v)

private theorem eA_mem : eA ∈ Oh ℚ := by
  refine ⟨rfl, fun v => ?_⟩
  change Valued.v (1 : H.Kv v) ≤ 1
  rw [map_one]

private theorem eA_mul {c : A ℚ} (hc : c.1 = 0) : eA * c = c := by
  refine Prod.ext ?_ ?_
  · change 0 * c.1 = c.1
    rw [hc, mul_zero]
  · change 1 * c.2 = c.2
    rw [one_mul]

private theorem L_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = eA := by
  have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · change (L : A ℚ).1 * 0 = 0
    rw [mul_zero]
  · change (L : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) L, ← map_mul, mul_inv_cancel₀ hL0, map_one]

private theorem psi_mul_of_one (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (y : A ℚ)
    (hy : ∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) (hz : ψ (iota L * (1 - y)) = 1)
    {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ (c * (iota L * (1 - y))) = 1 := by
  obtain ⟨m, c', hc', e⟩ := decomp (L * M) (Nat.mul_pos hL hM) hc
  have hw : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  have e2 : c * (iota L * (1 - y)) =
      m • (iota L * (1 - y)) + ((M : A ℚ) * c' + -(y * ((M : A ℚ) * c'))) := by
    have h1 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * c' - y * ((M : A ℚ) * c') := by
      have h2 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * (eA * c') * (1 - y) := by
        rw [← L_iota L hL]
        push_cast
        ring
      rw [h2, eA_mul hc'.1]
      ring
    rw [e, add_mul, h1, zsmul_eq_mul, mul_assoc, ← zsmul_eq_mul, eA_mul hw, sub_eq_add_neg ((M : A ℚ) * c')]
  rw [e2, psi_add, psi_add, psi_zsmul m hz, psi_Oh (oh_nat_mul M hc'), psi_neg_of_one (hy c' hc')]
  simp

private theorem val_iff (L : ℕ) (hL : 0 < L) (y : A ℚ) (v : H.P ℚ) :
    Dv L v (y - 1) ↔ Valued.v (H.cp v (iota L * (1 - y))) ≤ 1 := by
  have hab : Valued.v (L : H.Kv v) * Valued.v (H.cp v (iota L)) = 1 := by
    have e : (L : H.Kv v) * H.cp v (iota L) = 1 := by
      have h1 : H.cp v ((L : A ℚ) * iota L) = 1 := by
        rw [L_iota L hL]
        rfl
      rwa [map_mul, map_natCast] at h1
    rw [← map_mul, e, map_one]
  have hx : Valued.v (H.cp v (iota L * (1 - y))) =
      Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1)) := by
    rw [map_mul, map_mul, ← neg_sub y 1, map_neg, Valuation.map_neg]
  rw [hx]
  unfold Dv
  constructor
  · intro h
    calc _ ≤ Valued.v (H.cp v (iota L)) * Valued.v (L : H.Kv v) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hab]
  · intro h
    calc Valued.v (H.cp v (y - 1)) =
        Valued.v (L : H.Kv v) * (Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1))) := by
          rw [← mul_assoc, hab, one_mul]
      _ ≤ Valued.v (L : H.Kv v) * 1 := mul_le_mul' le_rfl h
      _ = _ := mul_one _

theorem UpperTheory.sum_range_ratAdeleChar_iota_mul_one_sub_eq_ite :
    ∀ (L M : ℕ), 0 < L → 0 < M → ∀ y : A ℚ, (∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) → ∑ a ∈ Finset.range (L * M), ψ ((a : A ℚ) * iota L * (1 - y)) = if ∀ v : H.P ℚ, Dv L v (y - 1) then ((L * M : ℕ) : ℂ) else 0 := by
  intro L M hL hM y hy
  have hsum : ∀ a : ℕ, ψ ((a : A ℚ) * iota L * (1 - y)) = ψ (iota L * (1 - y)) ^ a := by
    intro a
    rw [mul_assoc, ← nsmul_eq_mul, psi_nsmul]
  simp only [hsum]
  have hzn : ψ (iota L * (1 - y)) ^ (L * M) = 1 := by
    rw [← psi_nsmul, nsmul_eq_mul]
    have e : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
        (M : A ℚ) * eA + -(y * ((M : A ℚ) * eA)) := by
      have h1 : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
          (M : A ℚ) * ((L : A ℚ) * iota L) * (1 - y) := by
        push_cast
        ring
      rw [h1, L_iota L hL]
      ring
    rw [e, psi_add, psi_Oh (oh_nat_mul M eA_mem), psi_neg_of_one (hy eA eA_mem), one_mul]
  have hw1 : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  split_ifs with h
  · have hz : ψ (iota L * (1 - y)) = 1 :=
      psi_Oh ⟨hw1, fun v => (val_iff L hL y v).1 (h v)⟩
    simp [hz]
  · have hz : ψ (iota L * (1 - y)) ≠ 1 := by
      intro hz
      refine h fun v => (val_iff L hL y v).2 (local_good v _ fun c hc => ?_)
      obtain ⟨-, hm, -⟩ := H.sgLaws ℚ v
      rw [mul_comm c, ← hm, mul_comm]
      exact psi_mul_of_one L M hL hM y hy hz (sg_oh v c hc)
    rw [geom_sum_eq hz, hzn]
    simp
end
