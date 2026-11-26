module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletion
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.InertConj

theorem conj_mem_of_inert {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    (h : IsInertAt (maximalRealSubfield E) E v P) {x : 𝓞 E} (hx : x ∈ P.asIdeal) :
    IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal := by
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have key : P.asIdeal ≤ Ideal.comap
      (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) P.asIdeal := by
    conv_lhs => rw [← h']
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change IsCMField.ringOfIntegersComplexConj E _ ∈ _
    rw [AlgEquiv.commutes, ← h']
    exact Ideal.mem_map_of_mem _ hs
  exact key hx

theorem exists_conj_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E), (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) ∧ (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) ∧ σ ϖ = ϖ ∧ IsUnifV E P ϖ := by
  intro E _ _ _ _ v P h
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv P P := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv P _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
      algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ P.asIdeal ^ 2 := by
    by_contra hn
    push Not at hn
    have h1 : P.asIdeal ≤ P.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ P.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (a : E)) =
      P.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  refine ⟨σ, algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E), σ2', ?_, σ3,
    ?_, ?_, ?_⟩
  · intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous P (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2', ReciprocityTheory.ChartRestriction.G.FD.cc]
  · obtain ⟨x, hx⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact P.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 hx)
  · change σ _ = _
    rw [σ2', cc_algebraMap]
  · unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq P hs1 hs2

end GlobalTheory.InertConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletionStatement
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexConj_isometry_inert_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E), (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) ∧ (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) ∧ σ ϖ = ϖ ∧ IsUnifV E P ϖ := by
  first | exact @GlobalTheory.InertConj.exists_conj_completion | exact GlobalTheory.InertConj.exists_conj_completion | (intros; apply GlobalTheory.InertConj.exists_conj_completion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorLatSpan
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.StdBaseChange

def pureSet (K : Type) [CommRing K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) : Set (MvPolynomial (S × (Fin k × Fin n)) K) :=
  {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ A s) ∧ P = ∏ s, blockEmb K s (F s)}

theorem tensorLat_span (R K : Type) [CommRing R] [CommRing K] [Algebra R K] {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    tensorLat R K (fun s => Submodule.span R (A s)) = Submodule.span R (pureSet K A) := by
  classical
  apply le_antisymm
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 : ∀ s, blockEmb K s (F s) ∈ Submodule.span R (blockEmb K s '' A s) := fun s =>
      Submodule.apply_mem_span_image_of_mem_span ((blockEmb K s).toLinearMap.restrictScalars R) (hF s)
    have h2 : ∀ t : Finset S, ∏ s ∈ t, blockEmb K s (F s) ∈ ∏ s ∈ t, Submodule.span R (blockEmb K s '' A s) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.prod_empty]
        exact Submodule.one_le.mp le_rfl
      | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact Submodule.mul_mem_mul (h1 a) ih
    have h3 := h2 Finset.univ
    rw [Submodule.prod_span] at h3
    refine Submodule.span_mono ?_ h3
    intro P hP
    obtain ⟨G, hG, rfl⟩ := (Set.mem_fintype_prod _ _).mp hP
    choose F' hF' hFG using hG
    exact ⟨F', hF', by simp only [hFG]⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => Submodule.subset_span (hF s), rfl⟩

theorem image_pureSet {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {S : Type} [Fintype S] {k n : ℕ}
    (A : S → Set (MvPolynomial (Fin k × Fin n) K)) :
    MvPolynomial.map φ '' pureSet K A = pureSet L fun s => MvPolynomial.map φ '' A s := by
  have h : ∀ F : S → MvPolynomial (Fin k × Fin n) K,
      MvPolynomial.map φ (∏ s, blockEmb K s (F s)) = ∏ s, blockEmb L s (MvPolynomial.map φ (F s)) := by
    intro F
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [blockEmb, map_rename]
  ext P
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨_, fun s => ⟨F s, hF s, rfl⟩, h F⟩
  · rintro ⟨G, hG, rfl⟩
    choose F hF hFG using hG
    exact ⟨_, ⟨F, hF, rfl⟩, by rw [h]; simp only [hFG]⟩

theorem span_map_span {R K O L σ : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing O] [CommRing L] [Algebra O L]
    (φ : K →+* L) (ψ : R →+* O) (h : ∀ r, algebraMap O L (ψ r) = φ (algebraMap R K r)) (T : Set (MvPolynomial σ K)) :
    Submodule.span O (MvPolynomial.map φ '' (Submodule.span R T : Set (MvPolynomial σ K))) =
      Submodule.span O (MvPolynomial.map φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy =>
      have e : MvPolynomial.map φ (a • y) = ψ a • MvPolynomial.map φ y := by
        rw [← algebraMap_smul K a y, ← algebraMap_smul L (ψ a), smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, h]
      rw [e]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem dualWeyl_map (R K : Type) [CommRing R] [IsDomain R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (dualWeyl R n n ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.bidSet K n ν) := by
  rw [StdDual.dualWeyl_eq, Submodule.map_span, ← StdDual.image_bidSet (algebraMap R K)]
  rfl

theorem weyl_map (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) (ν : Fin n → ℕ) :
    (weyl R n n le_rfl ν).map (mapAlgHom (Algebra.ofId R K)).toLinearMap = Submodule.span R (StdDual.wordSet K n ν) := by
  rw [StdDual.weyl_eq, Submodule.map_span, ← StdDual.image_wordSet (algebraMap R K)]
  rfl

theorem std_baseChange : ∀ (O Kf K ι : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Field K] [NumberField K] [Fintype ι] (eK : K →+* Kf) (ψ : 𝓞 K →+* O), (∀ r, algebraMap O Kf (ψ r) = eK r) → ∀ (n : ℕ) (lam : ι → DomWeight n), Submodule.span O (MvPolynomial.map eK '' (nabStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdN O Kf n (lam τ).natW) ∧ Submodule.span O (MvPolynomial.map eK '' (delStd K lam : Set (Pol K ι n))) = (tensorLat O Kf fun τ => stdD O Kf n (lam τ).natW) := by
  intro O Kf K ι _ _ _ _ _ _ _ eK ψ h n lam
  constructor
  · have e : nabStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.bidSet K n (lam τ).natW) := by
      unfold nabStd
      congr 1
      funext τ
      exact dualWeyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdN, dualWeyl_map, StdDual.image_bidSet]
    rw [tensorLat_span]
  · have e : delStd K lam = tensorLat (𝓞 K) K fun τ => Submodule.span (𝓞 K) (StdDual.wordSet K n (lam τ).natW) := by
      unfold delStd
      congr 1
      funext τ
      exact weyl_map (𝓞 K) K n (lam τ).natW
    rw [e, tensorLat_span, span_map_span eK ψ h, image_pureSet]
    simp only [stdD, weyl_map, StdDual.image_wordSet]
    rw [tensorLat_span]

end GlobalTheory.StdBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShNums

theorem pow_six_le_exp {eps : ℝ} (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 4 ≤ x ∧ x ^ 6 ≤ Real.exp (x ^ (eps / 3)) := by
  have h := (isLittleO_log_rpow_atTop (r := eps / 3) (by positivity)).bound (c := 1 / 6) (by norm_num)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop (4 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  have hx' : 0 < x := by linarith
  refine ⟨h2, ?_⟩
  have hp : 0 < x ^ (eps / 3) := Real.rpow_pos_of_pos hx' _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at h1
  have h3 : Real.log x ≤ 1 / 6 * x ^ (eps / 3) := (le_abs_self _).trans h1
  calc x ^ 6 = Real.exp (Real.log (x ^ 6)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      rw [Real.log_pow]
      push_cast
      linarith

theorem size_rel_at {D : D7} (L : SizeData₂ D) (hs : SizesAt L) (h4 : 4 ≤ L.sc.x) (h6 : L.sc.x ^ 6 ≤ L.sc.X') :
    (D.R.k : ℝ) * D.R.N D.R.m ≤ L.Sc / 4 ∧ (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧ L.etaSz ≤ L.sc.w'' D.R.n ∧
    L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x ∧ 4 ≤ L.sc.x ∧ 2 * L.sc.b' ≤ L.sc.b ∧
    (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b ∧ 1 ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 + 3 * L.Sc ≤ L.sc.b := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, hEta, -, -, hDel, hW, -⟩ := hs
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hm : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by
      unfold Ranks.n
      exact D.R.ord_pos
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    refine le_trans (Real.one_le_rpow hx1 ?_) hK.1
    unfold szTh
    linarith
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := by
    refine hK.2.trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    unfold szTh
    push_cast
    linarith
  have hb1 : 1 ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (by positivity)
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : L.sc.b' * L.sc.X' = L.sc.x * L.sc.b := by
    unfold Scale.b' Scale.a
    field_simp
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a
    positivity
  have h5b : L.sc.x ^ 5 * L.sc.b' ≤ L.sc.b := by
    have : L.sc.x * (L.sc.x ^ 5 * L.sc.b') ≤ L.sc.x * L.sc.b := by
      rw [← hb']
      calc L.sc.x * (L.sc.x ^ 5 * L.sc.b') = L.sc.b' * L.sc.x ^ 6 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h6 hb'0.le
    exact le_of_mul_le_mul_left this hx0
  have hx5 : (4 : ℝ) ^ 5 ≤ L.sc.x ^ 5 := pow_le_pow_left₀ (by norm_num) h4 5
  have h5b' : 5 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    apply div_le_div_of_nonneg_left hb'0.le hx0
    nlinarith
  have hw' : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := le_trans (Real.one_le_sqrt.2 hb1) hW
  have heta0 := L.etaSz_pos
  have hS0 := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.w'' D.R.n := by
    refine le_trans ?_ hEta.2.2.2.2.1
    apply le_mul_of_one_le_left heta0.le
    nlinarith
  have hS : L.Sc ≤ L.sc.w'' D.R.n := le_trans (le_mul_of_one_le_left hS0.le hk1) hDel.2.2.2.1
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) :=
    le_trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hm)) hDel.1
  refine ⟨?_, hDel.2.2.2.1, hEta.2.2.2.2.1, heta, hw, h4, by linarith, ?_, hw1, by linarith⟩
  · rw [L.Sc_eq]
    have := mul_le_mul_of_nonneg_left hN (le_trans zero_le_one hk1)
    linarith
  · exact le_trans (mul_le_mul_of_nonneg_right hk5 hb'0.le) h5b

theorem size_rel : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m ≤ (Fm.L x i).Sc / 4 ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ ((Fm.D x i).R.m : ℝ) * (((Fm.D x i).R.t : ℝ) + 1) * (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.b' / (Fm.L x i).sc.x ∧ 4 ≤ (Fm.L x i).sc.x ∧ 2 * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc ≤ (Fm.L x i).sc.b := by
  intro eps Fm
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := pow_six_le_exp he
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨h4, h6⟩ := hx0 x hx
  apply size_rel_at (Fm.L x i) (Fm.sizes x hx1 i)
  · rw [Fm.L_x x i hx1]; exact h4
  · unfold Scale.X'
    rw [Fm.L_x x i hx1, Fm.L_eps x i]; exact h6

end GlobalTheory.ShNums
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventuallyStatement
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scale_family_size_relations_eventually : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m ≤ (Fm.L x i).Sc / 4 ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ ((Fm.D x i).R.m : ℝ) * (((Fm.D x i).R.t : ℝ) + 1) * (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.b' / (Fm.L x i).sc.x ∧ 4 ≤ (Fm.L x i).sc.x ∧ 2 * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc ≤ (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.ShNums.size_rel | exact GlobalTheory.ShNums.size_rel | (intros; apply GlobalTheory.ShNums.size_rel <;> assumption)
end
end
