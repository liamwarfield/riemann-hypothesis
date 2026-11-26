module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder Matrix.Norms.L2Operator

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dite_eq_left (map_mem_UL hU w γ)]

theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 := by
  let A : Matrix (Fin n) (Fin n) ℂ := (γ.1 : GL (Fin n) E).val.map τ
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom
      (γ.1 : GL (Fin n) E).val * (γ.1 : GL (Fin n) E).val = 1 := by
    have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom
        (γ.1 : GL (Fin n) E).val * 1 * (γ.1 : GL (Fin n) E).val = 1 := γ.2
    simpa only [Matrix.mul_one] using h
  have hstar : star A * A = 1 := by
    have hm := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map τ) hγ
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at hm
    convert hm using 1
    apply congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M * A)
    ext i j
    simp [A, cT, IsCMField.complexEmbedding_complexConj]
  have hu : A ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    apply IsUnit.mem_unitary_of_star_mul_self _ hstar
    exact ⟨GeneralLinearGroup.map τ γ.1, rfl⟩
  apply spectrum.norm_eq_one_of_unitary hu
  apply Matrix.mem_spectrum_of_isRoot_charpoly
  apply Polynomial.isRoot_of_mem_roots
  simpa [A, Matrix.charpoly_map] using hz

theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitary
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BddCpt

theorem bdd_entries_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  intro E _ _ _ n w t hK
  have hO : IsOpen ((Ov E w : Set (w.adicCompletion E))) := Valued.isOpen_valuationSubring _
  have hNe : (nhdsWithin (0 : w.adicCompletion E) {0}ᶜ).NeBot := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot 0
  have hev : ∀ᶠ a in nhds (0 : w.adicCompletion E),
      ∀ s ∈ closure (Subgroup.zpowers t : Set (UL n w)), ∀ i j, a * s.1.1 i j ∈ Ov E w := by
    refine hK.eventually_forall_of_forall_eventually fun s _ => ?_
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) := by fun_prop
    have h0 : (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) (0, s) ∈ (Ov E w : Set _) := by
      simp only [zero_mul]; exact (Ov E w).zero_mem
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
  obtain ⟨a, ha, ha0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set (w.adicCompletion E))))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (w.adicCompletion E))))).exists
  exact ⟨a, ha0, fun k i j => ha _ (subset_closure ⟨k, rfl⟩) i j⟩

end GlobalTheory.BddCpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_entries_of_isCompact_closure_zpowers_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  first | exact @GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers | exact GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommute
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepCommutant

theorem exists_eq_sum_pow_of_commute :
    ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  intro K _ n g t hs hc
  have hm := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute g t hs hc
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨p, rfl⟩ := hm
  set r := p %ₘ g.charpoly with hr
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hae : aeval g p = aeval g r := by
    exact (Polynomial.aeval_modByMonic_eq_self_of_root (Matrix.aeval_self_charpoly g)).symm
  have hdeg : r.degree < n := by
    have := Polynomial.degree_modByMonic_lt p hmon
    rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
  refine ⟨fun i => r.coeff i, ?_⟩
  change aeval g p = _
  rw [hae, aeval_def, eval₂_eq_sum, ← Polynomial.sum_fin (fun e a => algebraMap K (Matrix (Fin n) (Fin n) K) a * g ^ e) (by simp) hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]

end GlobalTheory.SepCommutant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommuteStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  first | exact @GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | exact GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | (intros; apply GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceGram

theorem det_trace_pow_gram_ne_zero {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : g.charpoly.Separable) :
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  set M : Matrix (Fin n) (Fin n) L := g.map f
  have hMc : M.charpoly = g.charpoly.map f := Matrix.charpoly_map g f
  have hnd : M.charpoly.roots.Nodup := by
    rw [hMc]; exact nodup_roots (hg.map)
  have hcard : M.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, GlobalTheory.CharpolyPow.card_roots_charpoly]
  set s := M.charpoly.roots.toFinset
  let e : Fin n ≃ s := (Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm
  let v : Fin n → L := fun i => (e i : L)
  have hv : Function.Injective v := fun a b h => e.injective (Subtype.ext h)
  have hsum : ∀ φ : L → L, (M.charpoly.roots.map φ).sum = ∑ i, φ (v i) := by
    intro φ
    have : M.charpoly.roots = s.val := by
      simp [s, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [this, ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have htr : ∀ m : ℕ, f (g ^ m).trace = ∑ i, v i ^ m := by
    intro m
    have h1 : f (g ^ m).trace = (M ^ m).trace := by
      have hp : M ^ m = (g ^ m).map f := by simp [M, Matrix.map_pow]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hp]; simp [Matrix.trace, Matrix.map_apply, map_sum]
    rw [h1, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, hsum]
  have hG : (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f
      = (vandermonde v)ᵀ * vandermonde v := by
    ext i j
    rw [vandermonde_transpose_mul_vandermonde, Matrix.map_apply, Matrix.of_apply, htr]
  intro h0
  have hd := RingHom.map_det f (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace)
  rw [h0, map_zero] at hd
  have h2 : ((vandermonde v)ᵀ * vandermonde v).det = 0 := by
    rw [← hG]; exact hd.symm
  rw [det_mul, det_transpose, mul_self_eq_zero] at h2
  exact det_vandermonde_ne_zero_iff.mpr hv h2

end GlobalTheory.TraceGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTracePowGramNeZeroStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  first | exact @GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | exact GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero | (intros; apply GlobalTheory.TraceGram.det_trace_pow_gram_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfPowBdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfPowBdd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceBdd

theorem trace_mem_valuationSubring_of_pow_bounded {K : Type} [Field K] (O : ValuationSubring K) [IsNoetherianRing O]
    (n : ℕ) (y : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ O) : y.trace ∈ O := by
  classical

  let N : Submodule O (Matrix (Fin n) (Fin n) K) :=
    Submodule.span O (Set.range fun p : Fin n × Fin n => a⁻¹ • Matrix.single p.1 p.2 (1 : K))
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  haveI : IsNoetherian O N := isNoetherian_of_fg_of_noetherian N hNfg
  have hpow : ∀ k : ℕ, y ^ k ∈ N := by
    intro k
    rw [Matrix.matrix_eq_sum_single (y ^ k)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hc : a * (y ^ k) i j ∈ O := h k i j
    have : Matrix.single i j ((y ^ k) i j) =
        (⟨a * (y ^ k) i j, hc⟩ : O) • (a⁻¹ • Matrix.single i j (1 : K)) := by
      rw [← algebraMap_smul K (⟨a * (y ^ k) i j, hc⟩ : O), smul_smul, Matrix.smul_single, smul_eq_mul]
      congr 1
      change (y ^ k) i j = a * (y ^ k) i j * a⁻¹ * 1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {y}) ≤ N := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    rintro x hx
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hx
    exact hpow k
  have hint : IsIntegral O y :=
    isIntegral_of_submodule_noetherian _ (isNoetherian_of_le hle) y (Algebra.self_mem_adjoin_singleton O y)
  obtain ⟨p, hpm, hp⟩ := hint

  have hpL : aeval (y.map (algebraMap K (AlgebraicClosure K))) (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
    have h1 : aeval y (p.map (algebraMap O K)) = 0 := by
      rw [aeval_map_algebraMap]; exact hp
    have h2 : aeval (y.map (algebraMap K (AlgebraicClosure K)))
          ((p.map (algebraMap O K)).map (algebraMap K (AlgebraicClosure K))) =
        (Algebra.ofId K (AlgebraicClosure K)).mapMatrix (aeval y (p.map (algebraMap O K))) := by
      rw [aeval_map_algebraMap]
      rw [← aeval_algHom_apply]
      rfl
    rw [IsScalarTower.algebraMap_eq O K (AlgebraicClosure K), ← Polynomial.map_map, h2, h1, map_zero]
  have hroot : ∀ μ ∈ (y.map (algebraMap K (AlgebraicClosure K))).charpoly.roots, IsIntegral O μ := by
    intro μ hμ
    have hs : μ ∈ spectrum (AlgebraicClosure K) (y.map (algebraMap K (AlgebraicClosure K))) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)
    have hs2 := spectrum.subset_polynomial_aeval (y.map (algebraMap K (AlgebraicClosure K)))
      (p.map (algebraMap O (AlgebraicClosure K))) ⟨μ, hs, rfl⟩
    rw [hpL] at hs2
    have h0 : eval μ (p.map (algebraMap O (AlgebraicClosure K))) = 0 := by
      by_contra hc
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Ne.isUnit hc).map _)
    exact ⟨p, hpm, by rwa [eval_map] at h0⟩
  have htr : algebraMap K (AlgebraicClosure K) y.trace = (y.map (algebraMap K (AlgebraicClosure K))).trace := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  have hL : IsIntegral O (algebraMap K (AlgebraicClosure K) y.trace) := by
    rw [htr, Matrix.trace_eq_sum_roots_charpoly]
    exact multiset_sum_mem _ (fun μ hμ => (mem_integralClosure_iff _ _).2 (hroot μ hμ))
  have hK : IsIntegral O y.trace :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).1 hL
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hK
  rw [← hz]
  exact z.2

end GlobalTheory.TraceBdd

theorem GlobalTheory.trace_mem_of_pow_bdd : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (a : w.adicCompletion E), a ≠ 0 →
    (∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ Ov E w) → y.trace ∈ Ov E w := by
  intro E _ _ w n y a ha h
  exact GlobalTheory.TraceBdd.trace_mem_valuationSubring_of_pow_bounded (w.adicCompletionIntegers E) n y a ha h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfPowBddStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mem_of_mul_pow_entries_mem : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (a : w.adicCompletion E), a ≠ 0 →
    (∀ k : ℕ, ∀ i j, a * (y ^ k) i j ∈ Ov E w) → y.trace ∈ Ov E w := by
  first | exact @GlobalTheory.trace_mem_of_pow_bdd | exact GlobalTheory.trace_mem_of_pow_bdd | (intros; apply GlobalTheory.trace_mem_of_pow_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntryMemSubringOfTraceGramUnitStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntryMemSubringOfTraceGramUnit
open Matrix

namespace GlobalTheory.TraceGram

theorem pow_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ O) (k : ℕ) : ∀ i j, (g ^ k) i j ∈ O := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (ih i l) (hg l j)

theorem adjugate_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by
  intro i j
  let G' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨G i j, hG i j⟩
  have h : O.subtype.mapMatrix G' = G := by
    ext i j; rfl
  rw [← h, ← RingHom.map_adjugate]
  exact (G'.adjugate i j).2

theorem entry_mem_of_trace_gram : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by
  intro K _ O n g x c hx hg htr hdet hinv
  set G : Matrix (Fin n) (Fin n) K := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hG : ∀ i j, G i j ∈ O := by
    intro i j
    simp only [hGdef, Matrix.of_apply, Matrix.trace, Matrix.diag_apply]
    exact O.sum_mem fun l _ => pow_entry_mem O g hg _ l l
  have hb : ∀ j, (c ᵥ* G) j ∈ O := by
    intro j
    have : (c ᵥ* G) j = (x * g ^ (j : ℕ)).trace := by
      rw [hx, Finset.sum_mul, Matrix.trace_sum]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply, smul_mul_assoc,
        Matrix.trace_smul, smul_eq_mul, pow_add]
    rw [this]; exact htr j
  have hc : ∀ i, c i ∈ O := by
    intro i
    have h1 : (c ᵥ* G) ᵥ* G.adjugate = G.det • c := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have h2 : c i = (G.det)⁻¹ * ((c ᵥ* G) ᵥ* G.adjugate) i := by
      rw [h1, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
    rw [h2]
    refine O.mul_mem hinv ?_
    change ∑ l, (c ᵥ* G) l * G.adjugate l i ∈ O
    exact O.sum_mem fun l _ => O.mul_mem (hb l) (adjugate_entry_mem O G hG l i)
  intro i j
  rw [hx, Matrix.sum_apply]
  refine O.sum_mem fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact O.mul_mem (hc l) (pow_entry_mem O g hg _ i j)

end GlobalTheory.TraceGram
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entry_mem_subring_of_trace_gram_unit : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by
  first | exact @GlobalTheory.TraceGram.entry_mem_of_trace_gram | exact GlobalTheory.TraceGram.entry_mem_of_trace_gram | (intros; apply GlobalTheory.TraceGram.entry_mem_of_trace_gram <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodCpt

theorem pow_mem_of_mem {K : Type} [Field K] (O : Subring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, M i j ∈ O) : ∀ k : ℕ, ∀ i j, (M ^ k) i j ∈ O := by
  intro k
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> simp [O.one_mem, O.zero_mem]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun m _ => O.mul_mem (ih i m) (hM m j)

theorem gram_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (g : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin n => ((g.map f) ^ ((i : ℕ) + j)).trace) =
      (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← Matrix.map_pow, Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  intro E _ _ _ hU n γ hs
  set g : Matrix (Fin n) (Fin n) E := γ.1.val with hgdef
  set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hd : G.det ≠ 0 := GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable g hs
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E (g i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => GlobalTheory.LocRatPt.eventually_valuation_le_one _
  filter_upwards [h1, GlobalTheory.LocRatPt.eventually_valuation_le_one (E := E) G.det⁻¹] with w hg hdi
  set f : E →+* w.adicCompletion E := algebraMap E (w.adicCompletion E)
  set gw : Matrix (Fin n) (Fin n) (w.adicCompletion E) := g.map f with hgw
  have hgwO : ∀ i j, gw i j ∈ Ov E w := fun i j => GlobalTheory.LocRatPt.algebraMap_mem_Ov (hg i j)
  have hsep : gw.charpoly.Separable := by rw [hgw, Matrix.charpoly_map]; exact hs.map
  have hGw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace) = G.map f := gram_map f g
  have hdet : (G.map f).det = f G.det := (RingHom.map_det f G).symm
  have hdw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
    rw [hGw, hdet]; exact (map_ne_zero f).2 hd
  have hdwi : ((Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ Ov E w := by
    rw [hGw, hdet, ← map_inv₀]; exact GlobalTheory.LocRatPt.algebraMap_mem_Ov hdi
  have hloc : (locPt w γ).1.1 = gw := by rw [GlobalTheory.LocRatPt.locPt_val hU]; rfl
  have key : ∀ s : UL n w, s * locPt w γ = locPt w γ * s →
      (∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (s ^ k).1.1 i j ∈ Ov E w) →
      ∀ i j, s.1.1 i j ∈ Ov E w := by
    rintro s hs' ⟨a, ha, hb⟩
    set x : Matrix (Fin n) (Fin n) (w.adicCompletion E) := s.1.1 with hx
    have hxc : x * gw = gw * x := by
      have := congrArg (fun u : UL n w => u.1.1) hs'
      simpa [hloc] using this
    have hpow : ∀ k : ℕ, (s ^ (k : ℤ)).1.1 = x ^ k := by
      intro k; rw [zpow_natCast]; simp [hx]
    obtain ⟨c, hcx⟩ := GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable gw x hsep hxc
    refine GlobalTheory.T.entry_mem_subring_of_trace_gram_unit (Ov E w) gw x c hcx hgwO (fun j => ?_) hdw hdwi
    refine GlobalTheory.T.trace_mem_of_mul_pow_entries_mem E w n _ a ha fun k i l => ?_
    have hcm : Commute x (gw ^ (j : ℕ)) := (Commute.pow_right hxc (j : ℕ))
    rw [hcm.mul_pow, ← pow_mul, Matrix.mul_apply, Finset.mul_sum]
    refine (Ov E w).sum_mem fun m _ => ?_
    rw [← mul_assoc, ← hpow]
    exact (Ov E w).mul_mem (hb _ i m) (pow_mem_of_mem _ gw hgwO _ m l)
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, hc⟩
  have ht' : t * locPt w γ = locPt w γ * t := ht
  obtain ⟨a, ha, hb⟩ := GlobalTheory.T.bounded_entries_of_isCompact_closure_zpowers_unitary E n w t hc
  have e1 := key t ht' ⟨a, ha, hb⟩
  have e2 := key t⁻¹ ((show Commute t (locPt w γ) from ht').inv_left).eq
    ⟨a, ha, fun k i j => by rw [_root_.inv_zpow']; exact hb (-k) i j⟩
  rw [SetLike.mem_coe, KL, Subgroup.mem_subgroupOf]
  exact GlobalTheory.LocRatPt.mem_GLint_of_entries e1 (fun i j => by simpa using e2 i j)

end GlobalTheory.BCT.GoodCpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAllStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centraliser_compactPart_le_integral_almostAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  first | exact @GlobalTheory.BCT.GoodCpt.main | exact GlobalTheory.BCT.GoodCpt.main | (intros; apply GlobalTheory.BCT.GoodCpt.main <;> assumption)
end
