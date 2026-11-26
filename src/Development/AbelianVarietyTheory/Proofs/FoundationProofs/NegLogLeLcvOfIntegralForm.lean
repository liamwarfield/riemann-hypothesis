module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem vw_gramR_locBasis_ge {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
    (Γ : Matrix (Fin d) (Fin d) K) (s : ℕ) (hs : 0 < s) (L : Submodule (𝓞 K) (Fin d → K))
    (hint : ∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ Γ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range)
    (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K) (hf : IsLocBasis L w f)
    (hG : gramR Γ f ≠ 0) : 0 ≤ (d : ℤ) * vw w (s : K) + vw w (gramR Γ f) := by
  classical
  have hmem : ∀ a, ∃ t ∈ ReductionFirst.Tw w, t • f a ∈ L := by
    intro a
    have h1 : f a ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range f)) :=
      ⟨1, (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal).one_mem, by
        rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
    rw [hf.2] at h1
    obtain ⟨t, ht, h⟩ := h1
    exact ⟨t, ReductionFirst.hcompl_le_Tw w ht, h⟩
  choose t ht htL using hmem
  have hT : (∏ a, t a) ∈ ReductionFirst.Tw w := Submonoid.prod_mem _ fun a _ => ht a
  have hTL : ∀ a, (∏ b, t b) • f a ∈ L := by
    intro a
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a), mul_smul]
    exact L.smul_mem _ (htL a)
  obtain ⟨T, hTdef⟩ : ∃ T, T = ∏ a, t a := ⟨_, rfl⟩
  rw [← hTdef] at hT
  simp only [← hTdef] at hTL
  choose Q hQ using fun a b => hint _ (hTL a) _ (hTL b)
  have hmap : (Matrix.of Q).map (algebraMap (𝓞 K) K) =
      ((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) •
        (Matrix.of fun a b => star (f a) ⬝ᵥ Γ.mulVec (f b)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hQ a b, ReductionFirst.smul_coe, ReductionFirst.smul_coe, star_smul, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, ReductionFirst.cO_coe, smul_eq_mul, smul_eq_mul]
    ring
  have hdet : algebraMap (𝓞 K) K (Matrix.of Q).det =
      ((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) ^ d * gramR Γ f := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_smul, Fintype.card_fin]
    rfl
  have hnn : 0 ≤ vw w (((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) ^ d * gramR Γ f) := by
    rw [← hdet]; exact ReductionFirst.vw_int_nonneg w _
  have hT0 := ReductionFirst.Tw_ne_zero hT
  have hT0' := ReductionFirst.Tw_ne_zero (ReductionFirst.cO_mem_Tw hT)
  have hs0 : (s : K) ≠ 0 := by exact_mod_cast hs.ne'
  rw [ReductionFirst.vw_mul w (pow_ne_zero _ (mul_ne_zero hs0 (mul_ne_zero hT0' hT0))) hG, ReductionFirst.vw_pow,
    ReductionFirst.vw_mul w hs0 (mul_ne_zero hT0' hT0), ReductionFirst.vw_mul w hT0' hT0, ReductionFirst.vw_unit w T hT.1,
    ReductionFirst.vw_unit w _ hT.2] at hnn
  simpa using hnn

theorem neg_log_le_lcv_of_integral_form :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) → ∀ (Γ : Matrix (Fin d) (Fin d) K) (s : ℕ), 0 < s → Γ.det ≠ 0 → (∏ v : InfinitePlace K, ‖v.embedding Γ.det‖ ≤ ∏ v : InfinitePlace K, (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re) → ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ Γ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((d : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ d X hX Γ s hs hΓ hle L hL hint
  classical
  have hli : LinearIndependent K (fun i => (Pi.single i 1 : Fin d → K)) := by
    have : (fun i => (Pi.single i 1 : Fin d → K)) = ⇑(Pi.basisFun K (Fin d)) := by
      funext i; simp [Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun K (Fin d)).linearIndependent
  obtain ⟨hfin, hlcv⟩ := covolume_via_basis K d X hX L hL _ hli
  obtain ⟨hGfin, hGpf⟩ := prod_formula' K _ hΓ
  obtain ⟨hsfin, hspf⟩ := Formalism.PairingDivisionLocalBalance.sum_valuation_nat K s
  obtain ⟨I, hI⟩ : ∃ I : HeightOneSpectrum (𝓞 K) → ℝ, I = fun w => lw w *
      (idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) L : ℝ) :=
    ⟨_, rfl⟩
  rw [← hI] at hfin hlcv

  have hpos : ∀ v : InfinitePlace K,
      0 < (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    intro v
    rw [Rb.gramStd]
    exact (Rb.pos_real (Rb.metMat_posDef X v (hX v)).det_pos).2
  have hpos' : ∀ v : InfinitePlace K, 0 < ‖v.embedding Γ.det‖ := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr hΓ)
  have hmean : ∑ v : InfinitePlace K, Real.log ‖v.embedding Γ.det‖ ≤
      ∑ v, Real.log (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    rw [← Real.log_prod (fun v _ => (hpos' v).ne'), ← Real.log_prod (fun v _ => (hpos v).ne')]
    exact Real.log_le_log (Finset.prod_pos fun v _ => hpos' v) hle
  have hinf : ∑ᶠ w, lw w * (vw w Γ.det : ℝ) ≤ (2 / (Module.finrank ℚ K : ℝ)) *
      ∑ v, Real.log (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    rw [← hGpf]
    exact mul_le_mul_of_nonneg_left hmean (by positivity)

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      0 ≤ (d : ℝ) * (lw w * (vw w (s : K) : ℝ)) + lw w * (vw w Γ.det : ℝ) + I w + I (conjPl w) := by
    intro w
    obtain ⟨hmul, hstar, hlw, -, -, -, -⟩ := valuation_basic_properties K w
    obtain ⟨f, hf⟩ := semilocal_basis_exists K d L hL w
    let γ : Matrix (Fin d) (Fin d) K := Matrix.of fun k i => f i k
    have hew : (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin d → K)) = f := by
      funext i j
      simp [γ, Finset.sum_apply, Pi.single_apply]
    have hdet : γ.det ≠ 0 := by
      have hu : IsUnit (Matrix.of f) := Matrix.linearIndependent_rows_iff_isUnit.mp hf.1
      have : γ = (Matrix.of f)ᵀ := by ext k i; rfl
      rw [this, Matrix.det_transpose]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hlb : IsLocBasis L w (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin d → K)) := by
      rw [hew]; exact hf
    obtain ⟨hi1, hi2⟩ := index_change_formula K d L hL.toIsLattice _ hli w γ hlb
    have hgc : gramR Γ f = star γ.det * γ.det * Γ.det := by
      rw [← hew, ← Rb.gramR_std Γ]
      exact gram_matrix_change K d d _ _ γ
    have hG : gramR Γ f ≠ 0 := by
      rw [hgc]; exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hΓ
    have h := vw_gramR_locBasis_ge Γ s hs L hint w f hf hG
    rw [hgc, hmul _ _ (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hΓ,
      hmul _ _ (star_ne_zero.mpr hdet) hdet, hstar] at h
    have h' : (0 : ℝ) ≤ (d : ℝ) * (vw w (s : K) : ℝ) +
        ((vw (conjPl w) γ.det : ℝ) + (vw w γ.det : ℝ) + (vw w Γ.det : ℝ)) := by exact_mod_cast h
    have hl0 : 0 ≤ lw w := div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have := mul_nonneg hl0 h'
    rw [hI]
    simp only
    rw [hi1, hi2, hlw]
    linarith
  have hinj : Function.Injective (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K)) :=
    fun a b h => by rw [← ValuationRepresentative.conjPl_conjPl a, h, ValuationRepresentative.conjPl_conjPl b]
  have hfc : (Function.support fun w => I (conjPl w)).Finite := hfin.preimage hinj.injOn
  have hsfin' : (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      (d : ℝ) * (lw w * (vw w (s : K) : ℝ))).Finite :=
    hsfin.subset (Function.support_mul_subset_right _ _)
  have h12 := (hsfin'.union hGfin).subset (Function.support_add _ _)
  have h123 := (h12.union hfin).subset (Function.support_add _ _)
  have htot := finsum_nonneg hloc
  rw [finsum_add_distrib h123 hfc, finsum_add_distrib h12 hfin, finsum_add_distrib hsfin' hGfin,
    finite_sum_conjugation K I, ← mul_finsum' _ _ hsfin, hspf] at htot
  rw [hlcv]
  linarith

end GlobalTheory.TestLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat


open Classical in
theorem blockForm_apply {F C I : Type} [CommRing F] [Fintype C] [Fintype I] {N : ℕ} (e : Fin N ≃ C × I)
    (M : Matrix I I F) (x y : Fin N → F) :
    x ⬝ᵥ (Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0) *ᵥ y =
      ∑ c, (fun i => x (e.symm (c, i))) ⬝ᵥ M *ᵥ (fun i => y (e.symm (c, i))) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp


open Classical in
theorem blockForm_posDef {C I : Type} [Fintype C] [Fintype I] {N : ℕ} (e : Fin N ≃ C × I)
    (M : Matrix I I ℂ) (hM : M.PosDef) :
    (Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : (e a).1 = (e b).1
    · rw [if_pos h, if_pos h.symm]
      exact hM.isHermitian.apply _ _
    · rw [if_neg h, if_neg (fun h' => h h'.symm), star_zero]
  · intro x hx
    rw [blockForm_apply]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun c _ => ?_) ⟨(e a).1, Finset.mem_univ _, ?_⟩
    · exact hM.posSemidef.dotProduct_mulVec_nonneg (fun i => x (e.symm (c, i)))
    · refine hM.dotProduct_mulVec_pos (x := fun i => x (e.symm ((e a).1, i))) ?_
      intro h0
      apply ha
      simpa using congrFun h0 (e a).2

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem IsDefGram.isUnit_det {n : ℕ} {G : Matrix (Fin n) (Fin n) K} (h : IsDefGram G) : IsUnit G.det := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h1 := (h.2.2 φ).det_pos
  have h2 : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
  rw [h2] at h1
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, map_zero] at h1
  exact lt_irrefl _ h1

theorem map_inv_of_isUnit {F F' : Type} [Field F] [Field F'] {n : ℕ} (φ : F →+* F') (G : Matrix (Fin n) (Fin n) F)
    (h : IsUnit G.det) : (G⁻¹).map φ = (G.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem IsDefGram.inv_transpose {n : ℕ} {G : Matrix (Fin n) (Fin n) K} (h : IsDefGram G) : IsDefGram (G⁻¹)ᵀ := by
  have hu := h.isUnit_det
  refine ⟨?_, ?_, fun φ => ?_⟩
  · have h1 : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, h.1]
    ext a b
    have := congrFun (congrFun h1 b) a
    simpa [Matrix.conjTranspose_apply] using this
  · intro a b
    set G0 : Matrix (Fin n) (Fin n) (cmMax K) := Matrix.of fun a b => ⟨G a b, h.2.1 a b⟩ with hG0
    have e0 : G = G0.map (cmMax K).subtype := by ext a b; rfl
    have hu0 : IsUnit G0.det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hu.ne_zero ?_
      have h2 : (G0.map (cmMax K).subtype).det = (cmMax K).subtype G0.det := (RingHom.map_det _ G0).symm
      rw [e0, h2, h0, map_zero]
    rw [Matrix.transpose_apply, e0, ← map_inv_of_isUnit _ _ hu0, Matrix.map_apply]
    exact (G0⁻¹ b a).2
  · rw [Matrix.transpose_map, map_inv_of_isUnit _ _ hu]
    exact (h.2.2 φ).inv.transpose


omit [NumberField K] in
theorem pairK_equivFun_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (u v : VVIdx lam → K) :
    pairK lam G ((bVV K lam).equivFun.symm u) ((bVV K lam).equivFun.symm v) =
      star u ⬝ᵥ (Matrix.of fun i j => pairK lam G (bVV K lam i) (bVV K lam j)) *ᵥ v := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum,
    LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Pi.star_apply, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sumGram_spec : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Fintype C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam), (∀ x y : Fin N → K, star x ⬝ᵥ sumGram lam e G *ᵥ y = ∑ c, pairK lam G (valAt lam e c x) (valAt lam e c y)) ∧ IsDefGram (sumGram lam e G) ∧ IsDefGram ((sumGram lam e G)⁻¹)ᵀ ∧ (∀ τ, IsUnit (G τ).det) := by
  intro K _ _ _ ι _ n lam G hG C _ N e
  have hdef : IsDefGram (sumGram lam e G) := by
    refine ⟨?_, ?_, fun φ => ?_⟩
    · ext a b
      simp only [sumGram, Matrix.conjTranspose_apply, Matrix.of_apply]
      by_cases h : (e a).1 = (e b).1
      · rw [if_pos h, if_pos h.symm]
        exact (pairSymm K ι n lam G fun τ => (hG τ).1).eq _ _
      · rw [if_neg h, if_neg (fun h' => h h'.symm), star_zero]
    · intro a b
      simp only [sumGram, Matrix.of_apply]
      split_ifs
      · exact pairingRational_holds K ι n lam _ G (fun τ => (hG τ).2.1) _ _
      · exact zero_mem _
    · have h1 := blockForm_posDef e _ (pairingPositive_holds K ι n lam G φ fun τ => (hG τ).2.2 φ)
      convert h1 using 1
      ext a b
      simp only [sumGram, Matrix.of_apply, Matrix.map_apply]
      split_ifs
      · rfl
      · exact map_zero φ
  refine ⟨fun x y => ?_, hdef, hdef.inv_transpose, fun τ => (hG τ).isUnit_det⟩
  have h1 := blockForm_apply e (Matrix.of fun i j => pairK lam G (bVV K lam i) (bVV K lam j)) (star x) y
  refine Eq.trans h1 (Finset.sum_congr rfl fun c _ => ?_)
  exact (pairK_equivFun_symm lam G (fun i => x (e.symm (c, i))) (fun i => y (e.symm (c, i)))).symm

end GlobalTheory.TestLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefiniteStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumPairingGramMatrix_values_and_definite : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Fintype C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam), (∀ x y : Fin N → K, star x ⬝ᵥ sumGram lam e G *ᵥ y = ∑ c, pairK lam G (valAt lam e c x) (valAt lam e c y)) ∧ IsDefGram (sumGram lam e G) ∧ IsDefGram ((sumGram lam e G)⁻¹)ᵀ ∧ (∀ τ, IsUnit (G τ).det) := by
  first | exact @GlobalTheory.TestLat.sumGram_spec | exact GlobalTheory.TestLat.sumGram_spec | (intros; apply GlobalTheory.TestLat.sumGram_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BoundedDenominatorsOfBeta
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def ClassTermBound : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * (T / Ω))

def ClassTermBoundBeta : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∀ Λ : PeriodPair, Λ.ω₁ = 1 → Λ.ω₂ = (1 + Complex.I * (Real.sqrt H.d : ℝ)) / 2 →
      ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * beta H.E H.d s κ Λ T)

theorem intAt_of_pow {l m : ℕ} (hm : 0 < m) {a : ℂ} (h : IntAt l (a ^ m)) : IntAt l a := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, IsIntegral.of_pow hm ?_⟩
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : IsIntegral ℤ ((n : ℂ) ^ m) := (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))).pow m |> fun h => by simpa using h
  have e : ((n : ℂ) * a) ^ (m + 1) = (n : ℂ) ^ m * ((n : ℂ) * a ^ (m + 1)) := by ring
  rw [e]
  exact h1.mul h

theorem intAt_natMul {l : ℕ} (k : ℕ) {a : ℂ} (h : IntAt l a) : IntAt l ((k : ℂ) * a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  have h1 : IsIntegral ℤ (k : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k : ℤ))
  rw [mul_left_comm]
  exact h1.mul h

def ringPair (d : ℕ) (hd : 0 < d) : PeriodPair where
  ω₁ := 1
  ω₂ := (1 + Complex.I * (Real.sqrt d : ℝ)) / 2
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h2 : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp at hi hr
    have hb : b = 0 := by
      rcases hi with hi | hi
      · exact hi
      · omega
    subst hb
    simpa using hr

theorem classTermBound_of_beta (h : ClassTermBoundBeta) : ClassTermBound := by
  intro R H I _ φ s κ 𝔣 χ hD
  have hd : 0 < H.d := H.hypOdd.2.1.pos
  set Λ := ringPair H.d hd
  have hC : ((C0 H.E H.d (2 * s) κ : ℝ) : ℂ) ≠ 0 := by
    have := hD.2.2.1
    exact_mod_cast (cmValueConst_pos H.E hd (by omega) κ).ne'
  have hΔ : latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (latDisc_ne_zero Λ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) (n := 12) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hz]; simp)
  refine ⟨z / C0 H.E H.d (2 * s) κ, div_ne_zero hz0 hC, fun l hl => ?_⟩
  obtain ⟨N, hN⟩ := h R H I φ s κ 𝔣 χ hD Λ rfl rfl l hl
  refine ⟨N, fun Q hQ hQl y T hT => intAt_of_pow (m := 12) (by norm_num) ?_⟩
  have := intAt_natMul (l ^ (11 * N)) (hN Q hQ hQl y T hT)
  convert this using 1
  unfold beta
  rw [← hz]
  push_cast
  field_simp
  ring

section Integral

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l : ℕ}

theorem isIntegral_of_intAt (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (ι : ℂ →+* AlgebraicClosure (FractionRing O)) {a : ℂ}
    (h : IntAt l a) : IsIntegral O (ι a) := by
  obtain ⟨n, hn, h⟩ := h
  have hu : IsUnit (n : O) := by
    by_contra hu
    have hn' : (n : O) ∈ IsLocalRing.maximalIdeal O := hu
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hn
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have : (x : O) * n + (y : O) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hxy
      rw [← this]
      exact add_mem (Ideal.mul_mem_left _ _ hn') (Ideal.mul_mem_left _ _ hl)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have h2 : IsIntegral O (ι ((n : ℂ) * a)) := h.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := v)).mul h2
  have h4 := congrArg (algebraMap O (AlgebraicClosure (FractionRing O))) hv
  rw [map_mul, map_natCast, map_one] at h4
  rwa [map_mul, map_natCast, ← mul_assoc, h4, one_mul] at h3

theorem exists_pow_mul_isIntegral (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (u : AlgebraicClosure (FractionRing O)) :
    ∃ M : ℕ, IsIntegral O ((l : AlgebraicClosure (FractionRing O)) ^ M * u) := by
  have ha : IsAlgebraic O u :=
    (IsFractionRing.isAlgebraic_iff O (FractionRing O) _).2 (Algebra.IsAlgebraic.isAlgebraic u)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hl
  obtain ⟨c, hc⟩ := hl
  refine ⟨n, ?_⟩
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := c ^ n * (↑v⁻¹ : O))).mul hint
  refine (congrArg (IsIntegral O) ?_).mpr h3
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← map_natCast (algebraMap O (AlgebraicClosure (FractionRing O))), ← map_pow, hc]
  congr 2
  rw [mul_assoc, ← mul_assoc (↑v⁻¹ : O), Units.inv_mul, one_mul, mul_pow, mul_comm]

theorem exists_eq_of_isIntegral {x : FractionRing O}
    (h : IsIntegral O (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O)) x)) :
    ∃ y : O, algebraMap O (FractionRing O) y = x :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algebraMap_iff ).1 h)

end Integral

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_bound_at (h : ClassTermBound) {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {s : ℕ}
    (ht : IsToricEltAt X i ι lam s) :
    ∃ n : ℕ, ∀ Q, BlochKatoReduction.Gen.QOk X i Q → ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
      ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, -, hth⟩ := ht
  obtain ⟨Ω, hΩ, hb⟩ := h D.R D.host I φ s κ 𝔣 χ hD
  obtain ⟨n, hn⟩ := hb (X.l i) (X.lPrime i).out
  obtain ⟨M, hM⟩ := exists_pow_mul_isIntegral (X.O_l i) (u * ι Ω)
  refine ⟨M + n, fun Q hQ δ => exists_eq_of_isIntegral ?_⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth Q hQ
  obtain ⟨h1, h2⟩ := placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣
  have hf : ({q | π q⁻¹ = δ} : Set (PicO (condQ 𝔣 (belowSet Q)))).Finite := Set.toFinite _
  have hs : IsIntegral (X.O i) (∑ q ∈ hf.toFinset, ι (((X.l i : ℕ) : ℂ) ^ n * (T q / Ω))) :=
    IsIntegral.sum _ fun q _ => isIntegral_of_intAt (X.O_l i) ι (hn _ h1 h2 _ _ (hT q))
  refine (congrArg (IsIntegral (X.O i)) ?_).mpr (hM.mul hs)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_pow, map_natCast, hδ, finsum_mem_eq_finite_toFinset_sum _ hf, ← map_sum, ← Finset.mul_sum, ← Finset.sum_div,
    map_mul, map_pow, map_natCast, map_div₀]
  have : ι Ω ≠ 0 := (map_ne_zero ι).2 hΩ
  field_simp
  ring

variable (X)

theorem exists_gen_bound (h : ClassTermBound) (ht : IsToricElt X) : ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0 := by
  classical
  have key : ∀ (i : X.Tw) (lam : X.abelian₂ i), ∃ n : ℕ, X.NonzeroIndexPlace i → ∀ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s → ∀ Q, BlochKatoReduction.Gen.QOk X i Q →
      ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
        ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
    intro i lam
    by_cases hx : X.NonzeroIndexPlace i ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s
    · obtain ⟨hi, s, hs⟩ := hx
      obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
      obtain ⟨ι, -, hι⟩ := ht i hi
      obtain ⟨n, hn⟩ := exists_bound_at h (hι lam s hs)
      exact ⟨n, fun _ _ _ => hn⟩
    · exact ⟨0, fun hi s hs => (hx ⟨hi, s, hs⟩).elim⟩
  choose n hn using key
  refine ⟨fun i => Finset.univ.sup (n i), fun i hi Q hQ lam s hs δ => ?_⟩
  obtain ⟨y, hy⟩ := hn i lam hi s hs Q hQ δ
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n i) (Finset.mem_univ lam))
  refine ⟨((X.l i : ℕ) : X.O i) ^ k * y, ?_⟩
  rw [map_mul, map_pow, map_natCast, hy]
  show _ = _ ^ (Finset.univ.sup (n i)) * _
  rw [hk]
  ring

end Record

end GlobalTheory.ToricDenom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNat
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MfactLeFactorialPow
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem mfact_le_factorial_pow : ∀ (n : ℕ) (ν : Fin n → ℕ) (R : ℕ), (∀ i, ν i ≤ R) → ∀ mo : Fin n × Fin n →₀ ℕ, (∀ t, ∑ a, mo (a, t) = ν t) → mfact mo ≤ (R.factorial) ^ n := by
  intro n ν R hR mo hmo
  have h : mfact mo = ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial := by
    change (mo.prod fun _ k => k.factorial) = _
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type_right]
  rw [h]
  calc ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial ≤ ∏ _t : Fin n, R.factorial := by
        refine Finset.prod_le_prod' fun t _ => ?_
        refine le_trans (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ fun a => mo (a, t))) ?_
        rw [hmo t]
        exact Nat.factorial_le (hR t)
    _ = R.factorial ^ n := by simp

end GlobalTheory.TestLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMvPolynomialCoeffAbsSumEqSumOfSupportSubset
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.IntMvPolynomialCoeffAbsSum

noncomputable def l1 {σ : Type*} (f : MvPolynomial σ ℤ) : ℕ :=
  ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs

variable {σ : Type*}

theorem intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset (f : MvPolynomial σ ℤ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    l1 f = ∑ mo ∈ s, (AddMonoidAlgebra.coeff f mo).natAbs := by
  unfold l1
  refine Finset.sum_subset h ?_
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.1 hm]

theorem intMvPolynomialCoeffAbsSum_add_le (f g : MvPolynomial σ ℤ) : l1 (f + g) ≤ l1 f + l1 g := by
  classical
  rw [intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset (f + g) (f.support ∪ g.support) MvPolynomial.support_add,
    intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset f (f.support ∪ g.support) Finset.subset_union_left,
    intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset g (f.support ∪ g.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  exact Int.natAbs_add_le _ _

theorem intMvPolynomialCoeffAbsSum_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem intMvPolynomialCoeffAbsSum_monomial (m : σ →₀ ℕ) (a : ℤ) : l1 (monomial m a) = a.natAbs := by
  classical
  rw [intMvPolynomialCoeffAbsSum_eq_sum_of_support_subset _ {m} MvPolynomial.support_monomial_subset]
  simp

theorem intMvPolynomialCoeffAbsSum_mul_le (f g : MvPolynomial σ ℤ) : l1 (f * g) ≤ l1 f * l1 g := by
  have h : f * g = ∑ m ∈ f.support, ∑ k ∈ g.support,
      monomial (m + k) (AddMonoidAlgebra.coeff f m * AddMonoidAlgebra.coeff g k) := by
    conv_lhs => rw [f.as_sum, g.as_sum, Finset.sum_mul_sum]
    simp only [monomial_mul]
  rw [h]
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  conv_rhs => unfold l1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun m _ => (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [intMvPolynomialCoeffAbsSum_monomial, Int.natAbs_mul]

theorem intMvPolynomialCoeffAbsSum_C (a : ℤ) : l1 (C a : MvPolynomial σ ℤ) = a.natAbs := intMvPolynomialCoeffAbsSum_monomial 0 a

theorem intMvPolynomialCoeffAbsSum_one : l1 (1 : MvPolynomial σ ℤ) = 1 := intMvPolynomialCoeffAbsSum_monomial 0 1

theorem intMvPolynomialCoeffAbsSum_X (v : σ) : l1 (X v : MvPolynomial σ ℤ) = 1 := intMvPolynomialCoeffAbsSum_monomial _ 1

theorem intMvPolynomialCoeffAbsSum_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intMvPolynomialCoeffAbsSum_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (intMvPolynomialCoeffAbsSum_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem intMvPolynomialCoeffAbsSum_pow_le (f : MvPolynomial σ ℤ) (k : ℕ) : l1 (f ^ k) ≤ l1 f ^ k := by
  simpa using intMvPolynomialCoeffAbsSum_prod_le (Finset.range k) (fun _ => f)

theorem intMvPolynomialCoeffAbsSum_det_X_le_factorial {s : ℕ} (v : Fin s → Fin s → σ) :
    l1 (Matrix.of fun p q : Fin s => (X (v p q) : MvPolynomial σ ℤ)).det ≤ s.factorial := by
  rw [Matrix.det_apply']
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  have : ∀ π : Equiv.Perm (Fin s), l1 ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) *
      ∏ i, (Matrix.of fun p q : Fin s => (X (v p q) : MvPolynomial σ ℤ)) (π i) i) ≤ 1 := by
    intro π
    refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ?_
    have h1 : l1 (((Equiv.Perm.sign π : ℤˣ) : ℤ) : MvPolynomial σ ℤ) = 1 := by
      have := intMvPolynomialCoeffAbsSum_C (σ := σ) ((Equiv.Perm.sign π : ℤˣ) : ℤ)
      rw [Int.units_natAbs] at this
      simpa using this
    rw [h1, one_mul]
    refine (intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_
    simp [intMvPolynomialCoeffAbsSum_X]
  refine (Finset.sum_le_sum fun π _ => this π).trans ?_
  simp [Fintype.card_perm]

theorem sum_range_sub_succ_add_eq_of_antitone (e : ℕ → ℕ) (he : Antitone e) (n : ℕ) :
    ∑ i ∈ Finset.range n, (e i - e (i + 1)) + e n = e 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := he (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at this
    omega

theorem sum_exponents_le {n : ℕ} (ν : Fin n → ℕ) (R : ℕ) (hν : Antitone ν) (hR : ∀ i, ν i ≤ R) :
    ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) ≤ R := by
  let e : ℕ → ℕ := fun i => if h : i < n then ν ⟨i, h⟩ else 0
  have he : Antitone e := by
    intro i j hij
    simp only [e]
    split_ifs with h1 h2 h3
    · exact hν hij
    · omega
    · omega
    · omega
  have h0 : e 0 ≤ R := by
    simp only [e]
    split_ifs
    · exact hR _
    · omega
  have h1 := sum_range_sub_succ_add_eq_of_antitone e he n
  have h2 : ∑ s : Fin n, (ν s - Formalism.GradedWeylDivisibility.nuNext ν s) = ∑ i ∈ Finset.range n, (e i - e (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => e i - e (i + 1)) n]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [e, Formalism.GradedWeylDivisibility.nuNext]
  omega

theorem highestWeightVector_coeff_natAbs_sum_le_factorial_pow : ∀ (n : ℕ) (ν : Fin n → ℕ) (R : ℕ), Antitone ν → (∀ i, ν i ≤ R) → ∑ mo ∈ (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν).support, (AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν) mo).natAbs ≤ (n.factorial) ^ R := by
  intro n ν R hν hR
  change l1 (Formalism.GradedWeylDivisibility.hw ℤ (le_refl n) ν) ≤ _
  unfold Formalism.GradedWeylDivisibility.hw
  refine (intMvPolynomialCoeffAbsSum_prod_le _ _).trans ?_
  refine le_trans (Finset.prod_le_prod' (g := fun s => n.factorial ^ (ν s - Formalism.GradedWeylDivisibility.nuNext ν s))
    fun s _ => ?_) ?_
  · refine (intMvPolynomialCoeffAbsSum_pow_le _ _).trans (Nat.pow_le_pow_left ?_ _)
    unfold Formalism.GradedWeylDivisibility.lpMinor
    exact (intMvPolynomialCoeffAbsSum_det_X_le_factorial _).trans (Nat.factorial_le s.isLt)
  · rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (Nat.factorial_pos n) (sum_exponents_le ν R hν hR)

end GlobalTheory.IntMvPolynomialCoeffAbsSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNat
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.ExtremalNorm

theorem weight_colW_apply {r n : ℕ} (mo : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) mo t = ∑ a, mo (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem fockS_extremal_eq_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  intro n lam R hR
  have hanti := Formalism.L2.DIV.natW_antitone lam
  set f : MvPolynomial (Fin n × Fin n) ℤ := extremal ℤ n lam with hf
  have hmem : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f lam.natW :=
    (Formalism.GradedWeylDivisibility.hwMem ℤ n n le_rfl _ hanti).1
  have hne : f ≠ 0 := Formalism.GradedWeylDivisibility.hwNe ℤ n n le_rfl _
  have hl1 : ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ≤ (n.factorial) ^ R :=
    GlobalTheory.IntMvPolynomialCoeffAbsSum.highestWeightVector_coeff_natAbs_sum_le_factorial_pow n lam.natW R hanti hR
  refine ⟨∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ^ 2 * mfact mo, ?_, ?_, ?_⟩
  · refine Finset.sum_pos (fun mo hmo => ?_) (support_nonempty.mpr hne)
    have h1 : 0 < (AddMonoidAlgebra.coeff f mo).natAbs := Int.natAbs_pos.mpr (mem_support_iff.mp hmo)
    have h2 : 0 < mfact mo := Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  · calc ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs ^ 2 * mfact mo
        ≤ ∑ mo ∈ f.support, (AddMonoidAlgebra.coeff f mo).natAbs * (n.factorial ^ R * R.factorial ^ n) := by
          refine Finset.sum_le_sum fun mo hmo => ?_
          have h1 : (AddMonoidAlgebra.coeff f mo).natAbs ≤ n.factorial ^ R :=
            (Finset.single_le_sum (f := fun mo => (AddMonoidAlgebra.coeff f mo).natAbs)
              (fun _ _ => Nat.zero_le _) hmo).trans hl1
          have h2 : mfact mo ≤ R.factorial ^ n := by
            refine GlobalTheory.TestLat.mfact_le_factorial_pow n lam.natW R hR mo fun t => ?_
            rw [← weight_colW_apply, hmem (mem_support_iff.mp hmo)]
          rw [pow_two, mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
      _ ≤ n.factorial ^ R * (n.factorial ^ R * R.factorial ^ n) := by
          rw [← Finset.sum_mul]
          exact Nat.mul_le_mul_right _ hl1
      _ = _ := by rw [two_mul, pow_add, mul_assoc]
  · intro K _ _ _
    have hinj : Function.Injective (Int.castRingHom K) := Int.cast_injective
    rw [← Formalism.L2.DIV.map_extremal (Int.castRingHom K) n lam, ← hf]
    unfold fockS
    rw [support_map_of_injective _ hinj, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h : (((AddMonoidAlgebra.coeff f m).natAbs ^ 2 : ℕ) : K) = ((AddMonoidAlgebra.coeff f m : ℤ) : K) * ((AddMonoidAlgebra.coeff f m : ℤ) : K) := by
      rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, pow_two, Int.cast_mul]
    rw [Nat.cast_mul, h]
    simp only [coeff_map, eq_intCast, star_intCast]

end GlobalTheory.ExtremalNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNatStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  first | exact @GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | exact GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | (intros; apply GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat <;> assumption)
end
end
