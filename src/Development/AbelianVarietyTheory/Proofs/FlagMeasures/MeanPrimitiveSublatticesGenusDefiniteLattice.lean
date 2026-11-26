module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusCyclicDiscriminantSplitPrime
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBoundedBasis
open NumberField Module Submodule
open ReciprocityTheory.ChartRestriction.G.FD (herm cc fdeg rdE)
open Formalism.MainNotions.StandardLattice (stdForm stdLat)
open Formalism.HermitianLatticesTheory (gmap isom genus)

namespace GlobalTheory.SmallRankMass

theorem transference_dual {M : ℕ} (hM : 1 ≤ M)
    (D : Basis (Fin M) ℝ (EuclideanSpace ℝ (Fin M))) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range D), x ≠ 0 → lam ≤ ‖x‖)
    (z : Fin M → EuclideanSpace ℝ (Fin M)) (hz : LinearIndependent ℝ z)
    (hzD : ∀ i j, ∃ m : ℤ, inner ℝ (z i) (D j) = m) :
    ∃ y : Fin M → EuclideanSpace ℝ (Fin M), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (D j) = m) ∧ ∀ i, ‖y i‖ ≤ 5 / 4 * (M / lam) := by
  have hT := transference_successive_minima M (span ℤ (Set.range D)) inferInstance (ZSpan.span_top D) 1 le_rfl hM
  rw [show M + 1 - 1 = M by omega] at hT
  have h1 : lam ≤ PI.succMin (span ℤ (Set.range D)) 1 := by
    apply le_csInf
    · refine ⟨‖D ⟨0, hM⟩‖, norm_nonneg _, fun _ => D ⟨0, hM⟩, fun _ => subset_span ⟨_, rfl⟩, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      exact D.ne_zero _
    · rintro t ⟨-, v, hvM, hvli, hvt⟩
      exact (hmin _ (hvM 0) (hvli.ne_zero 0)).trans (hvt 0)
  have h0 : 0 ≤ PI.succMin (PI.dualZ (span ℤ (Set.range D))) M := Real.sInf_nonneg (fun t ht => ht.1)
  have M0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlt : PI.succMin (PI.dualZ (span ℤ (Set.range D))) M < 5 / 4 * (M / lam) := by
    have : PI.succMin (PI.dualZ (span ℤ (Set.range D))) M ≤ M / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith
    have : 0 < (M : ℝ) / lam := by positivity
    linarith
  have hzm : ∀ i, z i ∈ PI.dualZ (span ℤ (Set.range D)) := by
    intro i x hx
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    choose m hm using hzD i
    refine ⟨∑ j, c j * m j, ?_⟩
    simp [inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hm]
  obtain ⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩ := exists_lt_of_csInf_lt
    (s := {t : ℝ | 0 ≤ t ∧ ∃ v : Fin M → EuclideanSpace ℝ (Fin M),
      (∀ j, v j ∈ PI.dualZ (span ℤ (Set.range D))) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t})
    ⟨∑ j, ‖z j‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), z, hzm, hz, fun j =>
      Finset.single_le_sum (f := fun j => ‖z j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)⟩ hlt
  exact ⟨v, hvli, fun i j => hvM i _ (subset_span ⟨j, rfl⟩), fun i => (hvt i).trans htlt.le⟩

theorem transference_rat {V : Type} [AddCommGroup V] [Module ℚ V] {M : ℕ} (hM : 1 ≤ M) (b : Basis (Fin M) ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) (hn : B.Nondegenerate)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, B u (b j) = k) → lam ^ 2 ≤ (B u u : ℝ)) :
    ∃ v : Fin M → V, (∀ i, v i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℚ v ∧
      ∀ i, (B (v i) (v i) : ℝ) ≤ (5 / 4 * ((M : ℝ) / lam)) ^ 2 := by
  have := b.finiteDimensional_of_finite
  obtain ⟨φ, hφ⟩ := ShortVectors.exists_euclidean (M := M)
    (by simpa using finrank_eq_card_basis b) B hs hp
  let d := B.dualBasis hn b
  have hd : ∀ i j, inner ℝ (φ (b i)) (φ (d j)) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hφ, LinearMap.BilinForm.apply_dualBasis_right hn hs]
    split_ifs <;> simp
  have hli : LinearIndependent ℝ (fun j => φ (d j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (inner ℝ (φ (b i))) hg
    simpa [inner_sum, real_inner_smul_right, hd] using this
  have hli' : LinearIndependent ℝ (fun j => φ (b j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun x => inner ℝ x (φ (d i))) hg
    simpa [sum_inner, real_inner_smul_left, hd] using this
  let D : Basis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp)
  have hD : ∀ j, D j = φ (d j) :=
    fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j
  have hnorm : ∀ x, ‖φ x‖ ^ 2 = (B x x : ℝ) := fun x => by
    rw [← hφ, real_inner_self_eq_norm_sq]
  obtain ⟨y, hyli, hyint, hy⟩ := transference_dual hM D lam hlam (by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : (∑ i, c i • D i) = φ (∑ i, c i • d i) := by simp [hD]
    rw [hw] at hx0 ⊢
    have h := hmin (∑ i, c i • d i) (fun h => hx0 (by rw [h, map_zero])) (fun j => ⟨c j, by
      simp [d, LinearMap.BilinForm.apply_dualBasis_left]⟩)
    rw [← hnorm] at h
    exact (pow_le_pow_iff_left₀ hlam.le (norm_nonneg _) two_ne_zero).1 h) _ hli'
    (fun i j => ⟨if i = j then 1 else 0, by rw [hD, hd]; split_ifs <;> simp⟩)
  choose m hm using hyint
  let v : Fin M → V := fun i => ∑ j, m i j • b j
  have hv : ∀ i, φ (v i) = y i := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis D fun j => ?_
    rw [hm, hD]
    simp [v, sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd]
  refine ⟨v, fun i => sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩), ?_, fun i => ?_⟩
  · refine LinearIndependent.of_comp φ ?_
    have : φ ∘ v = y := funext hv
    rw [this]
    exact hyli.restrict_scalars' ℚ
  · rw [← hnorm, hv]
    exact pow_le_pow_left₀ (norm_nonneg _) (hy i) 2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rdE_pos : 0 < rdE E := Real.rpow_pos_of_pos
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)) _


open ShortVectors in
theorem exists_bounded_basis {n : ℕ} (hn : 1 ≤ n) (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) :
    ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ Λ) ∧ LinearIndependent E v ∧
      ∀ (σ : E →+* ℂ) (i k : Fin n), ‖σ (herm 1 (v i) (v k))‖ ≤ 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2 := by
  obtain ⟨b, hb⟩ := exists_basis Λ hfg (DualFamily.span_eq_top Λ hfg hdual)
  have hf0 : 0 < fdeg E := ClassCount.fdeg_pos
  have hf : (0 : ℝ) < fdeg E := by exact_mod_cast hf0
  have hr : 0 < rdE E := rdE_pos
  have hl : 0 < 2 * (fdeg E : ℝ) / rdE E ^ 2 := by positivity
  obtain ⟨v, hv, hli, hle⟩ := transference_rat (Nat.mul_pos (by omega) hn) b (traceHerm n) (traceHerm_isSymm n)
    traceHerm_nonneg (traceHerm_nondegenerate n) _ (Real.sqrt_pos.mpr hl) (by
      intro u hu hk
      rw [Real.sq_sqrt hl.le, traceHerm_self]
      refine trace_dual_min Λ hint hdual u hu fun y hy => ?_
      obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 ((hb y).2 hy)
      choose k hk using hk
      refine ⟨∑ j, c j * k j, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← traceHerm_apply, map_sum]
      simp only [map_zsmul, hk]
      simp)
  have hle' : ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2 := by
    intro i τ
    have h := (two_mul_le_traceHerm (v i) τ).trans (hle i)
    have h4 : (5 / 4 * (((2 * fdeg E * n : ℕ) : ℝ) / √(2 * (fdeg E : ℝ) / rdE E ^ 2))) ^ 2
        = 25 / 16 * (2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2) := by
      rw [mul_pow, div_pow, div_pow, Real.sq_sqrt hl.le]
      push_cast
      field_simp
      norm_num
    have : 0 ≤ 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2 := by positivity
    linarith
  obtain ⟨s, hs1, hs2, -⟩ := euclidean_basis_exists E (Fin n → E) _ v hli (by simp [ShortVectors.finrank_eq])
  have hsr : s.card = n := by simpa using hs1
  let e : Fin n ≃ s := (s.equivFinOfCardEq hsr).symm
  exact ⟨fun i => v (e i), fun i => (hb _).1 (hv _), hs2.comp e e.injective, fun σ i k =>
    SelfDualClasses.norm_herm_le σ _ _ _ (hle' _ σ) (hle' _ σ)⟩


open StdMassBound RootClassCount in
theorem mass_le [StarRing E] (hs : ∀ x : E, star x = IsCMField.complexConj E x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hB : B = 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2) :
    Formalism.HermitianLatticesTheory.mass (stdForm E n) (stdLat E n) ≤ (1 + 2 * B) ^ (2 * fdeg E * n ^ 2) * (n * B) ^ (2 * fdeg E * n ^ 2) := by
  have B0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨R, -, H, hR⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
    {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)} B0 fun L hL =>
      ⟨by simp, fun x hx => (hL.2 x).1 hx,
        hB ▸ exists_bounded_basis hn L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
  refine le_trans ?_ hR
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs with hex
  swap
  · positivity
  obtain ⟨h1, h2⟩ := hex.choose_spec
  generalize hex.choose = s at h1 h2
  have key : ∀ M ∈ s, ∃ L₀ ∈ R, ∃ g ∈ isom (stdForm E n), gmap g L₀ = M := by
    intro M hM
    obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H M ⟨(h1 M hM).1.fg, fun y => by
      simp only [isIntegral_herm_iff]
      simpa only [hs] using selfDual_of_mem_genus (h1 M hM) y⟩
    have hγ' : (γ : Matrix (Fin n) (Fin n) E) * (γ : Matrix (Fin n) (Fin n) E).conjTranspose = 1 := by
      rw [← mul_conjTranspose_eq_one _ hγ]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply, hs]
    refine ⟨L₀, hL₀, matEquiv _ hγ', matEquiv_mem _ hγ', ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := (matEquiv _ hγ').surjective x
    constructor
    · rintro ⟨z, hz, e⟩
      rw [← e]
      exact (hm z).1 hz
    · intro hx
      exact ⟨x, (hm x).2 hx, rfl⟩
  choose! f hf g hg hfg using key
  have hcard : s.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn f (fun M hM => hf M hM) fun M hM N hN e => ?_
    have hM' : M ∈ s := hM
    have hN' : N ∈ s := hN
    refine (h2 M (h1 M hM')).unique ⟨hM', 1, one_mem _, Formalism.HermitianLatticesTheory.genusBasic_gmap_one _⟩
      ⟨hN', g M * (g N)⁻¹, mul_mem (hg M hM') (inv_mem (hg N hN')), ?_⟩
    have e1 : gmap (g N)⁻¹ N = f N := by
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (g N) (f N)
      rwa [hfg N hN'] at this
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, e1, ← e, hfg M hM']
  calc ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm E n) M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum fun M _ => Nat.cast_inv_le_one _
    _ = s.card := by simp
    _ ≤ R.card := by exact_mod_cast hcard


omit [IsCMField E] in
theorem mass_small [StarRing E] (hK : Formalism.HermitianLatticesTheory.IsCMUnram E) (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv E) {n : ℕ} (h1 : 1 ≤ n)
    (h2 : n ≤ 2) :
    Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form E n) (Formalism.HermitianLatticesTheory.massTelescope_lat E n) ≤
      (20 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ 2) ^ (16 * Formalism.HermitianLatticesTheory.fDeg E) := by
  have htc := hK.1
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  haveI : IsCMField E := by
    refine LeastExponentCompare.isCMField_of_conj E star hK.2.1 ?_
    by_contra hne
    push Not at hne
    refine IsTotallyComplex.complexEmbedding_not_isReal σ (ComplexEmbedding.isReal_iff.2 ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1, hne]
  have hs : ∀ x : E, star x = IsCMField.complexConj E x := fun x => σ.injective (by
    rw [hK.2.1, IsCMField.complexEmbedding_complexConj])
  have hf : fdeg E = Formalism.HermitianLatticesTheory.fDeg E := ClassCount.card_infinitePlace.symm
  have hr : rdE E = 2 * Formalism.HermitianLatticesTheory.vInv E := by
    rw [RootClassCount.rdE_eq, Formalism.HermitianLatticesTheory.vInv, ShortVectors.finrank_eq, hf]
    push_cast
    ring
  have hm := mass_le hs h1 rfl
  have e1 : stdForm E n = Formalism.HermitianLatticesTheory.massTelescope_form E n := LinearMap.ext fun x => LinearMap.ext fun y => rfl
  have e2 : stdLat E n = Formalism.HermitianLatticesTheory.massTelescope_lat E n := by
    unfold stdLat Formalism.HermitianLatticesTheory.massTelescope_lat
    congr 2
    exact funext fun i => (Pi.basisFun_apply E (Fin n) i).symm
  rw [e1, e2, hr, hf] at hm
  refine hm.trans ?_
  have f1 : (1 : ℝ) ≤ Formalism.HermitianLatticesTheory.fDeg E := by exact_mod_cast (Fintype.card_pos : 0 < Formalism.HermitianLatticesTheory.fDeg E)
  generalize Formalism.HermitianLatticesTheory.fDeg E = f at *
  generalize Formalism.HermitianLatticesTheory.vInv E = v at *
  have hw : 4 ≤ (2 * v) ^ 2 := by nlinarith
  generalize (2 * v) ^ 2 = w at *
  have hx : 4 ≤ f * w := by nlinarith
  rw [← mul_pow]
  have n2 : (n : ℝ) ≤ 2 := by exact_mod_cast h2
  have n0 : (0 : ℝ) ≤ n := by positivity
  have nn : (n : ℝ) ^ 2 ≤ 4 := by nlinarith
  have b : 2 * (f : ℝ) * n ^ 2 * w ≤ 8 * (f * w) := by nlinarith
  have b0 : 0 ≤ 2 * (f : ℝ) * n ^ 2 * w := by have : 0 ≤ w := by linarith
                                              positivity
  calc _ ≤ ((20 * (f : ℝ) * w) * (20 * f * w)) ^ (2 * f * n ^ 2) := by
        refine pow_le_pow_left₀ (by positivity) (mul_le_mul (by linarith) (by nlinarith) (by positivity)
          (by linarith)) _
    _ ≤ ((20 * (f : ℝ) * w) * (20 * f * w)) ^ (8 * f) := by
        refine pow_le_pow_right₀ (by nlinarith) ?_
        have : n ^ 2 ≤ 4 := by nlinarith
        nlinarith
    _ = _ := by rw [← sq, ← pow_mul]; congr 1; ring

end GlobalTheory.SmallRankMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisTail
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrthoMass

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ ms : ℕ → ℝ, (∀ n, 0 < ms n) ∧ ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n := by
  intro K _ _ _ hK
  refine ⟨fun n => Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n), fun n => ?_, ?_⟩
  · show 0 < Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n)
    rw [Formalism.MainNotions.StandardLattice.standard_form_eq_telescope_form, Formalism.MainNotions.StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos K hK n
  · intro n W _ _ _ _ h I _ ho
    exact Formalism.MainNotions.StandardLattice.mass_ortho K hK n W h I ho

end GlobalTheory.OrthoMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMass
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMass
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MassRatioBound

lemma core_two (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (hcmp : ∀ i t, 3 ≤ i → 1 ≤ t → m i ≤ m (i + t) * B ^ t)
    (h2 : ms 2 ≤ Mb) (t : ℕ) (ht : 2 ≤ t) (s : ℕ) (hs : 2 ≤ s) :
    ms s * ms t ≤ ms (s + t) * (Mb * (D * D) * B ^ (s * (s + t))) := by
  have hMb : 0 < Mb := (hpos 2).trans_le h2
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D := by linarith
  have hm : ∀ n, 2 ≤ n → 0 < m (n + 1) := by
    intro n hn
    have := hpos (n + 1)
    rw [hrec n hn] at this
    exact (mul_pos_iff_of_pos_left (hpos n)).mp this
  induction s, hs using Nat.le_induction with
  | base =>
    have e : 2 + t = t + 1 + 1 := by omega
    have a1 := hlow (t + 1) (by omega)
    have a2 := hlow (t + 1 + 1) (by omega)
    have p1 := hm t ht
    have p2 := hm (t + 1) (by omega)
    have a3 : 1 ≤ (m (t + 1) * D * B ^ (t + 1)) * (m (t + 1 + 1) * D * B ^ (t + 1 + 1)) :=
      one_le_mul_of_one_le_of_one_le a1 a2
    have a4 : B ^ (t + 1) * B ^ (t + 1 + 1) ≤ B ^ (2 * (t + 1 + 1)) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hB (by omega)
    rw [e, hrec (t + 1) (by omega), hrec t ht]
    have pt := hpos t
    calc ms 2 * ms t ≤ Mb * ms t := by gcongr
      _ ≤ Mb * ms t * ((m (t + 1) * D * B ^ (t + 1)) * (m (t + 1 + 1) * D * B ^ (t + 1 + 1))) :=
        le_mul_of_one_le_right (by positivity) a3
      _ = ms t * m (t + 1) * m (t + 1 + 1) * (Mb * (D * D) * (B ^ (t + 1) * B ^ (t + 1 + 1))) := by
        ring
      _ ≤ _ := by gcongr
  | succ s hs ih =>
    have e : s + 1 + t = s + t + 1 := by omega
    have a1 := hcmp (s + 1) t (by omega) (by omega)
    have p1 := hm s hs
    have p2 := hm (s + t) (by omega)
    have p3 := hpos (s + t)
    have a4 : B ^ (s * (s + t)) * B ^ t ≤ B ^ ((s + 1) * (s + t + 1)) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hB (by nlinarith)
    rw [e] at a1
    rw [e, hrec s hs, hrec (s + t) (by omega)]
    calc ms s * m (s + 1) * ms t = (ms s * ms t) * m (s + 1) := by ring
      _ ≤ (ms (s + t) * (Mb * (D * D) * B ^ (s * (s + t)))) * (m (s + t + 1) * B ^ t) := by
        gcongr
      _ = ms (s + t) * m (s + t + 1) * (Mb * (D * D) * (B ^ (s * (s + t)) * B ^ t)) := by ring
      _ ≤ _ := by gcongr

lemma core_one (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (h1 : ms 1 ≤ Mb) (t : ℕ) (ht : 2 ≤ t) (e : ℕ) (he : t + 1 ≤ e) :
    ms 1 * ms t ≤ ms (t + 1) * (Mb * (D * D) * B ^ e) := by
  have hMb : 0 < Mb := (hpos 1).trans_le h1
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D := by linarith
  have p1 : 0 < m (t + 1) := by
    have := hpos (t + 1)
    rw [hrec t ht] at this
    exact (mul_pos_iff_of_pos_left (hpos t)).mp this
  have a1 := hlow (t + 1) (by omega)
  have a4 : B ^ (t + 1) ≤ B ^ e := pow_le_pow_right₀ hB he
  have a5 : D ≤ D * D := le_mul_of_one_le_right hD0.le hD
  have pt := hpos t
  rw [hrec t ht]
  calc ms 1 * ms t ≤ Mb * ms t := by gcongr
    _ ≤ Mb * ms t * (m (t + 1) * D * B ^ (t + 1)) := le_mul_of_one_le_right (by positivity) a1
    _ = ms t * m (t + 1) * (Mb * D * B ^ (t + 1)) := by ring
    _ ≤ _ := by gcongr

lemma core (ms m : ℕ → ℝ) (D B Mb : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B) (hpos : ∀ n, 0 < ms n)
    (hrec : ∀ n, 2 ≤ n → ms (n + 1) = ms n * m (n + 1))
    (hlow : ∀ i, 3 ≤ i → 1 ≤ m i * D * B ^ i)
    (hcmp : ∀ i t, 3 ≤ i → 1 ≤ t → m i ≤ m (i + t) * B ^ t)
    (h1 : ms 1 ≤ Mb) (h2 : ms 2 ≤ Mb) (k s : ℕ) (hk : 3 ≤ k) (hs : 1 ≤ s) (hsk : s < k) :
    ms s * ms (k - s) ≤ ms k * (Mb * (D * D) * B ^ (s * k)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = s + t := ⟨k - s, by omega⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hs1 : s = 1
  · subst hs1
    rw [add_comm 1 t]
    exact core_one ms m D B Mb hD hB hpos hrec hlow h1 t (by omega) _ (by omega)
  by_cases ht1 : t = 1
  · subst ht1
    rw [mul_comm (ms s)]
    exact core_one ms m D B Mb hD hB hpos hrec hlow h1 s (by omega) _ (by nlinarith)
  exact core_two ms m D B Mb hD hB hpos hrec hlow hcmp h2 t (by omega) s (by omega)

lemma low_base (v : ℝ) (hv : 1 ≤ v) (i : ℕ) (hi : 1 ≤ i) :
    2 ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * 16 ^ i := by
  have hf : (1 : ℝ) ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hp := Real.pi_pos
  have h4 := Real.pi_le_four
  have h : 2 ≤ v / Real.pi * 16 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]; linarith
  have h' : (2 : ℝ) ≤ (v / Real.pi * 16) ^ i :=
    h.trans (le_self_pow₀ (by linarith) (by omega))
  rw [mul_assoc, ← mul_pow]
  nlinarith

lemma cmp_base (v : ℝ) (hv : 1 ≤ v) (i t : ℕ) (ht : 1 ≤ t) :
    ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * 4 ≤
      ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t) * 16 ^ t := by
  have hf : ((Nat.factorial (i - 1) : ℕ) : ℝ) ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hp := Real.pi_pos
  have h4 := Real.pi_le_four
  have h : 4 ≤ v / Real.pi * 16 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]; linarith
  have h' : (4 : ℝ) ≤ (v / Real.pi * 16) ^ t :=
    h.trans (le_self_pow₀ (by linarith) (by omega))
  have hv0 : 0 < v := by linarith
  calc _ ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i * (v / Real.pi * 16) ^ t := by
        gcongr
    _ = _ := by rw [mul_pow, pow_add]; ring

theorem mass_mul_mass_le : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (k s : ℕ) (Mb : ℝ) (ms : ℕ → ℝ), 3 ≤ k → 1 ≤ s → s < k → (∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n) → ms 1 ≤ Mb → ms 2 ≤ Mb → 1 ≤ Mb → ms s * ms (k - s) ≤ ms k * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * k * (Formalism.HermitianLatticesTheory.fDeg K))) := by
  intro hS K _ _ _ hCM hv k s Mb ms hk hs hsk hms h1 h2 _
  have hstd : ∀ n, Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form K n)
      (Formalism.HermitianLatticesTheory.massTelescope_lat K n) = ms n := fun n =>
    hms n _ _ _ (Formalism.HermitianLatticesTheory.massTelescope_symm K n) (Formalism.HermitianLatticesTheory.massTelescope_ortho K n)
  have hL := GlobalTheory.T.lValEta_mem_Icc_two_pow_fDeg K hCM
  set v := Formalism.HermitianLatticesTheory.vInv K with hvdef
  set f := Formalism.HermitianLatticesTheory.fDeg K with hfdef
  have hX : (1 : ℝ) ≤ (2 * v) ^ f := one_le_pow₀ (by linarith)
  have hD : 1 ≤ Real.sqrt ((2 * v) ^ f) := Real.one_le_sqrt.mpr hX
  have hDD : Real.sqrt ((2 * v) ^ f) * Real.sqrt ((2 * v) ^ f) = (2 * v) ^ f :=
    Real.mul_self_sqrt (by linarith)
  have hv0 : 0 < v := by linarith
  have hp := Real.pi_pos
  have key := core ms (Formalism.HermitianLatticesTheory.massRatioRightSide K) (Real.sqrt ((2 * v) ^ f)) (16 ^ f) Mb hD
    (one_le_pow₀ (by norm_num))
    (fun n => hstd n ▸ Formalism.HermitianLatticesTheory.massTelescope_std_pos K hCM n)
    (fun n hn => by
      rw [← hstd, ← hstd]; exact Formalism.HermitianLatticesTheory.massTelescope_step K hS hCM n hn)
    ?_ ?_ h1 h2 k s hk hs hsk
  · rw [hDD, ← pow_mul, mul_comm f] at key
    exact key
  · intro i hi
    have a := pow_le_pow_left₀ (by norm_num) (low_base v hv i (by omega)) f
    have b := (hL i (by omega)).1
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [← hvdef, ← hfdef]
    set D := Real.sqrt ((2 * v) ^ f)
    have hD0 : 0 < D := by linarith
    set A := ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i
    have e : A ^ f / D * Formalism.HermitianLatticesTheory.lValEta K i * D * (16 ^ f) ^ i
        = (A * 16 ^ i) ^ f * Formalism.HermitianLatticesTheory.lValEta K i := by
      rw [mul_pow A, ← pow_mul, ← pow_mul, mul_comm f i]; field_simp
    rw [e]
    calc (1 : ℝ) = 2 ^ f * (2 ^ f)⁻¹ := by field_simp
      _ ≤ _ := by
        refine mul_le_mul a b (by positivity) (le_trans (by positivity) a)
  · intro i t hi ht
    have a := pow_le_pow_left₀ (by positivity) (cmp_base v hv i t ht) f
    have b := (hL i (by omega)).2
    have c := (hL (i + t) (by omega)).1
    unfold Formalism.HermitianLatticesTheory.massRatioRightSide
    rw [← hvdef, ← hfdef]
    set D := Real.sqrt ((2 * v) ^ f)
    have hD0 : 0 < D := by linarith
    have hA : 0 ≤ ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i := by positivity
    have hA' : 0 ≤ ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t) := by positivity
    set A := ((Nat.factorial (i - 1) : ℕ) : ℝ) * (v / Real.pi) ^ i
    set A' := ((Nat.factorial (i + t - 1) : ℕ) : ℝ) * (v / Real.pi) ^ (i + t)
    have e4 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
    calc A ^ f / D * Formalism.HermitianLatticesTheory.lValEta K i ≤ A ^ f / D * 2 ^ f := by gcongr
      _ = (A * 4) ^ f / D * (2 ^ f)⁻¹ := by rw [mul_pow A, e4]; field_simp
      _ ≤ (A' * 16 ^ t) ^ f / D * Formalism.HermitianLatticesTheory.lValEta K (i + t) := by gcongr
      _ = _ := by rw [mul_pow A', ← pow_mul, ← pow_mul, mul_comm f t]; ring

end GlobalTheory.MassRatioBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularHermitianMassMulLeMassStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodularHermitianMass_mul_le_mass : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (k s : ℕ) (Mb : ℝ) (ms : ℕ → ℝ), 3 ≤ k → 1 ≤ s → s < k → (∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n) → ms 1 ≤ Mb → ms 2 ≤ Mb → 1 ≤ Mb → ms s * ms (k - s) ≤ ms k * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * k * (Formalism.HermitianLatticesTheory.fDeg K))) := by
  first | exact @GlobalTheory.MassRatioBound.mass_mul_mass_le | exact GlobalTheory.MassRatioBound.mass_mul_mass_le | (intros; apply GlobalTheory.MassRatioBound.mass_mul_mass_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveSublatticesGenusDefiniteLattice
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.PrimGenus

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : GlobalTheory.Mass.PD h) : h.Nondegenerate := by
  unfold GlobalTheory.Mass.PD at hp
  have key : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hlt := hp (Classical.arbitrary (K →+* ℂ)) x hne
    rw [hx, map_zero, Complex.zero_re] at hlt
    exact lt_irrefl _ hlt
  constructor
  · intro x hx
    exact key x (hx x)
  · intro y hy
    exact key y (hy y)

end

theorem gen_of_cyclic {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] {A B : Submodule R W} (hle : B ≤ A)
    (I : Ideal R) (e : (↥A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) :
    ∃ t : Finset W, t.card ≤ 1 ∧ A = B ⊔ Submodule.span R (t : Set W) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Ideal.Quotient.mk I 1))
  refine ⟨{(a : W)}, by simp, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
    have hmk : Ideal.Quotient.mk I r = r • Ideal.Quotient.mk I 1 := by
      rw [Algebra.smul_def, map_one, mul_one]
      rfl
    have h1 : Submodule.Quotient.mk (⟨x, hx⟩ : A) = Submodule.Quotient.mk (p := B.comap A.subtype) (r • a) := by
      rw [Submodule.Quotient.mk_smul, ha, ← LinearEquiv.map_smul, ← hmk, hr, LinearEquiv.symm_apply_apply]
    rw [Submodule.Quotient.eq] at h1
    have h2 : x - r • (a : W) ∈ B := by simpa using h1
    have h3 : x = (x - r • (a : W)) + r • (a : W) := by abel
    rw [h3]
    exact Submodule.add_mem_sup h2 (Submodule.smul_mem _ r (Submodule.subset_span (by simp)))
  · exact sup_le hle (Submodule.span_le.mpr (by simp [a.2]))

theorem exponents (n D k s l : ℝ) (hn : 1 ≤ n) (hD : 1 ≤ D) (hs : 0 ≤ s) :
    n ^ ((k - s) / 2) * (n * D) ^ ((9 * s + 8 + 4 * l) / 2) ≤
      D ^ ((k - 1) / 2) * ((n / D) ^ (k / 2) * (n * D) ^ (5 * s + 5 + 2 * (1 + l))) := by
  have hn0 : 0 < n := by linarith
  have hD0 : 0 < D := by linarith
  have ha : 0 ≤ Real.log n := Real.log_nonneg hn
  have hb : 0 ≤ Real.log D := Real.log_nonneg hD
  simp only [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos (mul_pos hn0 hD0),
    Real.rpow_def_of_pos (div_pos hn0 hD0), Real.log_mul hn0.ne' hD0.ne', Real.log_div hn0.ne' hD0.ne',
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ha hs, mul_nonneg hb hs]

private theorem finrank_eq_two_mul_fDeg (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
  haveI := hK.1
  rw [IsTotallyComplex.finrank]
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    zero_add]

private theorem mass_bound_rpow_le (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K) :
    1 ≤ (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) ∧
    (20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (16 * Formalism.HermitianLatticesTheory.fDeg K) ≤
      (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) := by
  have hd := finrank_eq_two_mul_fDeg K hK
  have hfpos : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hf : (1 : ℝ) ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) := by exact_mod_cast hfpos
  have hB : 1 ≤ 20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2 := by nlinarith
  have hd2 : (2 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    rw [hd]
    push_cast
    linarith
  have hl : 1 ≤ Real.logb 2 (Module.finrank ℚ K : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hd2
  have hcf : 2 ≤ cf K := by
    unfold cf
    linarith
  refine ⟨Real.one_le_rpow hB (by nlinarith), ?_⟩
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hB
  push_cast
  nlinarith

private theorem laurent_T_unit_zpow_eq_T (T : ℝ) (hT : 2 ≤ T) (k f : ℕ) (hk : 1 ≤ k) :
    (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) ≤ ((T ^ k - 1) / (T - 1)) ^ f := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : (T ^ (2 * f)) ^ (((k : ℝ) - 1) / 2) = (T ^ (k - 1)) ^ f := by
    rw [← Real.rpow_natCast T (2 * f), ← Real.rpow_mul hT0, ← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast [Nat.cast_sub hk]
    ring
  rw [h1]
  apply pow_le_pow_left₀ (pow_nonneg hT0 _)
  rw [le_div_iff₀ (by linarith)]
  have h2 : (1 : ℝ) ≤ T ^ (k - 1) := one_le_pow₀ (by linarith)
  have h3 : T ^ k = T ^ (k - 1) * T := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3]
  nlinarith

private theorem le_dual_of_integral_form {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (hi : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (1 : Submodule (𝓞 K) K)) : L ≤ Formalism.HermitianLatticesTheory.dual h L := by
  intro x hx
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  intro y hy
  first
  | exact hi x hx y hy
  | exact hi y hy x hx
  | simpa using hi x hx y hy
  | simpa using hi y hy x hx

private theorem norm_cofactor_le_of_factorization {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    GlobalTheory.Mass.discN h L = T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  have hc : GlobalTheory.Mass.discN h L = Nat.card (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}) := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN AddSubgroup.relIndex AddSubgroup.index
    exact Nat.card_congr e.toEquiv
  rw [hc, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have hT : ((T : 𝓞 K)) = algebraMap ℤ (𝓞 K) (T : ℤ) := by simp
  rw [hT, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, finrank_eq_two_mul_fDeg K hK]
  simp [Int.natAbs_pow]

private theorem mul_mul_mul_le_of_bounds (A Bm X Y C R Q1 Q2 G mk : ℝ) (h10 : Bm * A ≤ mk * C) (hexp : X * Y ≤ R * (Q1 * Q2))
    (htp : R ≤ G) (hXY : 0 ≤ X * Y) (hkC : 0 ≤ mk * C) (hQ : 0 ≤ Q1 * Q2) :
    A * Bm * X * Y ≤ mk * G * C * Q1 * Q2 := by
  calc A * Bm * X * Y = (Bm * A) * (X * Y) := by ring
    _ ≤ (mk * C) * (R * (Q1 * Q2)) := mul_le_mul h10 hexp hXY hkC
    _ ≤ (mk * C) * (G * (Q1 * Q2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htp hQ) hkC
    _ = mk * G * C * Q1 * Q2 := by ring

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ s n : ℕ, 1 ≤ s → s < (Module.finrank K V) → 1 ≤ n → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((GlobalTheory.Mass.primSp H.B.flip L ((Module.finrank K V) - s) n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K))) * ((n : ℝ) / D₀) ^ (((Module.finrank K V) : ℝ) / 2) * ((n : ℝ) * D₀) ^ (5 * (s : ℝ) + 5 + 2 * cf K)) := by
  intro hMax hS K V _ _ _ _ _ _ _ _ H hK hO hv hPD hk T L₀ Mb hT hTP hL₀ hq hMb D₀ hD₀ s n hs hsk hn
  obtain ⟨ms, hms0, hms⟩ := GlobalTheory.OrthoMass.main K hK
  have hsymm : H.B.flip.IsSymm := GlobalTheory.HermLat.flip_isSymm H
  have hnd : H.B.flip.Nondegenerate := nondeg_of_pd H.B.flip hPD
  have hgen := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V H.B.flip hK hsymm hnd T hT hTP
  obtain ⟨-, -, hstab, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V H.B.flip hK hsymm hPD L₀ hL₀.1
  have hsk' : Module.finrank K V - s + s = Module.finrank K V := Nat.sub_add_cancel hsk.le
  have key := GlobalTheory.T.primitiveSublattice_mean_count_bound hMax K V H.B.flip hK hsymm hPD hO (Module.finrank K V - s) s (by omega) hs hsk'
    (Fin (Module.finrank K V - s) → K) (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_ortho K _)
    (Fin s → K) (Formalism.HermitianLatticesTheory.massTelescope_form K s) (Formalism.HermitianLatticesTheory.massTelescope_lat K s)
    (Formalism.HermitianLatticesTheory.massTelescope_symm K s) (Formalism.HermitianLatticesTheory.massTelescope_ortho K s)
    n (T ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) hn (Nat.one_le_pow _ _ hT.pos)
    (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) hstab (fun L hL => by
      obtain ⟨hLi, ⟨eL⟩⟩ := (hgen.2 L₀ L hL₀ hq).mp hL
      exact ⟨hLi, norm_cofactor_le_of_factorization hK H.B.flip L T eL, gen_of_cyclic (le_dual_of_integral_form H.B.flip L hLi.2) _ eL⟩)
  have hm : ∀ j, Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form K j) (Formalism.HermitianLatticesTheory.massTelescope_lat K j) = ms j :=
    fun j => hms j _ _ _ (Formalism.HermitianLatticesTheory.massTelescope_symm K j) (Formalism.HermitianLatticesTheory.massTelescope_ortho K j)
  rw [hm, hm] at key
  have hmass := GlobalTheory.T.mass_genus_cyclicDiscriminant_splitPrime hMax K V H.B.flip hK hsymm hPD (by omega) (Fin (Module.finrank K V) → K)
    (Formalism.HermitianLatticesTheory.massTelescope_form K _) (Formalism.HermitianLatticesTheory.massTelescope_symm K _) (Formalism.HermitianLatticesTheory.massTelescope_lat K _)
    (Formalism.HermitianLatticesTheory.massTelescope_ortho K _) T hT hTP L₀ hL₀ hq
  rw [hm] at hmass
  obtain ⟨hMb1, hMbB⟩ := mass_bound_rpow_le K hK hv
  rw [← hMb] at hMb1 hMbB
  have hsmall : ∀ j, 1 ≤ j → j ≤ 2 → ms j ≤ Mb := fun j h1 h2 => by
    rw [← hm j]
    exact (GlobalTheory.SmallRankMass.mass_small hK hv h1 h2).trans hMbB
  have h10 := GlobalTheory.T.unimodularHermitianMass_mul_le_mass hS K hK hv (Module.finrank K V) s Mb ms hk hs hsk hms
    (hsmall 1 le_rfl (by norm_num)) (hsmall 2 (by norm_num) le_rfl) hMb1
  have hexp := exponents (n : ℝ) ((T : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K)) (Module.finrank K V : ℝ) (s : ℝ)
    (Real.logb 2 (Module.finrank ℚ K)) (by exact_mod_cast hn) (one_le_pow₀ (by exact_mod_cast hT.one_lt.le))
    (by positivity)
  have htp := laurent_T_unit_zpow_eq_T (T : ℝ) (by exact_mod_cast hT.two_le) (Module.finrank K V) (Formalism.HermitianLatticesTheory.fDeg K) (by omega)
  have hC : 0 ≤ Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) :=
    mul_nonneg (mul_nonneg (by linarith) (pow_nonneg (by linarith) _)) (by positivity)
  subst hD₀
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hmass, Nat.cast_sub hsk.le, Nat.cast_pow]
  exact mul_mul_mul_le_of_bounds _ _ _ _ _ _ _ _ _ _ h10 hexp htp (by positivity) (mul_nonneg (hms0 _).le hC) (by positivity)

end GlobalTheory.DegCnt.PrimGenus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveSublatticesGenusDefiniteLatticeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_primitiveSublattices_genus_definiteLattice : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → GlobalTheory.Mass.PD H.B.flip → 3 ≤ (Module.finrank K V) → ∀ (T : ℕ) (L₀ : Submodule (𝓞 K) V) (Mb : ℝ), T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → GlobalTheory.Mass.IsIntLat H.B.flip L₀ → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual H.B.flip L₀) ⧸ L₀.comap (Formalism.HermitianLatticesTheory.dual H.B.flip L₀).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → Mb = (20 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) * (6 + cf K)) → ∀ D₀ : ℝ, D₀ = (T : ℝ) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K)) → ∀ s n : ℕ, 1 ≤ s → s < (Module.finrank K V) → 1 ≤ n → GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom H.B.flip) (Formalism.HermitianLatticesTheory.genus H.B.flip L₀) (fun L => (((GlobalTheory.Mass.primSp H.B.flip L ((Module.finrank K V) - s) n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass H.B.flip L₀ * (Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (Formalism.HermitianLatticesTheory.fDeg K) * 16 ^ (s * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K))) * ((n : ℝ) / D₀) ^ (((Module.finrank K V) : ℝ) / 2) * ((n : ℝ) * D₀) ^ (5 * (s : ℝ) + 5 + 2 * cf K)) := by
  first | exact @GlobalTheory.DegCnt.PrimGenus.main | exact GlobalTheory.DegCnt.PrimGenus.main | (intros; apply GlobalTheory.DegCnt.PrimGenus.main <;> assumption)
end
