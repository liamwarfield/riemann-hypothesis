module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemGenusIffMaximalIntegralHermitianLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalLatticeLocalFactorProductPosAndLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalLatticeLocalFactorProductPosAndLe
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.MaxLatLam

theorem factor_bounds {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    0 < (q ^ n - (-1) ^ n) / (q + 1) ∧ (q ^ n - (-1) ^ n) / (q + 1) ≤ (q ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : q ≤ q ^ n := le_self_pow₀ (by linarith) (by omega)
  have h2 : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := neg_one_pow_eq_or ℝ n
  have h3 : (q ^ 2) ^ ((n : ℝ) / 2) = q ^ n := by
    rw [← Real.rpow_natCast q 2, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast q n]
    congr 1
    push_cast
    ring
  refine ⟨div_pos (by rcases h2 with e | e <;> rw [e] <;> linarith) (by linarith), ?_⟩
  rw [h3, div_le_iff₀ (by linarith)]
  rcases h2 with e | e <;> rw [e] <;> nlinarith

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → 1 ≤ Module.finrank K V → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → 0 < lamMax h M ∧ lamMax h M ≤ (discN h M : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd hn M hM
  obtain ⟨hfin, hd, -, hP⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM
  rw [hd, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin]
  have hq : ∀ P ∈ hfin.toFinset, (2 : ℝ) ≤ (qIn P : ℝ) := fun P hp => by
    exact_mod_cast (hP P (hfin.mem_toFinset.1 hp)).2.1
  refine ⟨Finset.prod_pos fun P hp => (factor_bounds (hq P hp) hn).1, ?_⟩
  rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun P _ => Nat.cast_nonneg _)]
  refine Finset.prod_le_prod₀ (fun P hp => (factor_bounds (hq P hp) hn).1.le) fun P hp => ?_
  rw [(hP P (hfin.mem_toFinset.1 hp)).2.2.1, Nat.cast_pow]
  exact (factor_bounds (hq P hp) hn).2

end GlobalTheory.MaxLatLam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalLatticeLocalFactorProductPosAndLeStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalLatticeLocalFactorProduct_pos_and_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → 1 ≤ Module.finrank K V → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → 0 < lamMax h M ∧ lamMax h M ≤ (discN h M : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
  first | exact @GlobalTheory.MaxLatLam.main | exact GlobalTheory.MaxLatLam.main | (intros; apply GlobalTheory.MaxLatLam.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesOfIndexLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesOfIndexLe
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem sublattice_count : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ M hM i hi
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.IsTorsionFree (𝓞 K) M := inferInstance
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
    have h1 : Module.rank (𝓞 K) M ≤ Module.rank K V := by
      rw [IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
      exact Submodule.rank_le M
    exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K V)
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (Module.finrank K V) i hi hr
  have hinj : Set.InjOn (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i} := by
    intro N hN N' hN' e
    have := congrArg (Submodule.map M.subtype) e
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr hN.1, inf_eq_right.mpr hN'.1] using this
  have hmaps : Set.MapsTo (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}
      {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i} := by
    intro N hN
    exact hN.2
  have h2 := Set.encard_le_encard_of_injOn hmaps hinj
  rw [← hfin.cast_ncard_eq] at h2
  calc _ ≤ (((({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast h2
    _ = ENNReal.ofReal ({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℝ) := by
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

end GlobalTheory.Mass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesOfIndexLeStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_sublattices_of_index_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by
  first | exact @GlobalTheory.Mass.sublattice_count | exact GlobalTheory.Mass.sublattice_count | (intros; apply GlobalTheory.Mass.sublattice_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLe
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.SpaceMass

theorem nondeg_of_PD {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

theorem PD_of_ortho {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (I : Submodule (𝓞 K) V) (n : ℕ)
    (hI : IsOrthoLattice h I n) : PD h := by
  obtain ⟨e, -, hsp, -, hort⟩ := hI
  intro τ x hx
  have hx' : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
  have e1 : h (∑ i, a i • e i) (∑ i, a i • e i) = ∑ i, star (a i) * a i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      hort, smul_eq_mul, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have e2 : (τ (∑ i, star (a i) * a i)).re = ∑ i, Complex.normSq (τ (a i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hK.2.1, Complex.normSq_eq_conj_mul_self.symm]
    simp
  rw [e1, e2]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (by simp [hc])
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.2 ((map_ne_zero τ).2 hi)

theorem mem_genus_self {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsFullLattice K M) : M ∈ genus h M := by
  refine ⟨hM, fun p _ => ⟨1, (isom h).one_mem, ?_⟩⟩
  exact one_smul (isom h) (loc (K := K) p M)

theorem real_bound (n' i : ℕ) (j l c m : ℝ) (hn : 1 ≤ n') (hl : 0 ≤ l) (hc : 0 ≤ c)
    (hm : m ≤ c * (n' : ℝ) ^ (j / 2)) :
    (i : ℝ) ^ (j + l) * m ≤ c * ((n' * i ^ 2 : ℕ) : ℝ) ^ ((j + l) / 2) := by
  have h1 : (n' : ℝ) ^ (j / 2) ≤ (n' : ℝ) ^ ((j + l) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have h2 : ((n' * i ^ 2 : ℕ) : ℝ) ^ ((j + l) / 2) = (n' : ℝ) ^ ((j + l) / 2) * (i : ℝ) ^ (j + l) := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2
    push_cast
    ring
  have h3 : (0 : ℝ) ≤ (i : ℝ) ^ (j + l) := by positivity
  rw [h2]
  calc (i : ℝ) ^ (j + l) * m ≤ (i : ℝ) ^ (j + l) * (c * (n' : ℝ) ^ ((j + l) / 2)) :=
        mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left h1 hc)) h3
    _ = _ := by ring

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ n : ℕ, 1 ≤ n → orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h' I * (n : ℝ) ^ (((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hj V' _ _ _ _ _ h' hs' I hI n hn
  have hnd := nondeg_of_PD h hp
  have hp' := PD_of_ortho h' hK I _ hI
  have hnd' := nondeg_of_PD h' hp'
  rcases (latsDisc (R := 𝓞 K) h n).eq_empty_or_nonempty with hE | ⟨M₁, hM₁⟩
  · rw [hE]
    unfold orbMass orbSum
    refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun q => q.2.elim) zero_le
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨M₀, hM₀, hle₀⟩ := hex M₁ hM₁.1

  obtain ⟨c, hc⟩ := hMM K hK _ hj
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  have hIfull : Submodule.IsFullLattice K I := by
    refine { toIsLattice := hIl, span_eq_top := ?_ }
    obtain ⟨e, -, hspan, rfl, -⟩ := hI
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIfull hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hcpos : 0 < c := hcI ▸ (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V' h' hK hs' hp' I hIfull).2.1
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  obtain ⟨hi0, hn₀⟩ := (hdisc M₁ hM₁.1).2.2.1 M₀ hM₀.1 hle₀
  have hn'0 := (hdisc M₀ hM₀.1).1
  set n' := discN h M₀ with hn'
  set i := idxN M₀ M₁ with hi
  have hnn : n = n' * i ^ 2 := hM₁.2 ▸ hn₀
  have hm₀ : mass h M₀ ≤ c * (n' : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
    rw [hc V h hs hp rfl M₀ hM₀]
    exact mul_le_mul_of_nonneg_left (GlobalTheory.T.maximalLatticeLocalFactorProduct_pos_and_le K V h hK hs hnd hj M₀ hM₀).2 hcpos.le
  have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
    intro g M hM
    have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M (mem_genus_self h M hM.1.1)
    have h2 := (hdisc M hM.1).2.2.2.1 _ h1
    exact ⟨h2.1, h2.2.trans hM.2⟩
  let X : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
    {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
  have hXst : Stable (isom h) X := by
    rintro g p ⟨h1, h2, h3⟩
    exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
  have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
    (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
  have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
    (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
  obtain ⟨mono, hconst, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) X := by
    rw [f1]
    refine mono _ _ _ _ subset_rfl fun M hM => ?_
    obtain ⟨M', hM', hle⟩ := hex M hM.1
    have hne : (X ∩ Prod.fst ⁻¹' {M}).Nonempty :=
      ⟨(M, M'), ⟨hM, (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
    have := Set.one_le_encard_iff_nonempty.2 hne
    exact_mod_cast this
  have s2 : orbMass (isom h) X ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) +
      Real.logb 2 (Module.finrank ℚ K))) * orbMass (isom h) (genus h M₀) := by
    rw [f2, ← hconst]
    refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
    refine le_trans ?_ (GlobalTheory.T.encard_sublattices_of_index_le K V h hK hs hnd M' hM'.1.toIsLattice i (Nat.one_le_iff_ne_zero.2 hi0))
    have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
    have : (X ∩ Prod.snd ⁻¹' {M'}).encard ≤
        {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N = i}.encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        refine ⟨h3, ?_⟩
        have h5 := ((hdisc N h1.1).2.2.1 N' hM''.1 h3).2
        rw [h1.2, hM''.2, hnn] at h5
        have h6 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn'0) h5
        exact ((Nat.pow_left_injective (by norm_num)) h6).symm
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine s1.trans (s2.trans ?_)
  rw [← hmass, ← ENNReal.ofReal_mul (by positivity), hcI, hnn]
  refine ENNReal.ofReal_le_ofReal (real_bound n' i _ _ c _ (Nat.one_le_iff_ne_zero.2 hn'0) ?_ hcpos.le hm₀)
  refine Real.logb_nonneg (by norm_num) ?_
  exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)

end GlobalTheory.Mass.SpaceMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLeStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_integralLattices_discriminantOrder_le : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ n : ℕ, 1 ≤ n → orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h' I * (n : ℝ) ^ (((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  first | exact @GlobalTheory.Mass.SpaceMass.main | exact GlobalTheory.Mass.SpaceMass.main | (intros; apply GlobalTheory.Mass.SpaceMass.main <;> assumption)
end
