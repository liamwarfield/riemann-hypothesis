module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormExistsConjNearReference
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesDefiniteQuotientNormalFormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesDefiniteQuotientNormalFormLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem count_index_fg {K Q : Type} [Field K] [NumberField K] [AddCommGroup Q] [Module K Q]
    [Module (𝓞 K) Q] [IsScalarTower (𝓞 K) K Q] [FiniteDimensional K Q] (M : Submodule (𝓞 K) Q) (hM : M.FG)
    (S : Submodule K Q) (hS : M ≤ S.restrictScalars (𝓞 K)) (k : ℕ) (hk : Module.finrank K S ≤ k)
    (x : ℕ) (hx : 1 ≤ x) :
    {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.Finite ∧
      (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤ (x : ℝ) ^ ((k : ℝ) + cf K) := by
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) Q := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K Q
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  obtain ⟨h1, h2⟩ := Formalism.SLP.Final.submoduleIndexCountO K M x hx
  refine ⟨h1, ?_⟩
  have hr : Module.finrank (𝓞 K) M ≤ k := by
    refine le_trans ?_ hk
    apply Module.finrank_le_of_rank_le
    have h3 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) S := Submodule.rank_mono hS
    have h5 : Module.rank K S = Module.rank (𝓞 K) S := IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl
    rw [Module.finrank_eq_rank, h5]
    exact h3
  have hn : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have h4 := Formalism.SLP.Final.omegaPow (Module.finrank ℚ K) x hn hx
  have h3 : (({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
      ((Module.finrank ℚ K : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length *
        (x : ℝ) ^ Module.finrank (𝓞 K) M := by exact_mod_cast h2
  have hr' : (Module.finrank (𝓞 K) M : ℝ) ≤ k := by exact_mod_cast hr
  calc _ ≤ _ := h3
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ Module.finrank (𝓞 K) M :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (x : ℝ) ^ ((Module.finrank (𝓞 K) M : ℝ) + Real.logb 2 (Module.finrank ℚ K)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by unfold cf; linarith)

theorem count_index_latMod {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (W I : Submodule K V)
    (La : Submodule (𝓞 K) V) (h : IsLatMod La (W ⊔ I) I) (x : ℕ) (hx : 1 ≤ x) :
    ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}).encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((x : ℝ) ^ ((Module.finrank K W : ℝ) + cf K)) := by
  obtain ⟨⟨N, hN, hLa⟩, hsp⟩ := h
  let q : V →ₗ[𝓞 K] (V ⧸ I) := I.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker q = rs (𝓞 K) I := by
    ext v; simp [q]
  have hM : (La.map q).FG := by
    have : (rs (𝓞 K) I).map q = ⊥ := by
      rw [← hker]; exact LinearMap.le_ker_iff_map.1 le_rfl
    rw [hLa, Submodule.map_sup, this, sup_bot_eq]
    exact hN.map q
  have hS : La.map q ≤ (W.map I.mkQ).restrictScalars (𝓞 K) := by
    rintro _ ⟨v, hv, rfl⟩
    have : v ∈ W ⊔ I := hsp ▸ Submodule.subset_span hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 this
    refine ⟨w, hw, ?_⟩
    have : I.mkQ u = 0 := by simpa using hu
    change I.mkQ w = I.mkQ (w + u)
    rw [map_add (f := _), this, add_zero]
  obtain ⟨h1, h2⟩ := count_index_fg (La.map q) hM (W.map I.mkQ) hS _ (Submodule.finrank_map_le _ _) x hx
  have hle : {Th : Submodule (𝓞 K) V | rs (𝓞 K) I ≤ Th ∧ Th ≤ La ∧ idx La Th = x}.encard ≤
      {N : Submodule (𝓞 K) (La.map q) | N.toAddSubgroup.index = x}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun Th => (Th.map q).comap (La.map q).subtype) ?_ ?_
    · rintro Th ⟨hI, hL, hi⟩
      have e : (Th.map q).comap q = Th := Submodule.comap_map_eq_self (hker ▸ hI)
      have e2 : idx La ((Th.map q).comap q) = idx (La.map q) (Th.map q) :=
        AddSubgroup.relIndex_comap (Th.map q).toAddSubgroup q.toAddMonoidHom La.toAddSubgroup
      rw [e, hi] at e2
      exact e2.symm
    · rintro Th ⟨hI, hL, -⟩ Th' ⟨hI', hL', -⟩ he
      have he2 : Th.map q = Th'.map q := by
        have := congrArg (Submodule.map (La.map q).subtype) he
        simp only [Submodule.map_comap_subtype] at this
        rwa [inf_eq_right.2 (Submodule.map_mono hL), inf_eq_right.2 (Submodule.map_mono hL')] at this
      rw [← Submodule.comap_map_eq_self (f := q) (p := Th) (hker ▸ hI), he2,
        Submodule.comap_map_eq_self (hker ▸ hI')]
  refine le_trans (ENat.toENNReal_le.2 hle) ?_
  rw [← h1.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h2

theorem count_sublattices_definite : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (La : Submodule (𝓞 K) V) (i : ℕ), 1 ≤ i → IsLatMod La (wSp N.F N.F') (II N.F N.F') → ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ La ∧ idx La Th = i}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K N.Wt : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N La i hi h
  have hw := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).2.2.2.2.2.2.1
  rw [hw] at h
  exact count_index_latMod N.Wt _ La h i hi

end GlobalTheory.DegCnt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesDefiniteQuotientNormalFormLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_sublattices_definiteQuotient_normalForm_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (La : Submodule (𝓞 K) V) (i : ℕ), 1 ≤ i → IsLatMod La (wSp N.F N.F') (II N.F N.F') → ((({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ La ∧ idx La Th = i}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K N.Wt : ℝ) + cf K)) := by
  first | exact @GlobalTheory.DegCnt.count_sublattices_definite | exact GlobalTheory.DegCnt.count_sublattices_definite | (intros; apply GlobalTheory.DegCnt.count_sublattices_definite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUnimodularHermGluingsLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUnimodularHermGluingsLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Glue

open TensorProduct

theorem finrank_baseChange_field (R M F : Type) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] [Field F] [Algebra R F] :
    Module.finrank F (F ⊗[R] M) = Module.finrank R M := by
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := F) ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
  exact h1

theorem exists_gens (R M : Type) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ t : Fin (Module.finrank R M) → M, ∀ N : Submodule R M, (∀ i, t i ∈ N) → I • (⊤ : Submodule R M) ≤ N →
      N = ⊤ := by
  have : Finite (MaximalSpectrum (R ⧸ I)) := inferInstance
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] M) (Module.finrank R M) (by
    intro P
    have := P.isMaximal
    let _ := Ideal.Quotient.field P.asIdeal
    rw [(AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) M).finrank_eq]
    exact finrank_baseChange_field R M _)
  have hs : Function.Surjective (TensorProduct.mk R (R ⧸ I) M 1) :=
    TensorProduct.mk_surjective R M (R ⧸ I) Ideal.Quotient.mk_surjective
  choose t ht using fun i => hs (b i)
  refine ⟨t, fun N hN hI => eq_top_iff.2 fun m _ => ?_⟩
  choose a ha using fun i => Ideal.Quotient.mk_surjective (b.repr (TensorProduct.mk R (R ⧸ I) M 1 m) i)
  have h0 : TensorProduct.mk R (R ⧸ I) M 1 (m - ∑ i, a i • t i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr (TensorProduct.mk R (R ⧸ I) M 1 m)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ht, ← ha, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have h1 : m - ∑ i, a i • t i ∈ I • (⊤ : Submodule R M) := by
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul M I) h0
    rw [map_zero] at this
    rw [← Submodule.Quotient.mk_eq_zero, ← this]
    simp
  have h2 := N.add_mem (hI h1) (N.sum_mem (t := Finset.univ) fun i _ => N.smul_mem (a i) (hN i))
  simpa using h2

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in
theorem finrank_le {D : Submodule (𝓞 K) V} {W : Submodule K V} (h : D ≤ rs (𝓞 K) W) :
    Module.finrank (𝓞 K) D ≤ Module.finrank K W := by
  let f : D →ₗ[𝓞 K] W := { toFun := fun d => ⟨d, h d.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b e => Subtype.ext (congrArg (fun z : W => (z : V)) e)
  have h1 := LinearMap.rank_le_of_injective f hf
  rw [← IsLocalization.rank_eq (N := W) K (nonZeroDivisors (𝓞 K)) le_rfl] at h1
  exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K W)

omit [StarRing K] [FiniteDimensional K V] in
theorem span_inf {L : Submodule (𝓞 K) V} (hL : Submodule.span K (L : Set V) = ⊤) (S : Submodule K V) :
    Submodule.span K ((L ⊓ rs (𝓞 K) S : Submodule (𝓞 K) V) : Set V) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun x hx => hx.2
  · intro v hv
    have hvL : v ∈ Submodule.span K (L : Set V) := by rw [hL]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (𝓞 K)) K (L : Set V) v hvL
    rw [Submodule.span_eq] at hs
    have hc := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) s.2
    rw [← Submodule.smul_mem_iff _ hc]
    refine Submodule.subset_span ⟨?_, S.smul_mem _ hv⟩
    rw [algebraMap_smul]
    exact hs

omit [StarRing K] [FiniteDimensional K V] in
theorem flat_of_submodule (D : Submodule (𝓞 K) V) : Module.Flat (𝓞 K) D := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro q ⟨a, ha⟩
  have h1 : (algebraMap (𝓞 K) K a) • (q : V) = 0 := by
    rw [algebraMap_smul]; exact congrArg Subtype.val ha
  have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
  rw [Submodule.mem_bot]
  exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left h3)

section Proj

variable (H : HermSpace K V) {U : Submodule K V} (hc : IsCompl U (perp H U)) {L : Submodule (𝓞 K) V}
  (hU : IsUnimod H L) {p : V →ₗ[K] V} (hp : ∀ v, p v ∈ U) (hq : ∀ v, v - p v ∈ perp H U)

omit [NumberField K] [FiniteDimensional K V] in
include hU in
theorem integral {y x : V} (hy : y ∈ L) (hx : x ∈ L) : H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← hU.2, mem_dual_iff] at hy
  exact hy.2 x hx


omit [FiniteDimensional K V] in
include hU hp hq in
theorem proj_mem_dual {v : V} (hv : v ∈ L) : p v ∈ dual H (L ⊓ rs (𝓞 K) U) := by
  rw [mem_dual_iff, span_inf ((isLatMod_top_bot_iff L).1 hU.1).2]
  refine ⟨hp v, fun a ha => ?_⟩
  have h0 := (mem_perp_iff H U _).1 (hq v) a ha.2
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h0
  rw [← h0]
  exact integral H hU hv ha.1


include hc hU hp hq in
theorem mem_dual_iff_proj (d : V) : d ∈ dual H (L ⊓ rs (𝓞 K) (perp H U)) ↔ ∃ v ∈ L, v - p v = d := by
  have hsp := span_inf ((isLatMod_top_bot_iff L).1 hU.1).2 (perp H U)
  have h0 : ∀ v, ∀ b ∈ perp H U, H.B b (p v) = 0 := fun v b hb => (mem_perp_iff H U _).1 hb _ (hp v)
  rw [mem_dual_iff, hsp]
  constructor
  · rintro ⟨hy, hyM⟩
    have hx : ∀ x : ↥(L ⊓ rs (𝓞 K) (perp H U)), IsIntegral ℤ (H.B x d) := by
      intro x
      rw [← GlobalTheory.UnimodQuot.mem_one_iff, ← H.herm]
      exact GlobalTheory.UnimodQuot.star_mem_one (hyM x x.2)
    let φ : ↥(L ⊓ rs (𝓞 K) (perp H U)) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x d, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) d = H.B a d + H.B b d
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) d = algebraMap (𝓞 K) K a * H.B b d
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨v, hv, h'⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU (perp H U) φ
    refine ⟨v, hv, sub_eq_zero.1 ?_⟩
    have h1 : v - p v - d ∈ U := by
      apply GlobalTheory.UnimodQuot.mem_of_perp_perp H U
      intro x hx
      rw [← hsp] at hx
      have : Submodule.span K ((L ⊓ rs (𝓞 K) (perp H U) : Submodule (𝓞 K) V) : Set V) ≤
          LinearMap.ker (H.B.flip (v - p v - d)) := by
        rw [Submodule.span_le]
        intro b hb
        have h2 : H.B b v = H.B b d := h' ⟨b, hb⟩
        show H.B b (v - p v - d) = 0
        rw [map_sub, map_sub, h0 v b hb.2, h2, sub_zero, sub_self]
      exact this hx
    exact (Submodule.disjoint_def.1 hc.disjoint) _ h1 ((perp H U).sub_mem (hq v) hy)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨hq v, fun b hb => ?_⟩
    have : H.B (p v) b = 0 := by rw [← H.herm, h0 v b hb.2, star_zero]
    rw [map_sub, LinearMap.sub_apply, this, sub_zero]
    exact integral H hU hv hb.1


include hc hU in
theorem idx_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    idx (dual H (L ⊓ rs (𝓞 K) U)) (L ⊓ rs (𝓞 K) U) ≠ 0 := by
  have hL := (isLatMod_top_bot_iff L).1 hU.1
  have hM : IsLatMod (L ⊓ rs (𝓞 K) U) U ⊥ := by
    refine ⟨⟨L ⊓ rs (𝓞 K) U, ?_, by simp⟩, span_inf hL.2 U⟩
    have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL.1
    have : IsNoetherian (𝓞 K) L := inferInstance
    have : IsNoetherian (𝓞 K) ↥(L ⊓ rs (𝓞 K) U) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  obtain ⟨h1, h2⟩ := (GlobalTheory.DegCnt.DelScale.main K V H hK _ _ U ⊥ bot_le (fun x hx =>
    ⟨fun h => (Submodule.disjoint_def.1 hc.disjoint) x hx ((mem_perp_iff H U x).2 h), by
      rintro rfl y _
      simp⟩) hM hM).2.2.2 ((isIntegralLat_iff H _).2 fun x hx y hy => integral H hU hx.1 hy.1)
  intro h
  rw [h] at h2
  have : (0 : ℝ) < del H (L ⊓ rs (𝓞 K) U) ^ 2 := by positivity
  rw [h2] at this
  simp at this

end Proj

theorem encard_gluings_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (U : Submodule K V) (A B : Submodule (𝓞 K) V) (x : ℕ), IsCompl U (perp H U) → idx (dual H A) A = x → ((({Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B}).encard : ℕ∞) : ℝ≥0∞) ≤ (x : ℝ≥0∞) ^ Module.finrank K (perp H U) := by
  intro K V _ _ _ _ _ _ _ _ H hK U A B x hc hx
  set S := {Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B} with hS
  rcases S.eq_empty_or_nonempty with h | ⟨L₀, hL₀, hA₀, hB₀⟩
  · rw [h]; simp
  obtain ⟨p, hp, hq⟩ : ∃ p : V →ₗ[K] V, (∀ v, p v ∈ U) ∧ ∀ v, v - p v ∈ perp H U :=
    ⟨U.projection _ hc, fun v => Submodule.projection_apply_mem hc v, fun v => Submodule.sub_projection_mem hc v⟩
  have hx0 : x ≠ 0 := by rw [← hx, ← hA₀]; exact idx_ne_zero H hc hL₀ hK
  have hpA : ∀ L ∈ S, ∀ v ∈ L, p v ∈ dual H A := fun L hL v hv => hL.2.1 ▸ proj_mem_dual H hL.1 hp hq hv
  have hD : ∀ L ∈ S, ∀ d, d ∈ dual H B ↔ ∃ v ∈ L, v - p v = d := fun L hL d =>
    hL.2.2 ▸ mem_dual_iff_proj H hc hL.1 hp hq d
  have hS₀ : L₀ ∈ S := ⟨hL₀, hA₀, hB₀⟩
  let q : V →ₗ[𝓞 K] V := (LinearMap.id - p).restrictScalars (𝓞 K)
  have hqv : ∀ v, q v = v - p v := fun _ => rfl
  have hfin : Module.Finite (𝓞 K) (dual H B) := by
    have e : dual H B = L₀.map q := by
      ext d; rw [hD L₀ hS₀]; rfl
    rw [e, Module.Finite.iff_fg]
    exact ((isLatMod_top_bot_iff L₀).1 hL₀.1).1.map _
  have hflat := flat_of_submodule (dual H B)
  have hI : Ideal.span {(x : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hx0
  have := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  obtain ⟨t, ht⟩ := exists_gens (𝓞 K) (dual H B) (Ideal.span {(x : 𝓞 K)})
  have hrk : Module.finrank (𝓞 K) (dual H B) ≤ Module.finrank K (perp H U) := by
    refine finrank_le fun d hd => ?_
    obtain ⟨v, -, rfl⟩ := (hD L₀ hS₀ d).1 hd
    exact hq v
  have hAL : ∀ L ∈ S, A ≤ L := fun L hL => hL.2.1 ▸ inf_le_left
  have hBL : ∀ L ∈ S, B ≤ L := fun L hL => hL.2.2 ▸ inf_le_left
  have hxB : ∀ d ∈ dual H B, (x : 𝓞 K) • d ∈ B := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := (hD L₀ hS₀ d).1 hd
    have h1 : x • p v ∈ A := by
      have := AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := (dual H A).toAddSubgroup) (hpA L₀ hS₀ v hv)
      rwa [show A.toAddSubgroup.relIndex (dual H A).toAddSubgroup = x from hx] at this
    rw [← hB₀]
    refine ⟨?_, (rs (𝓞 K) (perp H U)).smul_mem _ (hq v)⟩
    rw [Nat.cast_smul_eq_nsmul, smul_sub]
    exact L₀.sub_mem (nsmul_mem hv x) (hAL L₀ hS₀ h1)
  have hpB : ∀ b ∈ B, p b = 0 := by
    intro b hb
    rw [← hB₀] at hb
    refine (Submodule.disjoint_def.1 hc.disjoint) _ (hp b) ?_
    simpa using (perp H U).sub_mem hb.2 (hq b)
  choose w hw hw' using fun (L : S) i => (hD L L.2 (t i)).1 (t i).2
  let Q := (dual H A).toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf (dual H A).toAddSubgroup
  have hQ : Nat.card Q = x := hx
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hx0)
  let f : S → Fin (Module.finrank (𝓞 K) (dual H B)) → Q := fun L i =>
    QuotientAddGroup.mk ⟨p (w L i), hpA L L.2 _ (hw L i)⟩
  have key : ∀ L L' : S, f L = f L' → L.1 ≤ L'.1 := by
    intro L L' e v hv
    have h1 : ((L.1 ⊓ L'.1).map q).comap (dual H B).subtype = ⊤ := by
      refine ht _ (fun i => ⟨w L i, ⟨hw L i, ?_⟩, hw' L i⟩) ?_
      · have h2 : -p (w L i) + p (w L' i) ∈ A := QuotientAddGroup.eq.1 (congrFun e i)
        have h3 : w L i = w L' i - (-p (w L i) + p (w L' i)) := by
          have := (hw' L i).trans (hw' L' i).symm
          linear_combination (norm := module) this
        rw [h3]
        exact L'.1.sub_mem (hw L' i) (hAL L' L'.2 h2)
      · refine Submodule.smul_le.2 fun r hr d _ => ?_
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h2 : (c * x) • (d : V) ∈ B := by rw [mul_smul]; exact B.smul_mem _ (hxB d d.2)
        refine ⟨(c * x) • (d : V), ⟨hBL L L.2 h2, hBL L' L'.2 h2⟩, ?_⟩
        rw [hqv, hpB _ h2, sub_zero]; rfl
    have h2 : (⟨v - p v, (hD L L.2 _).2 ⟨v, hv, rfl⟩⟩ : dual H B) ∈
        ((L.1 ⊓ L'.1).map q).comap (dual H B).subtype := h1 ▸ Submodule.mem_top
    obtain ⟨u, ⟨hu, hu'⟩, e'⟩ := h2
    have e'' : u - p u = v - p v := e'
    have h3 : v - u ∈ A := by
      rw [← L.2.2.1]
      refine ⟨L.1.sub_mem hv hu, ?_⟩
      have : v - u = p v - p u := by linear_combination (norm := module) -e''
      rw [this]
      exact U.sub_mem (hp v) (hp u)
    simpa using L'.1.add_mem (hAL L' L'.2 h3) hu'
  have hf : Function.Injective f := fun L L' e => Subtype.ext (le_antisymm (key L L' e) (key L' L e.symm))
  have : Finite S := Finite.of_injective f hf
  have h1 : Nat.card S ≤ x ^ Module.finrank K (perp H U) := by
    refine (Nat.card_le_card_of_injective f hf).trans ?_
    rw [Nat.card_fun, hQ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hx0) hrk
  rw [← (Set.toFinite S).cast_ncard_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast h1

end GlobalTheory.DegCnt.Glue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUnimodularHermGluingsLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_unimodular_hermGluings_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (U : Submodule K V) (A B : Submodule (𝓞 K) V) (x : ℕ), IsCompl U (perp H U) → idx (dual H A) A = x → ((({Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B}).encard : ℕ∞) : ℝ≥0∞) ≤ (x : ℝ≥0∞) ^ Module.finrank K (perp H U) := by
  first | exact @GlobalTheory.DegCnt.Glue.encard_gluings_le | exact GlobalTheory.DegCnt.Glue.encard_gluings_le | (intros; apply GlobalTheory.DegCnt.Glue.encard_gluings_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardLatticesNearReferenceLatticeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardLatticesNearReferenceLatticeLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.NearCount

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem line_cyclic (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ u ∈ line (I : Submodule (𝓞 K) K) v,
      line (I : Submodule (𝓞 K) K) v ≤ n • line (I : Submodule (𝓞 K) K) v ⊔ Submodule.span (𝓞 K) {u} := by
  obtain ⟨a, J, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • v)
  have hφ : line (I : Submodule (𝓞 K) K) v = Submodule.map φ J := by
    ext x
    simp only [line, Submodule.mem_map, hI, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
      FractionalIdeal.mem_coeIdeal, φ, LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
  rw [hφ]
  by_cases hJ : J = ⊥
  · exact ⟨0, zero_mem _, by simp [hJ]⟩
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := n * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hn hJ)
  have hbJ : b ∈ J := by
    rw [← hb]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  refine ⟨φ b, Submodule.mem_map_of_mem hbJ, ?_⟩
  conv_lhs => rw [← hb]
  rw [Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'']
  refine sup_le_sup_left ?_ _
  rw [← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton]


omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem count_between (P : Submodule (𝓞 K) V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (e : ℕ) (v : Fin e → V)
    (hv : ∀ i, v i ∈ P) (hP : P ≤ n • P ⊔ Submodule.span (𝓞 K) (Set.range v)) :
    {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P}.encard ≤ ((Ideal.absNorm n ^ (e * e) : ℕ) : ℕ∞) := by
  let S : Submodule (𝓞 K) P := (n • P).comap P.subtype
  let w : Fin e → P ⧸ S := fun i => S.mkQ ⟨v i, hv i⟩
  have hS : ∀ a ∈ n, ∀ y : P ⧸ S, a • y = 0 := by
    intro a ha y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha x.2
  have hgen : ∀ y : P ⧸ S, ∃ c : Fin e → 𝓞 K, y = ∑ i, c i • w i := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hP x.2)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ht
    refine ⟨c, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [w, ← map_smul, ← map_sum]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((x - ∑ i, c i • (⟨v i, hv i⟩ : P) : P) : V) ∈ n • P
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← hst, add_sub_cancel_right]
    exact hs
  haveI : Finite (𝓞 K ⧸ n) := Ideal.finiteQuotientOfFreeOfNeBot n hn
  let f : (Fin e → 𝓞 K ⧸ n) → P ⧸ S := fun c => ∑ i, (c i).out • w i
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := hgen y
    refine ⟨fun i => Ideal.Quotient.mk n (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← sub_eq_zero, ← sub_smul]
    apply hS
    rw [← Ideal.Quotient.eq]
    exact Quotient.out_eq _
  haveI : Finite (P ⧸ S) := Finite.of_surjective f hf
  have hcard : Nat.card (P ⧸ S) ≤ Ideal.absNorm n ^ e := by
    refine (Nat.card_le_card_of_surjective f hf).trans (le_of_eq ?_)
    rw [Nat.card_fun, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp
  have hw : Submodule.span (𝓞 K) (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hgen y
    exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, rfl⟩
  have hc := Formalism.SLP.P.card_submodules_le_of_dedekind (𝓞 K) (P ⧸ S) e w hw
  haveI : Finite (Submodule (𝓞 K) (P ⧸ S)) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Set.InjOn (fun L : Submodule (𝓞 K) V => (L.comap P.subtype).map S.mkQ)
      {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P} := by
    have key : ∀ L : Submodule (𝓞 K) V, n • P ≤ L → L ≤ P →
        (((L.comap P.subtype).map S.mkQ).comap S.mkQ).map P.subtype = L := by
      intro L h1 h2
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono h1),
        Submodule.map_comap_subtype, inf_eq_right.2 h2]
    intro L hL L' hL' h
    rw [← key L hL.1 hL.2, ← key L' hL'.1 hL'.2]
    simp only at h
    rw [h]
  refine (Set.encard_le_encard_of_injOn (t := Set.univ) (Set.mapsTo_univ _ _) hinj).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.cast_le, pow_mul]
  exact hc.trans (Nat.pow_le_pow_left hcard e)

theorem smul_injective (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Function.Injective fun P : Submodule (𝓞 K) V => m • P := by
  obtain ⟨a, ham, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨J, hJ⟩ : m ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ham)
  have key : ∀ P Q : Submodule (𝓞 K) V, m • P = m • Q → P ≤ Q := by
    intro P Q h x hx
    have h2 : Ideal.span {a} • P = Ideal.span {a} • Q := by
      rw [hJ, mul_comm, Submodule.mul_smul, Submodule.mul_smul, h]
    have h3 : a • x ∈ Ideal.span {a} • Q := h2 ▸ Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨y, hy, hxy⟩ := h3
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    rw [← algebraMap_smul K a y, ← algebraMap_smul K a x] at hxy
    rwa [← smul_right_injective V ha' hxy]
  intro P Q h
  exact le_antisymm (key P Q h) (key Q P h.symm)

theorem exists_gens [StarRing K] {H : HermSpace K V} {r : ℕ} (N : NF H r) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ v : Fin (2 * r + 1) → V, (∀ i, v i ∈ N.P0) ∧ N.P0 ≤ n • N.P0 ⊔ Submodule.span (𝓞 K) (Set.range v) := by
  choose u hu hu' using fun (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) => line_cyclic I v n hn
  let d : FractionalIdeal (𝓞 K)⁰ K := N.𝔡
  let I : Option (Fin r ⊕ Fin r) → FractionalIdeal (𝓞 K)⁰ K := fun o => o.elim 1
    (Sum.elim (fun a => d ^ (-((r : ℤ) - a.val)))
      fun a => if a.val < N.j then d ^ (-((r : ℤ) - a.val)) else d ^ ((r : ℤ) - a.val))
  let x : Option (Fin r ⊕ Fin r) → V := fun o => o.elim N.F.z
    (Sum.elim (fun a => N.F.e a.castSucc) fun a => if a.val < N.j then N.F'.e a.castSucc else N.ist a)
  have hP : N.P0 = ⨆ o, line (I o : Submodule (𝓞 K) K) (x o) := by
    apply le_antisymm
    · refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a h => ?_)) ?_) (iSup₂_le fun a h => ?_)
      · exact le_iSup_of_le (some (Sum.inl a)) le_rfl
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
        rfl
      · refine le_iSup_of_le none (le_of_eq ?_)
        simp only [I, x, Option.elim, FractionalIdeal.coe_one]
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_neg (not_lt.2 h)]
        rfl
    · refine iSup_le ?_
      rintro (_ | a | a)
      · simp only [I, x, Option.elim, FractionalIdeal.coe_one]
        exact le_sup_of_le_left le_sup_right
      · refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left ?_))
        exact le_iSup_of_le a le_rfl
      · by_cases h : a.val < N.j
        · simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
          refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right ?_))
          exact le_iSup₂_of_le a h le_rfl
        · simp only [I, x, Option.elim, Sum.elim_inr, if_neg h]
          refine le_sup_of_le_right ?_
          exact le_iSup₂_of_le a (not_lt.1 h) le_rfl
  have hle : ∀ o, line (I o : Submodule (𝓞 K) K) (x o) ≤ N.P0 := fun o => by
    rw [hP]; exact le_iSup (fun o => line (I o : Submodule (𝓞 K) K) (x o)) o
  let σ : Fin (2 * r + 1) ≃ Option (Fin r ⊕ Fin r) := Fintype.equivOfCardEq (by simp; ring)
  refine ⟨fun i => u (I (σ i)) (x (σ i)), fun i => hle _ (hu _ _), ?_⟩
  conv_lhs => rw [hP]
  refine iSup_le fun o => (hu' _ _).trans (sup_le_sup (Submodule.smul_mono le_rfl (hle o)) ?_)
  exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨σ.symm o, by simp⟩)

end GlobalTheory.DegCnt.NearCount

theorem GlobalTheory.DegCnt.NearCount.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N m hm
  have hn : m * m ≠ ⊥ := mul_ne_zero hm hm
  obtain ⟨v, hv, hP⟩ := GlobalTheory.DegCnt.NearCount.exists_gens N (m * m) hn
  have h1 := GlobalTheory.DegCnt.NearCount.count_between N.P0 (m * m) hn _ v hv hP
  have h2 : ({P : Submodule (𝓞 K) V | m • N.P0 ≤ P ∧ m • P ≤ N.P0}).encard ≤
      {L : Submodule (𝓞 K) V | (m * m) • N.P0 ≤ L ∧ L ≤ N.P0}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun P => m • P) ?_
      (GlobalTheory.DegCnt.NearCount.smul_injective m hm).injOn
    rintro P ⟨h, h'⟩
    exact ⟨by rw [Submodule.mul_smul]; exact Submodule.smul_mono le_rfl h, h'⟩
  refine (ENat.toENNReal_le.2 (h2.trans h1)).trans (le_of_eq ?_)
  rw [map_mul, ← sq, ← pow_mul, ← sq]
  simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardLatticesNearReferenceLatticeLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_lattices_near_reference_lattice_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.NearCount.main | exact GlobalTheory.DegCnt.NearCount.main | (intros; apply GlobalTheory.DegCnt.NearCount.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.OmCount

theorem encard_le_of_fibres {α β : Type*} (S : Set α) (A : Set β) (f : α → β) (c : ℝ≥0∞)
    (hA : ∀ x ∈ S, f x ∈ A)
    (hc : ∀ x ∈ S, ((({y | y ∈ S ∧ f y = f x} : Set α).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((A.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun x : S => (⟨f x, hA x x.2⟩ : A))]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [ENNReal.tsum_set_one]
  rcases Set.eq_empty_or_nonempty ((fun x : S => (⟨f x, hA x x.2⟩ : A)) ⁻¹' {a}) with h | ⟨x, hx⟩
  · rw [h]; simp
  · refine le_trans (ENat.toENNReal_le.2 ?_) (hc x x.2)
    refine Set.encard_le_encard_of_injOn (f := Subtype.val) ?_ Subtype.val_injective.injOn
    intro y hy
    refine ⟨y.2, ?_⟩
    have h1 : (⟨f y, hA y y.2⟩ : A) = a := hy
    have h2 : (⟨f x, hA x x.2⟩ : A) = a := hx
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem tsum_orbits_le {G α : Type*} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞) (S : Set α)
    (B : ℝ≥0∞) (h : ∀ x, Q x → w x ≤ B ∧ ∃ s : G, s • x ∈ S) :
    (∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0) ≤
      ((S.encard : ℕ∞) : ℝ≥0∞) * B := by
  set T : Set (MulAction.orbitRel.Quotient G α) := {o | Q o.out} with hT
  have h1 : (∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0) ≤ ∑' _ : T, B := by
    rw [tsum_subtype T (fun _ => B)]
    refine ENNReal.tsum_le_tsum fun o => ?_
    by_cases ho : Q o.out
    · rw [if_pos ho, Set.indicator_of_mem (show o ∈ T from ho)]
      exact (h _ ho).1
    · rw [if_neg ho]; exact zero_le
  refine h1.trans ?_
  rw [ENNReal.tsum_set_const]
  gcongr
  have h2 : T ⊆ (fun x : α => (Quotient.mk (MulAction.orbitRel G α) x)) '' S := by
    intro o ho
    obtain ⟨s, hs⟩ := (h _ ho).2
    refine ⟨_, hs, ?_⟩
    conv_rhs => rw [← Quotient.out_eq o]
    exact Quotient.sound ⟨s, rfl⟩
  exact (Set.encard_le_encard h2).trans (Set.encard_image_le _ _)

section

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

theorem idx_dual_sup (H : HermSpace K V) (W I : Submodule K V) (A : Submodule R V) (hA : A ≤ rs R W)
    (hWI : W ⊓ I = ⊥) (h1 : ∀ x ∈ W ⊔ I, ∀ y ∈ I, H.B x y = 0) (h2 : ∀ x ∈ W ⊔ I, ∀ y ∈ I, H.B y x = 0)
    (hint : IsIntegralLat H A) :
    idx (dual H (A ⊔ rs R I)) (A ⊔ rs R I) = idx (dual H A) A := by
  have hsp : Submodule.span K (A : Set V) ≤ W := Submodule.span_le.2 hA
  have hdW : dual H A ≤ rs R W := fun y hy => hsp ((mem_dual_iff H A y).1 hy).1
  have hAd : A ≤ dual H A := fun y hy => (mem_dual_iff H A y).2
    ⟨Submodule.subset_span hy, fun x hx => (isIntegralLat_iff H A).1 hint y hy x hx⟩
  have hspan : Submodule.span K ((A ⊔ rs R I : Submodule R V) : Set V) = Submodule.span K (A : Set V) ⊔ I := by
    apply le_antisymm
    · rw [Submodule.span_le]
      have : A ⊔ rs R I ≤ rs R (Submodule.span K (A : Set V) ⊔ I) :=
        sup_le (fun x hx => Submodule.mem_sup_left (Submodule.subset_span hx))
          (fun x hx => Submodule.mem_sup_right hx)
      exact this
    · exact sup_le (Submodule.span_mono fun x hx => Submodule.mem_sup_left hx)
        (fun x hx => Submodule.subset_span (Submodule.mem_sup_right hx))
  have hd : dual H (A ⊔ rs R I) = dual H A ⊔ (A ⊔ rs R I) := by
    rw [← sup_assoc, sup_eq_left.2 hAd]
    apply le_antisymm
    · intro y hy
      obtain ⟨hy1, hy2⟩ := (mem_dual_iff H _ y).1 hy
      rw [hspan] at hy1
      obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hy1
      refine Submodule.add_mem_sup ((mem_dual_iff H A a).2 ⟨ha, fun x hx => ?_⟩) hi
      have := hy2 x (Submodule.mem_sup_left hx)
      rwa [map_add, LinearMap.add_apply, h2 x (Submodule.mem_sup_left (hA hx)) i hi, add_zero] at this
    · intro y hy
      obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨ha1, ha2⟩ := (mem_dual_iff H A a).1 ha
      refine (mem_dual_iff H _ _).2 ⟨?_, fun x hx => ?_⟩
      · rw [hspan]; exact Submodule.add_mem_sup ha1 hi
      · obtain ⟨a', ha', i', hi', rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add (f := _), h1 (a + i) (Submodule.add_mem_sup (hsp ha1) hi) i' hi', add_zero, map_add (f := _),
          LinearMap.add_apply, h2 a' (Submodule.mem_sup_left (hA ha')) i hi, add_zero]
        exact ha2 a' ha'
  have hinf : (A ⊔ rs R I) ⊓ dual H A = A := by
    rw [sup_inf_assoc_of_le _ hAd, sup_eq_left]
    intro x hx
    have : x ∈ W ⊓ I := ⟨hdW hx.2, hx.1⟩
    rw [hWI, Submodule.mem_bot] at this
    rw [this]; exact A.zero_mem
  unfold idx
  rw [hd, Submodule.sup_toAddSubgroup (dual H A), AddSubgroup.relIndex_sup_right,
    ← AddSubgroup.inf_relIndex_right]
  congr 1
  exact congrArg Submodule.toAddSubgroup hinf

end

theorem numeric (r k : ℕ) (i b c n Db Del NT x : ℝ) (hi : 0 < i) (hb : 0 ≤ b) (hn0 : 0 ≤ n) (hx0 : 0 ≤ x)
    (hDb : 1 ≤ Db) (hDel : 1 ≤ Del) (hNT : 1 ≤ NT) (hn : n ≤ (Db * NT) ^ 2) (hx : x ≤ (Del * NT) ^ 2) :
    i ^ ((k : ℝ) + c) * (n ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * x ^ (2 * r + 1) *
      (b ^ k * Del ^ r * n ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) ≤
    (i * b) ^ k * i ^ c * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3) := by
  set M := Db * Del * NT with hM
  have hM1 : Db * NT ≤ M := by rw [hM]; nlinarith [mul_nonneg (sub_nonneg.2 hDel) (mul_nonneg (zero_le_one.trans hDb) (zero_le_one.trans hNT))]
  have hM2 : Del * NT ≤ M := by rw [hM]; nlinarith [mul_nonneg (sub_nonneg.2 hDb) (mul_nonneg (zero_le_one.trans hDel) (zero_le_one.trans hNT))]
  have hM3 : Del ≤ M := le_trans (le_mul_of_one_le_right (by linarith) hNT) hM2
  have hM4 : 1 ≤ M := hDel.trans hM3
  have hn' : n ≤ M ^ 2 := hn.trans (by gcongr)
  have hx' : x ≤ M ^ 2 := hx.trans (by gcongr)
  have hic : 0 ≤ i ^ c := by positivity
  calc _ = (i * b) ^ k * i ^ c * ((n ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * x ^ (2 * r + 1) *
      Del ^ r * n ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) := by
        rw [Real.rpow_add hi, Real.rpow_natCast, mul_pow]; ring
    _ ≤ (i * b) ^ k * i ^ c * (((M ^ 2) ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * (M ^ 2) ^ (2 * r + 1) *
      M ^ r * (M ^ 2) ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) := by
        have : 0 ≤ Del := by linarith
        gcongr
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp only [← pow_mul, ← pow_add]
        refine pow_le_pow_right₀ hM4 ?_
        ring_nf
        nlinarith [Nat.zero_le r, Nat.zero_le (r ^ 2), Nat.zero_le (r ^ 3)]

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem om_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) {s : V ≃ₗ[K] V} (hs : s ∈ N.R) : N.om (s • Λ) = N.om Λ := by
  obtain ⟨-, hS, -, -⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ hg hΛ s hs
  obtain ⟨-, -, -, -, hnil⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  have hLat := ((isUnimod_iff H Λ).1 hΛ.1.1).1
  have hL : Submodule.IsFullLattice K Λ :=
    { Submodule.IsLattice.of_fg K hLat.1 with span_eq_top := hLat.2 }
  unfold NF.om NF.Gam
  rw [hS.1]
  let A := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ
  let B := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (s • Λ)
  let C := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (N.Ref (latL N.F N.F' Λ))
  have hB : Submodule.IsFullLattice K (s • Λ) := Unimod.isLattice_smul s hL
  have hab : A.relIndex B ≠ 0 := Unimod.relIndex_ne_zero N.R hL hB
  have hba : B.relIndex A ≠ 0 := Unimod.relIndex_ne_zero N.R hB hL
  have hd : GlobalTheory.HL.invVol A B = 1 := by
    have h := (Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ Λ hL hL).2 s hs
    simpa [A, B, GlobalTheory.HL.invVol] using h
  change GlobalTheory.HL.invVol C B = GlobalTheory.HL.invVol C A
  by_cases hca : C.relIndex A = 0
  · have hcb : C.relIndex B = 0 := by
      by_contra h
      exact (Subgroup.relIndex_ne_zero_trans h hba) hca
    simp [GlobalTheory.HL.invVol, hca, hcb]
  · by_cases hac : A.relIndex C = 0
    · have hbc : B.relIndex C = 0 := by
        by_contra h
        exact (Subgroup.relIndex_ne_zero_trans hab h) hac
      simp [GlobalTheory.HL.invVol, hac, hbc]
    · have hcb : C.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hca hab
      have hbc : B.relIndex C ≠ 0 := Subgroup.relIndex_ne_zero_trans hba hac
      have h := (GlobalTheory.HL.invVol_mul_pos_le_conj C A B hca hac hcb hbc).1
      simpa [hd] using h

theorem isLatMod_latLa (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) :
    IsLatMod (latLa N.F N.F' Λ (g : 𝓞 K)) (wSp N.F N.F') (II N.F N.F') := by
  obtain ⟨hTh, -, -, -, -, -, -, ⟨M, -, hM⟩, hsp⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  obtain ⟨⟨⟨⟨M', hM', hL⟩, -⟩, -⟩, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  have h0 : latLa N.F N.F' Λ (g : 𝓞 K) ≤ flagPairDefinitePartLattice N.F N.F' Λ := fun x hx => hx.1.2
  have hI : rs (𝓞 K) (II N.F N.F') ≤ latLa N.F N.F' Λ (g : 𝓞 K) := le_trans (by rw [hM]; exact le_sup_right) hTh
  refine ⟨⟨latLa N.F N.F' Λ (g : 𝓞 K) ⊓ M', ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · haveI : IsNoetherian (𝓞 K) M' := isNoetherian_of_fg_of_noetherian _ hM'
    exact isNoetherian_submodule.1 this _ inf_le_right
  · rw [inf_sup_assoc_of_le _ hI, ← hL]
    exact (inf_eq_left.2 (h0.trans inf_le_left)).symm
  · exact Submodule.span_le.2 fun x hx => (h0 hx).2
  · rw [← hsp]; exact Submodule.span_mono hTh

theorem inf_Wt_of_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {Λ : Submodule (𝓞 K) V} (h : N.Split Λ) :
    Λ ⊓ rs (𝓞 K) N.Wt = latTh N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt := by
  obtain ⟨-, hlift, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  rw [h, sup_inf_assoc_of_le _ inf_le_right, eq_comm, sup_eq_left]
  intro x hx
  have : x ∈ N.Wt ⊓ II N.F N.F' := ⟨hx.2, hx.1⟩
  rw [hlift.2.1, Submodule.mem_bot] at this
  rw [this]; exact Submodule.zero_mem _

theorem idx_dual_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) (h : N.Split Λ) :
    (idx (dual H (Λ ⊓ rs (𝓞 K) N.Wt)) (Λ ⊓ rs (𝓞 K) N.Wt) : ℝ) ≤ (N.Del * N.NT) ^ 2 := by
  obtain ⟨-, hlift, -, -, -, -, hw, -, hPD, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, hgi, -, hdel, hlat⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hΛ
  have h1 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B x y = 0 := by
    intro x hx y hy
    rw [← hw] at hx
    exact (mem_perp_iff H _ x).1 hx y (Submodule.mem_sup_left (Submodule.mem_sup_left hy.1))
  have h2 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B y x = 0 := by
    intro x hx y hy
    rw [← H.herm, h1 x hx y hy, star_zero]
  have hintΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx y hy
    have hu : dual H Λ = Λ := hΛ.1.1.2
    rw [← hu] at hx
    exact ((mem_dual_iff H Λ x).1 hx).2 y hy
  have hintA : IsIntegralLat H (Λ ⊓ rs (𝓞 K) N.Wt) :=
    (isIntegralLat_iff H _).2 fun x hx y hy => hintΛ x hx.1 y hy.1
  have hintT : IsIntegralLat H (latTh N.F N.F' Λ) := by
    rw [h]
    refine (isIntegralLat_iff H _).2 fun x hx y hy => ?_
    obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a', ha', i', hi', rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _), h1 (a + i) (Submodule.add_mem_sup ha.2 hi) i' hi', add_zero, map_add (f := _),
      LinearMap.add_apply, h2 a' (Submodule.mem_sup_left ha'.2) i hi, add_zero]
    exact hintΛ a ha.1 a' ha'.1
  have hrad : ∀ x ∈ wSp N.F N.F', (∀ y ∈ wSp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
    rw [hw]
    intro x hx
    refine ⟨fun hx0 => ?_, fun hxI y hy => h2 y hy x hxI⟩
    obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    have haa := hx0 a (Submodule.mem_sup_left ha)
    rw [map_add (f := _), LinearMap.add_apply, h2 a (Submodule.mem_sup_left ha) i hi, add_zero] at haa
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have ha0 : a = 0 := by
      by_contra hne
      have := hPD τ ⟨a, ha⟩ (fun h => hne (congrArg Subtype.val h))
      have e : GlobalTheory.Mass.hRes H.B.flip N.Wt ⟨a, ha⟩ ⟨a, ha⟩ = H.B a a := rfl
      rw [e, haa] at this
      simp at this
    rw [ha0, zero_add]; exact hi
  have hd := (DelScale.main K V H hK _ _ _ _ (by rw [hw]; exact le_sup_right) hrad hlat hlat).2.2.2 hintT
  rw [← idx_dual_sup H N.Wt (II N.F N.F') _ inf_le_right hlift.2.1 h1 h2 hintA, ← h, ← hd.2, hdel]
  have : 0 ≤ N.NT := by unfold NF.NT; positivity
  gcongr

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ i b : ℕ, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤ ENNReal.ofReal (((i : ℝ) * b) ^ Module.finrank K N.Wt * (i : ℝ) ^ cf K * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ i b
  obtain ⟨𝔠, hcn, hDb, hDel, hQ⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors K V H hK r N g Λ hg hΛ
  refine hQ _ fun c0 c1 c2 c3 => ?_
  obtain ⟨-, -, hcompl, hrk, -, -, -, -, -, hT, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hrkPi : Module.finrank K (perp H N.Wt) = 2 * r + 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    unfold NF.Pi at this
    omega
  have hNT : 1 ≤ N.NT := one_le_pow₀ (by exact_mod_cast hT)
  set S : Set (Submodule (𝓞 K) V) := {Λ' | (N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ∧
    N.Split Λ' ∧ N.Near (𝔠 ^ (12 * r + 50)) Λ'} with hS
  set B : ℝ := (b : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r *
    (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2) with hB
  have hQs : ∀ Λ', (N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) → ∀ s ∈ N.R,
      (N.IsTerm g (s • Λ') ∧ N.SameDat g Λ (s • Λ') ∧ N.iI g (s • Λ') = i ∧ N.bI (s • Λ') = b) := by
    rintro Λ' ⟨h1, h2, h3, h4⟩ s hs
    obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.T.commonUnipotent_stabiliser_preserves_terms_and_datum K V H hK r N g Λ' hg h1 s hs
    refine ⟨k1, ⟨k2.1.trans h2.1, k2.2.1.trans h2.2.1, k2.2.2.trans h2.2.2⟩, ?_, k4.trans h4⟩
    rw [← h3]
    unfold NF.iI latLa
    rw [k3, k2.2.2]
  have step1 : N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤
      ((S.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal B := by
    refine tsum_orbits_le (G := N.R)
      (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) (fun Λ' => ENNReal.ofReal (N.om Λ')) S _ ?_
    intro Λ' h
    obtain ⟨s, hs, hsp⟩ := GlobalTheory.T.hermFramePair_exists_unipotent_split_lattice K V H hK r N g Λ' hg h.1
    have h' := hQs Λ' h s hs
    obtain ⟨t, ht, hsp', hnear⟩ := GlobalTheory.T.hermFramePairNormalForm_exists_conj_near_reference K V H hK r N g _ hg h'.1 𝔠 c0 c1 c2 c3 hsp
    have h'' := hQs _ h' t ht.1
    refine ⟨ENNReal.ofReal_le_ofReal ?_, ⟨t, ht.1⟩ * ⟨s, hs⟩, ?_⟩
    · rw [← om_smul hK N hg h.1 hs, ← om_smul hK N hg h'.1 ht.1, hB, ← h''.2.2.2]
      exact GlobalTheory.T.splitTermWeight_le_near_referenceLattice K V H hK r N g _ hg h''.1 𝔠 c0 c1 c2 c3 _ hsp' hnear
    · rw [mul_smul]
      exact ⟨h'', hsp', hnear⟩
  refine step1.trans ?_
  rcases Set.eq_empty_or_nonempty S with hE | ⟨Λ₀, hΛ₀⟩
  · rw [hE]; simp
  have hi : 1 ≤ i := by
    rw [← hΛ₀.1.2.2.1]
    exact (GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ₀ hg hΛ₀.1.1).2.2.1
  have hTh := GlobalTheory.T.card_sublattices_definiteQuotient_normalForm_le K V H hK r N _ i hi (isLatMod_latLa hK N hg hΛ)
  have hP := GlobalTheory.T.encard_lattices_near_reference_lattice_le K V H hK r N (𝔠 ^ (12 * r + 50)) (pow_ne_zero _ c0)
  have step2 := encard_le_of_fibres S
    ({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧
        idx (latLa N.F N.F' Λ (g : 𝓞 K)) Th = i} ×ˢ
      {P : Submodule (𝓞 K) V | 𝔠 ^ (12 * r + 50) • N.P0 ≤ P ∧ 𝔠 ^ (12 * r + 50) • P ≤ N.P0})
    (fun Λ' => (latTh N.F N.F' Λ', Λ' ⊓ rs (𝓞 K) N.Pi))
    (ENNReal.ofReal (((N.Del * N.NT) ^ 2) ^ (2 * r + 1))) ?_ ?_
  rotate_left
  · rintro Λ' ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    have e : latLa N.F N.F' Λ' (g : 𝓞 K) = latLa N.F N.F' Λ (g : 𝓞 K) := by
      unfold latLa; rw [h2.2.2]
    refine ⟨⟨?_, ?_, ?_⟩, h6⟩
    · show _ ≤ latTh N.F N.F' Λ'
      rw [h5]; exact le_sup_right
    · rw [← e]; exact (GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ' hg h1).1
    · rw [← e]; exact h3
  · rintro Λ' ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    have hgl := GlobalTheory.T.encard_unimodular_hermGluings_le K V H hK N.Wt (Λ' ⊓ rs (𝓞 K) N.Wt) (Λ' ⊓ rs (𝓞 K) N.Pi) _ hcompl rfl
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) (hgl.trans ?_)
    · rintro Λ'' ⟨⟨⟨k1, -⟩, k5, -⟩, k⟩
      refine ⟨k1.1.1, ?_, (Prod.ext_iff.1 k).2⟩
      rw [inf_Wt_of_split hK N k5, inf_Wt_of_split hK N h5]
      exact congrArg (· ⊓ rs (𝓞 K) N.Wt) (Prod.ext_iff.1 k).1
    · rw [hrkPi, ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast]
      gcongr
      exact idx_dual_le hK N hg h1 h5
  rw [Set.encard_prod, ENat.toENNReal_mul] at step2
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hDel0 : 0 ≤ N.Del := by linarith
  have hP' : (Ideal.absNorm (𝔠 ^ (12 * r + 50)) : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) =
      ENNReal.ofReal (((Ideal.absNorm 𝔠 : ℝ) ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2)) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, map_pow,
      Nat.cast_pow]
  rw [hP'] at hP
  refine le_trans (mul_le_mul_left (step2.trans (mul_le_mul_left (mul_le_mul' hTh hP) _)) _) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (numeric r _ i b (cf K) _ N.Db N.Del N.NT _ hipos (by positivity) (by positivity)
    (by positivity) hDb hDel hNT hcn le_rfl)

end GlobalTheory.DegCnt.OmCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLeStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePair_omSum_same_datum_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ i b : ℕ, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤ ENNReal.ofReal (((i : ℝ) * b) ^ Module.finrank K N.Wt * (i : ℝ) ^ cf K * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  first | exact @GlobalTheory.DegCnt.OmCount.main | exact GlobalTheory.DegCnt.OmCount.main | (intros; apply GlobalTheory.DegCnt.OmCount.main <;> assumption)
end
