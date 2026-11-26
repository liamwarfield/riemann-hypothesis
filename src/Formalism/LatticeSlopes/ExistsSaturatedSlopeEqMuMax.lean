module

public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume

@[expose] public section

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
open Module Submodule

noncomputable section

namespace Formalism.F

universe u

private theorem finrank_int_eq_finrank_span_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (span ℝ (L : Set E)) := by

  let V := span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L' ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : L' => (⟨((x : V) : E), x.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ L')

theorem linearIndependent_coe_basis' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR, ← finrank_int_eq_finrank_span_real L,
    Module.finrank_eq_card_basis e]

theorem gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem slopesBdd_of (hG : GramDetLe.{u, 0, 0}) : SlopesBdd.{u} := by
  intro E _ _ _ L hL
  haveI := hL
  let e := Module.finBasis ℤ L
  have he : LinearIndependent ℝ (fun i => (e i : E)) := linearIndependent_coe_basis' L e

  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, WithLp.ofLp x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h0 := Fintype.linearIndependent_iff.mp he (fun i => WithLp.ofLp x i) hx
    have h1 : WithLp.ofLp x = 0 := funext h0
    simpa using congrArg (WithLp.toLp 2) h1
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := by
    intro j
    rw [hfj j]
    simp [S, w]
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := by
    intro c
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hSw]
    rw [← h1]
    simpa [dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N))
    (fun j => (f j : E)) w K hcomp
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin] at hdet

  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h2 : ∑ j, c j • (f j : E) = 0 := by
      rw [← map_zero S, ← hc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hSw]
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis' N f) c h2
  have hwpos : 0 < (Matrix.gram ℝ w).det := (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det] at hwpos
  have hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det := by
    simp only [eq_intCast] at hwpos ⊢
    have : (0 : ℤ) < (M.transpose * M).det := by exact_mod_cast hwpos
    exact_mod_cast this
  have hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ) := by
    haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
    exact_mod_cast Module.finrank_pos
  set g := (Matrix.gram ℝ (fun j => (f j : E))).det with hg
  have hgK : 1 ≤ (K : ℝ) ^ (2 * Module.finrank ℤ N) * g := hd1.trans hdet
  have hgpos : 0 < g := by
    by_contra hneg
    push_neg at hneg
    have : (K : ℝ) ^ (2 * Module.finrank ℤ N) * g ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hlog : -(2 * (Module.finrank ℤ N : ℝ)) * Real.log K ≤ Real.log g := by
    have h1 : Real.log 1 ≤ Real.log ((K : ℝ) ^ (2 * Module.finrank ℤ N) * g) :=
      Real.log_le_log one_pos hgK
    rw [Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hcov : covol N = Real.sqrt g := by rw [covol, dite_eq_left hN]
  show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K
  rw [hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]
  nlinarith

end Formalism.F
end
end

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
namespace Formalism.F

universe u

theorem slopeLeMuMax_of (h : SlopesBdd.{u}) : SlopeLeMuMax.{u} := by
  intro E _ _ _ L N hL hNL hN
  exact le_csSup (h E L hL) (show slope N ∈ slopes L from ⟨N, hNL, hN, rfl⟩)

theorem muMaxMono_of (h : SlopesBdd.{u}) : MuMaxMono.{u} := by
  intro E _ _ _ L N hL hNL hN
  apply csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)
  rintro t ⟨M, hMN, hM, rfl⟩
  exact ⟨M, hMN.trans hNL, hM, rfl⟩

end Formalism.F
end

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated
open Module Submodule

noncomputable section

namespace Formalism.F

universe u

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem finite_mem_norm_le (L : Submodule ℤ E) [hL : DiscreteTopology L] (C : ℝ) :
    {v : E | v ∈ L ∧ ‖v‖ ≤ C}.Finite := by
  have hD : DiscreteTopology (L.toAddSubgroup) := hL
  have hcl : IsClosed (L : Set E) := (L.toAddSubgroup).isClosed_of_discreteTopology
  have hs : IsDiscrete (L : Set E) := isDiscrete_iff_discreteTopology.mpr hL
  refine (Metric.finite_isBounded_inter_isClosed hs (Metric.isBounded_closedBall (x := (0 : E)) (r := C))
    hcl).subset ?_
  intro v hv
  exact ⟨mem_closedBall_zero_iff.mpr hv.2, hv.1⟩

theorem sub_mem_of_starProjection_eq (W : Submodule ℝ E) {x z : E}
    (h : Wᗮ.starProjection x = Wᗮ.starProjection z) : x - z ∈ W := by
  have h0 : Wᗮ.starProjection (x - z) = 0 := by rw [map_sub, h, sub_self]
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h0
  exact h0

theorem mem_of_starProjection_mem_span_orthQuotient {L M N₁ : Submodule ℤ E} (hM : IsSaturated L M) (h1 : N₁ ≤ M)
    {x : E} (hx : x ∈ L)
    (hπ : (span ℝ (N₁ : Set E))ᗮ.starProjection x ∈ span ℝ (quot M N₁ : Set E)) : x ∈ M := by
  unfold quot at hπ
  rw [Submodule.map_coe] at hπ
  have hfun : ⇑(LinearMap.restrictScalars ℤ
      (((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E)) =
      ⇑(((span ℝ (N₁ : Set E))ᗮ.starProjection : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
  rw [hfun, Submodule.span_image, Submodule.mem_map] at hπ
  obtain ⟨y, hy, hyx⟩ := hπ
  have hxy : x - y ∈ span ℝ (N₁ : Set E) := sub_mem_of_starProjection_eq _ hyx.symm
  have hle : span ℝ (N₁ : Set E) ≤ span ℝ (M : Set E) := span_mono h1
  refine hM.2 x hx ?_
  have := add_mem (hle hxy) hy
  rwa [sub_add_cancel] at this

end

private theorem rk_pos_of_ne_zero_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (N : Submodule ℤ E) [DiscreteTopology N]
    {v : E} (hv : v ∈ N) (hv0 : v ≠ 0) : 0 < rk N := by
  unfold rk
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, by simpa using hv0⟩

theorem finite_saturated_rank_le_covol_le (hS : ShortVector.{u}) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (k : ℕ) :
    ∀ (L : Submodule ℤ E), DiscreteTopology L → ∀ X : ℝ,
      {N : Submodule ℤ E | IsSaturated L N ∧ rk N ≤ k ∧ covol N ≤ X}.Finite := by
  induction k with
  | zero =>
    intro L hL X
    refine (Set.finite_singleton (⊥ : Submodule ℤ E)).subset ?_
    rintro N ⟨hN, hrk, -⟩
    haveI : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hN.1
    rw [Set.mem_singleton_iff]
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    have := rk_pos_of_ne_zero_mem N hv hv0
    omega
  | succ k ih =>
    intro L hL X
    have hdisc : ∀ N : Submodule ℤ E, N ≤ L → DiscreteTopology N :=
      fun N h => DiscreteTopology.of_subset (s := (L : Set E)) hL h
    have hB : {v : E | v ∈ L ∧ ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X ∧ v ≠ 0}.Finite :=
      (finite_mem_norm_le L _).subset fun v hv => ⟨hv.1, hv.2.1⟩
    refine ((Set.finite_singleton ⊥).union (hB.biUnion (t := fun v =>
      {N : Submodule ℤ E | IsSaturated L N ∧ rk N ≤ k + 1 ∧ covol N ≤ X ∧
        satur L (span ℤ ({v} : Set E)) ≤ N}) fun v hv => ?_)).subset ?_
    ·
      obtain ⟨hvL, -, hv0⟩ := hv
      have hspL : span ℤ ({v} : Set E) ≤ L := span_le.mpr (Set.singleton_subset_iff.mpr hvL)
      obtain ⟨sat1, hsp1, hrk1⟩ := saturation_properties E L _ hL hspL
      haveI : DiscreteTopology (span ℤ ({v} : Set E)) := hdisc _ hspL
      have hrksp : 0 < rk (span ℤ ({v} : Set E)) :=
        rk_pos_of_ne_zero_mem _ (mem_span_singleton_self v) hv0
      have dq := degree_quotient E L _ hL sat1
      have hc1 : 0 < covol (satur L (span ℤ ({v} : Set E))) := covol_pos' E _ (hdisc _ sat1.1)
      have hfin := ih (quot L (satur L (span ℤ ({v} : Set E)))) dq.1
        (X / covol (satur L (span ℤ ({v} : Set E))))
      refine Set.Finite.of_finite_image (f := fun N => quot N (satur L (span ℤ ({v} : Set E))))
        (hfin.subset ?_) ?_
      · rintro _ ⟨N, ⟨hN, hrkN, hcov, h1⟩, rfl⟩
        dsimp only [Set.mem_setOf_eq]
        have hdN := hdisc N hN.1
        have satN1 : IsSaturated N (satur L (span ℤ ({v} : Set E))) :=
          ⟨h1, fun x hx hxs => sat1.2 x (hN.1 hx) hxs⟩
        have dqN := degree_quotient E N _ hdN satN1
        have hcQ := covol_pos' E _ dqN.1
        have hcN := covol_pos' E N hdN
        have hlog : Real.log (covol N) = Real.log (covol (satur L (span ℤ ({v} : Set E))) *
            covol (quot N (satur L (span ℤ ({v} : Set E))))) := by
          rw [Real.log_mul hc1.ne' hcQ.ne']
          have := dqN.2.2
          unfold deg at this
          linarith
        have hmul := Real.log_injOn_pos (Set.mem_Ioi.mpr hcN) (Set.mem_Ioi.mpr (mul_pos hc1 hcQ)) hlog
        refine ⟨⟨Submodule.map_mono hN.1, fun y hy hys => ?_⟩, ?_, ?_⟩
        · obtain ⟨x, hxL, rfl⟩ := Submodule.mem_map.mp hy
          exact Submodule.mem_map_of_mem (mem_of_starProjection_mem_span_orthQuotient hN h1 hxL hys)
        · have := dqN.2.1
          omega
        · rw [le_div_iff₀ hc1, mul_comm, ← hmul]
          exact hcov
      · intro N hN N' hN' heq
        have key : ∀ {A B : Submodule ℤ E}, IsSaturated L B → satur L (span ℤ ({v} : Set E)) ≤ B →
            quot A (satur L (span ℤ ({v} : Set E))) = quot B (satur L (span ℤ ({v} : Set E))) →
            A ≤ L → A ≤ B := by
          intro A B hB hB1 hAB hAL x hx
          refine mem_of_starProjection_mem_span_orthQuotient hB hB1 (hAL hx) ?_
          rw [← hAB]
          exact subset_span (Submodule.mem_map_of_mem hx)
        exact le_antisymm (key hN'.1 hN'.2.2.2 heq hN.1.1) (key hN.1 hN.2.2.2 heq.symm hN'.1.1)
    ·
      rintro N ⟨hN, hrk, hcov⟩
      by_cases hbot : N = ⊥
      · exact Or.inl hbot
      right
      have hdN := hdisc N hN.1
      obtain ⟨v, hvN, hv0, hvle⟩ := hS E N hdN hbot
      have hr := rk_pos_of_ne_zero_mem N hvN hv0
      have hcN := covol_pos' E N hdN
      have hsq : Real.sqrt (rk N : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hrk)
      have hpow : covol N ^ ((1 : ℝ) / (rk N : ℝ)) ≤ max 1 X := by
        have he : (1 : ℝ) / (rk N : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hr)]
          exact_mod_cast hr
        have he0 : (0 : ℝ) ≤ 1 / (rk N : ℝ) := by positivity
        rcases le_or_gt (covol N) 1 with h | h
        · exact (Real.rpow_le_one hcN.le h he0).trans (le_max_left _ _)
        · calc covol N ^ ((1 : ℝ) / (rk N : ℝ)) ≤ covol N ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h.le he
            _ = covol N := Real.rpow_one _
            _ ≤ max 1 X := hcov.trans (le_max_right _ _)
      have hnorm : ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X :=
        hvle.trans (mul_le_mul hsq hpow (by positivity) (Real.sqrt_nonneg _))
      refine Set.mem_biUnion (x := v) ⟨hN.1 hvN, hnorm, hv0⟩ ⟨hN, hrk, hcov, ?_⟩
      intro x hx
      obtain ⟨hxL, hxs⟩ := Submodule.mem_inf.mp hx
      refine hN.2 x hxL (span_mono ?_ ((Submodule.restrictScalars_mem _ _ _).mp hxs))
      exact span_le.mpr (Set.singleton_subset_iff.mpr hvN)

theorem finiteSaturated_of (hS : ShortVector.{u}) : FiniteSaturated.{u} := by
  intro E _ _ _ L hL X
  refine (finite_saturated_rank_le_covol_le hS (rk L) L hL X).subset ?_
  rintro N ⟨hN, hX⟩
  have := (degree_quotient E L N hL hN).2.1
  exact ⟨hN, by omega, hX⟩

end Formalism.F
end
end

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum
open Module Submodule

noncomputable section

namespace Formalism.F

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_span_range_and_covol {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → E)
    (hu : LinearIndependent ℝ u) :
    DiscreteTopology (span ℤ (Set.range u)) ∧
      covol (span ℤ (Set.range u)) = Real.sqrt (Matrix.gram ℝ u).det := by
  have hd := discreteTopology_span_range_of_linearIndependent u hu
  refine ⟨hd, ?_⟩
  haveI := hd
  have hZ : LinearIndependent ℤ u := hu.restrict_scalars' ℤ
  rw [covol_eq_gram E (span ℤ (Set.range u)) ι (Basis.span hZ)]
  simp only [Basis.span_apply]

theorem discreteTopology_sup_and_covol_sup (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [DiscreteTopology L₂]
    (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0) :
    DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E) ∧ covol (L₁ ⊔ L₂) = covol L₁ * covol L₂ := by
  classical

  let b₁ := Module.finBasis ℤ L₁
  let b₂ := Module.finBasis ℤ L₂
  let v₁ : Fin (Module.finrank ℤ L₁) → E := fun i => (b₁ i : E)
  let v₂ : Fin (Module.finrank ℤ L₂) → E := fun i => (b₂ i : E)
  have hv₁ : LinearIndependent ℝ v₁ := linearIndependent_coe_basis''' L₁ b₁
  have hv₂ : LinearIndependent ℝ v₂ := linearIndependent_coe_basis''' L₂ b₂
  have horth : ∀ i j, inner ℝ (v₁ i) (v₂ j) = 0 := fun i j => h _ (b₁ i).2 _ (b₂ j).2
  have horth' : ∀ i j, inner ℝ (v₂ i) (v₁ j) = 0 := fun i j => by
    rw [real_inner_comm]; exact horth j i
  have hdisj : Disjoint (span ℝ (Set.range v₁)) (span ℝ (Set.range v₂)) := by
    apply Submodule.IsOrtho.disjoint
    rw [Submodule.isOrtho_span]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact horth i j
  have hli := hv₁.sum_type hv₂ hdisj
  have hs₁ : span ℤ (Set.range v₁) = L₁ := span_range_coe_basis' L₁ b₁
  have hs₂ : span ℤ (Set.range v₂) = L₂ := span_range_coe_basis' L₂ b₂
  have hspan : span ℤ (Set.range (Sum.elim v₁ v₂)) = L₁ ⊔ L₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hs₁, hs₂]
  obtain ⟨hd, hc⟩ := discreteTopology_span_range_and_covol _ hli
  rw [hspan] at hd hc
  refine ⟨hd, ?_⟩
  have hc₁ : covol L₁ = Real.sqrt (Matrix.gram ℝ v₁).det := covol_eq_gram E L₁ _ b₁
  have hc₂ : covol L₂ = Real.sqrt (Matrix.gram ℝ v₂).det := covol_eq_gram E L₂ _ b₂
  have hp₁ : 0 ≤ (Matrix.gram ℝ v₁).det := (det_gram_basis_pos L₁ b₁).le
  have hg : Matrix.gram ℝ (Sum.elim v₁ v₂) =
      Matrix.fromBlocks (Matrix.gram ℝ v₁) 0 0 (Matrix.gram ℝ v₂) := by
    ext (i | i) (j | j) <;> simp [Matrix.gram_apply, horth, horth']
  rw [hc, hc₁, hc₂, hg, Matrix.det_fromBlocks_zero₂₁, Real.sqrt_mul hp₁]

theorem degree_le_rank_mul_maxSlope (L N : Submodule ℤ E) (hL : DiscreteTopology L) (hNL : N ≤ L) :
    deg N ≤ rk N * muMax L := by
  haveI := hL
  by_cases hN : N = ⊥
  · subst hN
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · haveI : DiscreteTopology N := discreteTopology_of_le hNL
    have hs : slope N ≤ muMax L := slopeLeMuMax_of (slopesBdd_of gram_det_le) E L N hL hNL hN
    have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN)
    have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith

theorem degree_le_rank_mul_maxSlope_of_injective (Q M : Submodule ℤ E) (hQ : DiscreteTopology Q)
    (hM : DiscreteTopology M) (ψ : Q →ₗ[ℤ] M) (hinj : Function.Injective ψ)
    (hψ : ∀ x : Q, ‖((ψ x : M) : E)‖ ≤ ‖(x : E)‖) : deg Q ≤ rk Q * muMax M := by
  haveI := hQ
  by_cases hQ0 : Q = ⊥
  · subst hQ0
    have h0 : covol (⊥ : Submodule ℤ E) = 1 := (covol_basic_properties E).1
    have hr : rk (⊥ : Submodule ℤ E) = 0 := by simp [rk]
    simp [deg, h0, hr]
  · have hs := slopeInequality_of (slopeLeMuMax_of (slopesBdd_of gram_det_le)) E E Q M hQ hM hQ0
      ψ 1 hinj (fun x => by simpa using hψ x)
    rw [Real.log_one, add_zero] at hs
    have hk : 0 < rk Q := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQ0)
    have hk' : (0 : ℝ) < (rk Q : ℝ) := by exact_mod_cast hk
    unfold slope at hs
    rw [div_le_iff₀ hk'] at hs
    linarith


set_option maxHeartbeats 800000 in
theorem slope_le_max_maxSlope (L₁ L₂ : Submodule ℤ E) (h1 : DiscreteTopology L₁)
    (h2 : DiscreteTopology L₂) (h : ∀ x ∈ L₁, ∀ y ∈ L₂, inner ℝ x y = 0)
    (hd : DiscreteTopology (L₁ ⊔ L₂ : Submodule ℤ E))
    (N : Submodule ℤ E) (hN : N ≤ L₁ ⊔ L₂) (hN0 : N ≠ ⊥) :
    slope N ≤ max (muMax L₁) (muMax L₂) := by
  haveI := h1
  haveI := h2
  haveI := hd
  haveI hNd : DiscreteTopology N := discreteTopology_of_le hN

  obtain ⟨P, hPdef⟩ : ∃ P : E →L[ℝ] E, P = (span ℝ (L₂ : Set E)).starProjection := ⟨_, rfl⟩
  have hortho : span ℝ (L₁ : Set E) ≤ (span ℝ (L₂ : Set E))ᗮ := by
    rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    intro x hx y hy
    exact h x hx y hy
  have hP0 : ∀ x ∈ span ℝ (L₁ : Set E), P x = 0 := fun x hx => by
    rw [hPdef, Submodule.starProjection_apply_eq_zero_iff]
    exact hortho hx
  have hP1 : ∀ x ∈ L₁, P x = 0 := fun x hx => hP0 x (subset_span hx)
  have hP2 : ∀ x ∈ L₂, P x = x := fun x hx => by
    rw [hPdef, Submodule.starProjection_eq_self_iff]
    exact subset_span hx
  have hP3 : ∀ x ∈ L₁ ⊔ L₂, P x ∈ L₂ ∧ x - P x ∈ L₁ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _), hP1 y hy, hP2 z hz, zero_add, add_sub_cancel_right]
    exact ⟨hz, hy⟩
  have hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := fun x => by
    rw [hPdef]; exact Submodule.norm_starProjection_apply_le _ x

  set K : Submodule ℤ E := N ⊓ L₁ with hK
  have hKspan : span ℝ (K : Set E) ≤ span ℝ (L₁ : Set E) :=
    Submodule.span_mono (fun x hx => hx.2)
  have hsat : IsSaturated N K := by
    refine ⟨inf_le_left, fun x hx hxs => ⟨hx, ?_⟩⟩
    have h0 : P x = 0 := hP0 x (hKspan hxs)
    have := (hP3 x (hN hx)).2
    rwa [h0, sub_zero] at this
  obtain ⟨hQd, hrk, hdeg⟩ := degree_quotient E N K hNd hsat
  set Q := quot N K with hQ

  have hPR : ∀ x ∈ N, P ((span ℝ (K : Set E))ᗮ.starProjection x) = P x := by
    intro x hx
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have hS : (span ℝ (K : Set E)).starProjection x ∈ span ℝ (L₁ : Set E) := by
      apply hKspan
      rw [Submodule.starProjection_apply]
      exact SetLike.coe_mem _
    rw [hP0 _ hS, sub_zero]
  have hQmem : ∀ y ∈ Q, P y ∈ L₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) ∈ L₂
    rw [hPR x hx]
    exact (hP3 x (hN hx)).1
  let ψ : Q →ₗ[ℤ] L₂ := LinearMap.codRestrict L₂
    ((P.toLinearMap.restrictScalars ℤ).comp Q.subtype) (fun y => hQmem y.1 y.2)
  have hψ : ∀ y : Q, ((ψ y : L₂) : E) = P y := fun y => rfl
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy0
    have hPy : P y = 0 := by
      rw [← hψ, hy0]; rfl
    obtain ⟨y, hyQ⟩ := y
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyQ
    change P ((span ℝ (K : Set E))ᗮ.starProjection x) = 0 at hPy
    rw [hPR x hx] at hPy
    have hx1 : x ∈ L₁ := by
      have := (hP3 x (hN hx)).2
      rwa [hPy, sub_zero] at this
    have hxK : x ∈ span ℝ (K : Set E) := subset_span ⟨hx, hx1⟩
    apply Subtype.ext
    change (span ℝ (K : Set E))ᗮ.starProjection x = 0
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr hxK, sub_self]
  have hnorm : ∀ y : Q, ‖((ψ y : L₂) : E)‖ ≤ ‖(y : E)‖ := fun y => by
    rw [hψ]; exact hPnorm _
  have hdK : deg K ≤ rk K * muMax L₁ := degree_le_rank_mul_maxSlope L₁ K h1 inf_le_right
  have hdQ : deg Q ≤ rk Q * muMax L₂ := degree_le_rank_mul_maxSlope_of_injective Q L₂ hQd h2 ψ hinj hnorm
  have hk : 0 < rk N := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hN0)
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk
  have hK0 : (0 : ℝ) ≤ (rk K : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ (rk Q : ℝ) := Nat.cast_nonneg _
  have e1 : (rk K : ℝ) * muMax L₁ ≤ (rk K : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hK0
  have e2 : (rk Q : ℝ) * muMax L₂ ≤ (rk Q : ℝ) * max (muMax L₁) (muMax L₂) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hQ0
  have hrk' : (rk N : ℝ) = (rk K : ℝ) + (rk Q : ℝ) := by exact_mod_cast hrk
  unfold slope
  rw [div_le_iff₀ hk', hdeg, hrk']
  linarith

end

theorem orthogonal_sum_slope : OrthSum := by
  intro E _ _ _ L₁ L₂ h1 h2 h
  haveI := h1
  haveI := h2
  obtain ⟨hd, hc⟩ := discreteTopology_sup_and_covol_sup L₁ L₂ h
  refine ⟨hd, ?_, ?_⟩
  · have p1 := covol_pos_of_discrete L₁
    have p2 := covol_pos_of_discrete L₂
    unfold deg
    rw [hc, Real.log_mul p1.ne' p2.ne']
    ring
  · intro hL1 hL2
    apply le_antisymm
    · show sSup (slopes (L₁ ⊔ L₂)) ≤ _
      refine csSup_le ⟨_, L₁, le_sup_left, hL1, rfl⟩ ?_
      rintro t ⟨N, hN, hN0, rfl⟩
      exact slope_le_max_maxSlope L₁ L₂ h1 h2 h hd N hN hN0
    · have hmono := muMaxMono_of (slopesBdd_of gram_det_le)
      exact max_le (hmono E (L₁ ⊔ L₂) L₁ hd le_sup_left hL1)
        (hmono E (L₁ ⊔ L₂) L₂ hd le_sup_right hL2)

end Formalism.F
end
end

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin
open Module

namespace Formalism.F

universe u

theorem muMaxLeMin_of (hP : CovolPos.{u}) (hS : ShortVector.{u}) : MuMaxLeMin.{u} := by
  intro E _ _ _ L hL hL0 r hr hmin
  haveI := hL
  have hne : (slopes L).Nonempty := ⟨slope L, L, le_rfl, hL0, rfl⟩
  unfold muMax
  apply csSup_le hne
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI : DiscreteTopology N := discreteTopology_of_le hNL
  have hk : 0 < rk N := att_rk_pos hN0
  have hkL : rk N ≤ rk L := att_rk_le hNL
  have hc : 0 < covol N := hP E N inferInstance
  obtain ⟨v, hvN, hv0, hvle⟩ := hS E N inferInstance hN0
  have hrv : r ≤ ‖v‖ := hmin v (hNL hvN) hv0
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk

  have h1 : Real.log r ≤ Real.log (rk N : ℝ) / 2 + Real.log (covol N) / (rk N : ℝ) := by
    have hpow : 0 < covol N ^ ((1 : ℝ) / (rk N : ℝ)) := Real.rpow_pos_of_pos hc _
    have hsq : 0 < Real.sqrt (rk N : ℝ) := Real.sqrt_pos.mpr hk'
    have h := Real.log_le_log hr (hrv.trans hvle)
    rw [Real.log_mul hsq.ne' hpow.ne', Real.log_sqrt hk'.le, Real.log_rpow hc] at h
    have e : (1 : ℝ) / (rk N : ℝ) * Real.log (covol N) = Real.log (covol N) / (rk N : ℝ) := by ring
    linarith
  have h2 : Real.log (rk N : ℝ) ≤ Real.log (rk L : ℝ) :=
    Real.log_le_log hk' (by exact_mod_cast hkL)
  have h3 : slope N = -(Real.log (covol N) / (rk N : ℝ)) := by
    unfold slope deg; ring
  rw [h3]
  linarith

end Formalism.F
end

namespace Formalism.F

theorem covolEqGram : CovolEqGram := covol_eq_gram
theorem covolPos : CovolPos := covol_pos'
theorem covolBasic : CovolBasic := covol_basic_properties
theorem covolEqCovolume : CovolEqCovolume := covol_eq_covolume'
theorem gramDetLe : GramDetLe := gram_det_le
theorem slopesBdd : SlopesBdd := slopesBdd_of gramDetLe
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
theorem degQuot : DegQuot := degree_quotient
theorem covolAntiSameRank : CovolAntiSameRank := covol_anti_same_rank
theorem saturProps : SaturProps := saturation_properties
theorem shortVector : ShortVector := shortVector_of covolEqCovolume
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of covolPos shortVector
theorem orthSum : OrthSum := orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem covol_pos (L : Submodule ℤ E) [DiscreteTopology L] : 0 < covol L :=
  covolPos E L ‹_›

theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end Formalism.F
