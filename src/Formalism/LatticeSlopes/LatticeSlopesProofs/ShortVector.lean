module

public import Formalism.LatticeSlopes.CovolAntiSameRank
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe

@[expose] public section

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
open Module Submodule MeasureTheory

noncomputable section

namespace Formalism.F

universe u

theorem covol_eq_of_linearEquiv_inner {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology M]
    (f : L ≃ₗ[ℤ] M)
    (hf : ∀ x y : L, inner ℝ ((f x : M) : F) ((f y : M) : F) = inner ℝ (x : E) (y : E)) :
    covol M = covol L := by
  classical
  let b := Module.finBasis ℤ L
  rw [covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]
  congr 2
  ext i j
  simp only [Matrix.gram, Matrix.of_apply, Basis.map_apply]
  exact hf (b i) (b j)

theorem exists_short_vector_of_isZLattice (hC : CovolEqCovolume.{u}) {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ Real.sqrt (finrank ℝ W : ℝ) * covol L ^ ((1 : ℝ) / (finrank ℝ W : ℝ)) := by
  classical
  set n := finrank ℝ W with hn_def
  let b := Module.finBasis ℤ L
  have hfund := ZLattice.isAddFundamentalDomain b MeasureTheory.volume
  have hcov : ZLattice.covolume L = MeasureTheory.volume.real
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L _ hfund
  have hFfin : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hc : 0 < covol L := by
    rw [hC W L]
    exact ZLattice.covolume_pos L _
  have hF : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
      ENNReal.ofReal (covol L) := by
    rw [hC W L, hcov, MeasureTheory.measureReal_def, ENNReal.ofReal_toReal hFfin]

  set t := covol L ^ ((1 : ℝ) / (n : ℝ)) with ht_def
  have ht : 0 ≤ t := Real.rpow_nonneg hc.le _
  have htn : t ^ n = covol L := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  let o := stdOrthonormalBasis ℝ W
  set S : Set W := {x | ∀ i, |o.repr x i| ≤ t} with hS
  have hnorm : ∀ x ∈ S, ‖x‖ ≤ Real.sqrt (n : ℝ) * t := by
    intro x hx
    rw [← o.repr.norm_map x, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖o.repr x i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, t ^ 2) := by
          apply Real.sqrt_le_sqrt
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
      _ = Real.sqrt (n : ℝ) * t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx i
    simpa [map_neg] using hx i
  have hconv : Convex ℝ S := by
    intro x hx y hy a c ha hc hac i
    simp only [map_add (f := _), map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc |a * o.repr x i + c * o.repr y i| ≤ |a * o.repr x i| + |c * o.repr y i| := abs_add_le _ _
      _ = a * |o.repr x i| + c * |o.repr y i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
      _ ≤ a * t + c * t := by
          gcongr
          · exact hx i
          · exact hy i
      _ = t := by rw [← add_mul, hac, one_mul]
  have hclosed : IsClosed S := by
    rw [hS, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hcpt : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    refine (Metric.isBounded_closedBall (x := (0 : W)) (r := Real.sqrt (n : ℝ) * t)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm x hx
  have hSeq : S = (WithLp.ofLp ∘ o.measurableEquiv) ⁻¹'
      Set.Icc (fun _ => -t) (fun _ => t) := by
    ext x
    simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, Set.mem_Icc,
      Pi.le_def, abs_le, forall_and]
    rfl
  have hvolS : MeasureTheory.volume S = ENNReal.ofReal (t - -t) ^ n := by
    rw [hSeq, ((PiLp.volume_preserving_ofLp (Fin n)).comp
      o.measurePreserving_measurableEquiv).measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmeas : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) *
      2 ^ n ≤ MeasureTheory.volume S := by
    rw [hF, hvolS, ← ENNReal.ofReal_pow (by linarith),
      show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by simp,
      ← ENNReal.ofReal_mul hc.le]
    apply le_of_eq
    congr 1
    rw [show t - -t = 2 * t by ring, mul_pow, htn, mul_comm]
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hn
  haveI hLc : Countable L := b.equivFun.injective.countable
  haveI : Countable L.toAddSubgroup := hLc
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (L := L.toAddSubgroup) hfund hsymm hconv hcpt hmeas
  refine ⟨(x : W), x.2, ?_, hnorm _ hxS⟩
  intro h0
  exact hx0 (Subtype.ext h0)

theorem shortVector_of (hC : CovolEqCovolume.{u}) : ShortVector.{u} := by
  intro E _ _ _ L hL hne
  classical
  haveI : DiscreteTopology L := hL

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L ≃ₗ[ℤ] L₀ :=
    { toFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      invFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e.symm) ?_ e.symm.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  haveI : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  letI : MeasurableSpace (Submodule.span ℝ (L : Set E)) := borel _
  haveI : BorelSpace (Submodule.span ℝ (L : Set E)) := ⟨rfl⟩
  have hcov : covol L₀ = covol L :=
    covol_eq_of_linearEquiv_inner L L₀ e (fun _ _ => rfl)
  have hrk : finrank ℝ (Submodule.span ℝ (L : Set E)) = rk L := by
    rw [← ZLattice.rank ℝ L₀]
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E)) := by
    rw [hrk]
    exact Module.finrank_pos
  obtain ⟨x, hx, hx0, hxn⟩ := exists_short_vector_of_isZLattice hC L₀ hpos
  refine ⟨(x : E), hx, ?_, ?_⟩
  · intro h0
    exact hx0 (Subtype.ext h0)
  · rw [hrk, hcov] at hxn
    exact hxn

end Formalism.F
end
end

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
open Module

namespace Formalism.F

universe u

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem att_rk_pos {N : Submodule ℤ E} [DiscreteTopology N] (hN : N ≠ ⊥) : 0 < rk N := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  exact Module.finrank_pos

theorem att_rk_le {L N : Submodule ℤ E} [DiscreteTopology L] (h : N ≤ L) : rk N ≤ rk L :=
  LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion h) (Submodule.inclusion_injective h)

end

end Formalism.F
end

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
open Module Submodule

noncomputable section

namespace Formalism.F

theorem linearIndependent_coe_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical

  let V : Submodule ℝ E := Submodule.span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L ≃ₗ[ℤ] L' :=
    { toFun := fun x => ⟨⟨x, Submodule.subset_span x.2⟩, x.2⟩
      invFun := fun y => ⟨((y : V) : E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective (f := fun y : L' => (⟨((y : V) : E), y.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (by
        intro a c h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    show Submodule.span ℝ _ = Submodule.span ℝ (L : Set E)
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩⟩
  have hrank := ZLattice.rank ℝ L'
  have hLspan : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have h1 := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
    exact h1
  have key : Fintype.card ι = Module.finrank ℝ V := by
    rw [← hrank, ← φ.finrank_eq, Module.finrank_eq_card_basis b]
  rw [linearIndependent_iff_card_eq_finrank_span]
  show Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => (b i : E)))
  rw [← Submodule.span_span_of_tower ℤ ℝ, hLspan]
  exact key

theorem covol_pos' : CovolPos := by
  intro E _ _ _ L hL
  haveI := hL
  rw [covol_eq_gram E L (Fin (Module.finrank ℤ L)) (Module.finBasis ℤ L)]
  apply Real.sqrt_pos.2
  exact (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis L _)).det_pos

theorem discreteTopology_span_singleton {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : v ≠ 0) :
    DiscreteTopology (span ℤ ({v} : Set E)) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hs : ({0} : Set (span ℤ ({v} : Set E))) = Metric.ball 0 ‖v‖ := by
    ext ⟨x, hx⟩
    rw [Set.mem_singleton_iff, mem_ball_zero_iff]
    constructor
    · intro h
      rw [h, norm_zero]
      exact hv'
    · intro h
      obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have hn : ‖n • v‖ < ‖v‖ := h
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs] at hn
      have h1 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left hv').1 hn
      have hn0 : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h1)
      subst hn0
      exact Subtype.ext (zero_smul ℤ v)
  rw [hs]
  exact Metric.isOpen_ball

theorem covol_basic_properties : CovolBasic := by
  intro E _ _ _
  refine ⟨?_, ?_⟩
  · haveI : DiscreteTopology (⊥ : Submodule ℤ E) := inferInstance
    rw [covol_eq_gram E ⊥ (Fin 0) (Module.Basis.empty _)]
    simp [Matrix.det_isEmpty]
  · intro v hv
    haveI := discreteTopology_span_singleton hv
    have hli : LinearIndependent ℤ (fun _ : Unit => v) := by
      have hR : LinearIndependent ℝ (fun _ : Unit => v) := by
        rw [linearIndependent_unique_iff]
        first
          | exact hv
          | (intro r hr; exact (smul_eq_zero.1 hr).resolve_right hv)
      first
        | exact hR.restrict_scalars' ℤ
        | exact hR.restrict_scalars (by intro a c h; simpa using h)
    have hr : span ℤ (Set.range fun _ : Unit => v) = span ℤ ({v} : Set E) := by
      rw [Set.range_const]
    let b : Basis Unit ℤ (span ℤ ({v} : Set E)) := (Basis.span hli).map (LinearEquiv.ofEq _ _ hr)
    have hb : (fun i => (b i : E)) = fun _ => v := by
      funext i
      simp [b, Basis.span_apply]
    rw [covol_eq_gram E _ Unit b, hb, Matrix.det_unique, Matrix.gram_apply,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end Formalism.F
end
end

section -- merged from Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeInequality
open Module Submodule

noncomputable section

namespace Formalism.F

universe u v

private theorem finrank_int_eq_finrank_real_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L₀ ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      invFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e) ?_ e.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  haveI : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  rw [← e.finrank_eq, ZLattice.rank ℝ L₀]

theorem linearIndependent_coe_basis'' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical
  have h1 : Submodule.span ℤ (Set.range (fun i => (b i : E))) = L := by
    have := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range (fun i => (b i : E))) =
      Submodule.span ℝ (L : Set E) := by
    have h2 := Submodule.span_span_of_tower ℤ ℝ (Set.range (fun i => (b i : E)))
    rw [h1] at h2
    exact h2.symm
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, ← finrank_int_eq_finrank_real_span L,
    Module.finrank_eq_card_basis b]

theorem det_gram_basis_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    0 < (Matrix.gram ℝ (fun i => (b i : E))).det :=
  (Matrix.posDef_gram_of_linearIndependent (linearIndependent_coe_basis'' L b)).det_pos

theorem covol_pos_of_discrete {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    0 < covol L := by
  classical
  rw [covol, dite_eq_left (inferInstance : DiscreteTopology L)]
  exact Real.sqrt_pos.mpr (det_gram_basis_pos L _)

theorem norm_sum_smul_le_of_int {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (v : ι → E) (w : ι → F)
    (C : ℝ) (h : ∀ n : ι → ℤ, ‖∑ i, (n i : ℝ) • w i‖ ≤ C * ‖∑ i, (n i : ℝ) • v i‖) :
    ∀ c : ι → ℝ, ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖ := by

  have hq : ∀ q : ι → ℚ, ‖∑ i, (q i : ℝ) • w i‖ ≤ C * ‖∑ i, (q i : ℝ) • v i‖ := by
    intro q
    classical
    obtain ⟨m, hm, hz⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ z : ℤ, (q i : ℝ) * m = z := by
      refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), fun i => ?_⟩
      obtain ⟨k, hk⟩ : (q i).den ∣ ∏ j, (q j).den :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(q i).num * k, ?_⟩
      rw [hk]
      push_cast
      rw [← mul_assoc]
      congr 1
      exact_mod_cast Rat.mul_den_eq_num (q i)
    choose n hn using hz
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hw : ∑ i, (n i : ℝ) • w i = (m : ℝ) • ∑ i, (q i : ℝ) • w i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have hv : ∑ i, (n i : ℝ) • v i = (m : ℝ) • ∑ i, (q i : ℝ) • v i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hn i, smul_smul, mul_comm]
    have key := h n
    rw [hw, hv, norm_smul, norm_smul, Real.norm_of_nonneg hm'.le, mul_left_comm] at key
    exact le_of_mul_le_mul_left key hm'

  intro c
  have hd : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  refine hd.induction_on (p := fun c : ι → ℝ => ‖∑ i, c i • w i‖ ≤ C * ‖∑ i, c i • v i‖) c ?_ hq
  exact isClosed_le (by fun_prop) (by fun_prop)

theorem slopeInequality_of (h : SlopeLeMuMax.{v}) : SlopeInequality.{u, v} := by
  intro E F _ _ _ _ _ _ L M hL hM hne φ C hφ hC
  classical
  let g : L →ₗ[ℤ] F := M.subtype.comp φ
  have ginj : Function.Injective g := M.injective_subtype.comp hφ
  let N : Submodule ℤ F := LinearMap.range g
  have hNM : N ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact (φ x).2
  haveI : DiscreteTopology L := hL
  haveI : DiscreteTopology M := hM
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (continuous_inclusion hNM)
      (Submodule.inclusion_injective hNM)
  let e : L ≃ₗ[ℤ] N := LinearEquiv.ofInjective g ginj

  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφx : ((φ ⟨x, hxL⟩ : M) : F) ≠ 0 := by
    intro h0
    apply hx0
    have h1 : φ ⟨x, hxL⟩ = φ 0 := by
      rw [map_zero]
      exact Subtype.ext h0
    exact congrArg Subtype.val (hφ h1)
  have hNne : N ≠ ⊥ := by
    intro h0
    apply hφx
    have hmem : g ⟨x, hxL⟩ ∈ N := LinearMap.mem_range_self g _
    rw [h0, Submodule.mem_bot] at hmem
    exact hmem
  have hCpos : 0 < C := by
    have h1 : ‖((φ ⟨x, hxL⟩ : M) : F)‖ ≤ C * ‖x‖ := hC ⟨x, hxL⟩
    have h2 : 0 < ‖((φ ⟨x, hxL⟩ : M) : F)‖ := norm_pos_iff.mpr hφx
    have h3 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h3.le]
  have h1 : slope N ≤ muMax M := h F M N hM hNM hNne

  set r := Module.finrank ℤ L with hr_def
  have hrkL : rk L = r := rfl
  have hrkN : rk N = r := by
    show Module.finrank ℤ N = Module.finrank ℤ L
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hrpos : 0 < r := Module.finrank_pos

  let b := Module.finBasis ℤ L
  have hcL : covol L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det :=
    covol_eq_gram E L (Fin r) b
  have hcN : covol N = Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det :=
    covol_eq_gram F N (Fin r) (b.map e)
  have hint : ∀ n : Fin r → ℤ,
      ‖∑ i, (n i : ℝ) • ((φ (b i) : M) : F)‖ ≤ C * ‖∑ i, (n i : ℝ) • (b i : E)‖ := by
    intro n
    have h2 := hC (∑ i, n i • b i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul] at h2
    simpa only [Int.cast_smul_eq_zsmul] using h2
  have hreal := norm_sum_smul_le_of_int (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hint
  have hdet := gram_det_le E F (Fin r) (fun i => (b i : E))
    (fun i => ((φ (b i) : M) : F)) C hreal
  have hle : covol N ≤ C ^ r * covol L := by
    rw [hcN, hcL]
    calc Real.sqrt (Matrix.gram ℝ (fun i => ((φ (b i) : M) : F))).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin r)) *
            (Matrix.gram ℝ (fun i => (b i : E))).det) := Real.sqrt_le_sqrt hdet
      _ = C ^ r * Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det := by
        rw [Fintype.card_fin, show C ^ (2 * r) = (C ^ r) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hcLpos := covol_pos_of_discrete L
  have hcNpos := covol_pos_of_discrete N
  have hlog : Real.log (covol N) ≤ r * Real.log C + Real.log (covol L) := by
    have h2 := Real.log_le_log hcNpos hle
    rwa [Real.log_mul (by positivity) hcLpos.ne', Real.log_pow] at h2
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hs : slope L ≤ slope N + Real.log C := by
    unfold slope deg
    rw [hrkL, hrkN, div_add' _ _ _ hr.ne', div_le_div_iff_of_pos_right hr]
    nlinarith
  linarith

end Formalism.F
end
end
