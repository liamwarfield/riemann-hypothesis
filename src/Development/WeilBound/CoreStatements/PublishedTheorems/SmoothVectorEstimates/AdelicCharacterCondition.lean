module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AdelicCharacterCondition
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AdelicCharacterCondition

theorem isCharAF_of {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF E ψ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  have hb : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime, hb⟩
  exact ⟨hψ.cont, hψ.norm, hψ.rat, _, hy⟩

theorem condAA {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    ∀ᶠ v in (cofinite : Filter (HeightOneSpectrum (𝓞 E))), ∀ t : v.adicCompletion E,
      (∀ s ∈ v.adicCompletionIntegers E, ψ (sFin E (sLoc E v (s * t))) = 1) ↔ t ∈ v.adicCompletionIntegers E := by
  have h := _root_.PI.VolStabSW.VolAAW.condAA_of (_root_.PI.VolStabSW.VolAAW.condExact_of _root_.PI.VolStabSW.sAf_holds
    (_root_.PI.VolStabSW.chInf_of_lift _root_.PI.VolStabSW.chLift_holds)) E ψ (isCharAF_of hψ)
  filter_upwards [h] with v hv t
  simp only [sFin_sLoc_eq]
  exact hv t

end AdelicCharacterCondition

theorem adelic_character_holds : StandardCharacterExists := by
  intro E _ _ _
  obtain ⟨ψ, hψ⟩ := exists_stdPsi E
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [AdelicCharacterCondition.condAA hψ] with w hw
  have hint : ∀ y ∈ Ov E w, ψ (sFin E (sLoc E w y)) = 1 := by
    intro y hy
    have := (hw 1).2 (one_mem _) y hy
    rwa [mul_one] at this
  refine ⟨hint, ?_⟩
  set ϖ : w.adicCompletion E := ((w.valuation_exists_uniformizer E).choose : w.adicCompletion E) with hϖ
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [hϖ, w.valuedAdicCompletion_eq_valuation', (w.valuation_exists_uniformizer E).choose_spec]
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  have hu : IsUnifV E w ϖ := hv
  have hnot : ϖ⁻¹ ∉ w.adicCompletionIntegers E := by
    intro h
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
    rw [hv] at h
    exact absurd h (by decide)
  have hex : ¬ ∀ s ∈ w.adicCompletionIntegers E, ψ (sFin E (sLoc E w (s * ϖ⁻¹))) = 1 :=
    fun h => hnot ((hw _).1 h)
  push Not at hex
  obtain ⟨s, hs, hne⟩ := hex
  refine ⟨ϖ, s * ϖ⁻¹, hu, ?_, hne⟩
  rw [mul_comm s, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  exact hs

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InfiniteFiniteFactorization
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace InfiniteFiniteFactorization

open Classical

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem stepInf (h6 : G6) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (m : Pl E → ℕ)
    (h : St ψ S Y Y' 0 m) : ∀ n, n ≤ a - 1 → St ψ S Y Y' n m := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro hn; exact h6 E a ψ hψ S Y Y' hY hY' n m (by omega) (ih (by omega))

theorem stepFin (h7 : G7) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (w : Pl E) (hw : w ∈ S)
    (n : ℕ) (m : Pl E → ℕ) (hm : m w = 0) (h : St ψ S Y Y' n m) :
    ∀ k, k ≤ a - 1 → St ψ S Y Y' n (Function.update m w k) := by
  intro k
  induction k with
  | zero => intro _; rw [Function.update_eq_self_iff.mpr hm.symm]; exact h
  | succ k ih =>
    intro hk
    have h' := h7 E a ψ hψ S Y Y' hY hY' n (Function.update m w k) w hw
      (by simp only [Function.update_self]; omega) (ih (by omega))
    simpa only [Function.update_self, Function.update_idem] using h'

end InfiniteFiniteFactorization

open InfiniteFiniteFactorization in
theorem whittaker_factorization_places : G6 → G7 → FourierInductionSteps := by
  classical
  intro h6 h7 E _ _ _ a ψ hψ S Y Y' hY hY' h0
  have h1 := stepInf h6 hψ hY hY' (fun _ => 0) h0 (a - 1) le_rfl
  have key : ∀ T : Finset (Pl E), T ⊆ S →
      St ψ S Y Y' (a - 1) (fun w => if w ∈ T then a - 1 else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      simpa using h1
    · intro x T hx ih hT
      have h := stepFin h7 hψ hY hY' x (hT (Finset.mem_insert_self x T)) (a - 1)
        (fun w => if w ∈ T then a - 1 else 0) (by simp [hx])
        (ih (subset_trans (Finset.subset_insert x T) hT)) (a - 1) le_rfl
      convert h using 1
      funext w
      by_cases hw : w = x
      · subst hw; simp
      · simp [hw]
  exact key S subset_rfl

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InductionG11
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearInduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem step (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hma : m + 1 < a) (hG : Good ψ (m + 1) f)
    (Z : Set (GA E a)) (hZ : ∀ γ, IsMir (m + 1) γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z)
    (hc : ∀ g ∈ Z, colT ψ (m + 1) f g = 0) : ∀ g ∈ Z, f g = 0 := by
  intro g₀ hg
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) = 0 := by
    refine _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer fun ξ => ?_
    by_cases hξ0 : ξ = 0
    · subst hξ0
      have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
      have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
          ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
        intro x
        simp [dot]
      simp only [e, one_mul]
      exact hv
    · obtain ⟨γ, hγ, hγξ⟩ := _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
      have h1 := hc _ (hZ γ hγ g₀ hg)
      simp only [colT] at h1
      rw [_root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
      have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) =>
          ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ := funext hγξ
      rw [e] at h1
      exact h1
  have h1 := congrFun hΦ 0
  simp only [Pi.zero_apply] at h1
  have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
  rw [e, one_mul] at h1
  exact h1

theorem main (hψ : StdPsi ψ) (m : ℕ) : ∀ (f : GA E a → ℂ), (m < a ∨ m = 0) → Good ψ m f →
    ∀ Z : Set (GA E a), (∀ γ, IsMir m γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z) →
      (∀ g ∈ Z, whit ψ m f g = 0) → ∀ g ∈ Z, f g = 0 := by
  induction m with
  | zero => intro f _ _ Z _ hw; exact hw
  | succ m ih =>
    intro f hm hG Z hZ hw
    have hma : m + 1 < a := by omega
    refine step hψ m f hma hG Z hZ ?_
    refine ih _ (Or.inl (by omega)) (_root_.GlobalTheory.CuspRep.Generic.good_colT hψ hma hG) Z
      (fun γ hγ g hg => hZ γ (fun i k h => hγ i k (by omega)) g hg) ?_
    intro g hg
    exact hw g hg

end GeneralLinearInduction

theorem induction_g11_holds : FourierUniquenessMirabolic := by
  intro E _ _ _ a ψ hψ m f hm hG Z hZ _ hw
  exact GeneralLinearInduction.main hψ m f hm hG Z hZ hw

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.BoundedInvariantL2
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace BoundedInvariantL2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]

theorem memL2Quotient_of_bounded_left_invariant [IsFiniteMeasure (quotMeasure Γ μ)] (φ : G →ᵇ ℂ) (h : LeftInv Γ φ) : MemL2Quotient Γ μ φ := by
  refine ⟨h, MemLp.of_bound ?_ ‖φ‖ (Eventually.of_forall fun q => φ.norm_coe_le_norm q.out)⟩
  rw [aestronglyMeasurable_quotMeasure_iff_lift, h.lift_descend]
  exact φ.continuous.aestronglyMeasurable

theorem norm_toL2_sub_le_sup_norm [IsFiniteMeasure (quotMeasure Γ μ)] (φ ψ : G →ᵇ ℂ) (hφ : MemL2Quotient Γ μ φ)
    (hψ : MemL2Quotient Γ μ ψ) :
    ‖hφ.toL2 - hψ.toL2‖ ≤ (measureUnivNNReal (quotMeasure Γ μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹ * ‖φ - ψ‖ := by
  have hd : LeftInv Γ ⇑(φ - ψ) := fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g]
  have h := memL2Quotient_of_bounded_left_invariant (μ := μ) (φ - ψ) hd
  have e : hφ.toL2 - hψ.toL2 = h.toL2 := (MemLp.toLp_sub hφ.2 hψ.2).symm
  rw [e]
  exact Lp.norm_le_of_ae_bound (norm_nonneg _)
    (h.coeFn_toL2.mono fun q hq => by rw [hq]; exact (φ - ψ).norm_coe_le_norm _)

end BoundedInvariantL2

theorem bounded_invariant_functions_in_L2 : G2b := by
  intro E _ _ _ a μ _ _ H hH
  have := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  let Y : Submodule ℂ (XB E a) :=
    { carrier := {φ | ∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H}
      add_mem' := by
        rintro φ ψ ⟨h1, m1⟩ ⟨h2, m2⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(φ + ψ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g, h2.1 γ hγ g], h1.2.add h2.2⟩
        have e : h.toL2 = h1.toL2 + h2.toL2 := MemLp.toLp_add h1.2 h2.2
        exact ⟨h, e ▸ H.add_mem m1 m2⟩
      zero_mem' := by
        have h : MemL2Quotient (latticeGL E a) μ ⇑(0 : XB E a) := ⟨fun γ hγ g => rfl, MemLp.zero⟩
        have e : h.toL2 = 0 := MemLp.toLp_zero h.2
        exact ⟨h, e ▸ H.zero_mem⟩
      smul_mem' := by
        rintro c φ ⟨h1, m1⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(c • φ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g], h1.2.const_smul c⟩
        have e : h.toL2 = c • h1.toL2 := MemLp.toLp_const_smul c h1.2
        exact ⟨h, e ▸ H.smul_mem c m1⟩ }
  refine ⟨Y, ?_, ?_, fun φ => Iff.rfl⟩
  · refine IsSeqClosed.isClosed fun {x p} hx hp => ?_
    choose hxm hxH using hx
    have hpl : LeftInv (latticeGL E a) ⇑p := fun γ hγ g => by
      have t1 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p (γ * g))) :=
        ((continuous_eval_const (γ * g)).tendsto p).comp hp
      have t2 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p g)) := by
        have := ((continuous_eval_const g).tendsto p).comp hp
        refine this.congr fun n => ?_
        exact ((hxm n).1 γ hγ g).symm
      exact tendsto_nhds_unique (f := fun n => x n (γ * g)) (l := (atTop : Filter ℕ)) t1 t2
    have hp2 := BoundedInvariantL2.memL2Quotient_of_bounded_left_invariant (μ := μ) p hpl
    refine ⟨hp2, hH.1.mem_of_tendsto (f := fun n => (hxm n).toL2) (b := (atTop : Filter ℕ)) ?_
      (Eventually.of_forall hxH)⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hn : Tendsto (fun n => ‖x n - p‖) atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hp
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => BoundedInvariantL2.norm_toL2_sub_le_sup_norm (x n) p (hxm n) hp2) ?_
    simpa using hn.const_mul ((measureUnivNNReal (quotMeasure (latticeGL E a) μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹)
  · rintro g φ ⟨h, m⟩
    have m' := hH.2 g _ m
    rw [right_translate_toL2] at m'
    exact ⟨h.mul_right g, m'⟩

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.HeckeOperatorOfAutomorphic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenfunctionsClosed
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.HeckeEigenspaces

theorem exists_closed_common_ker {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (𝒯 : Set (X →L[ℂ] X)) :
    ∃ Y : Submodule ℂ X, IsClosed (Y : Set X) ∧ ∀ φ, φ ∈ Y ↔ ∀ T ∈ 𝒯, T φ = 0 := by
  refine ⟨{ carrier := {φ | ∀ T ∈ 𝒯, T φ = 0}
            add_mem' := fun {x y} hx hy T hT => by rw [map_add (f := _), hx T hT, hy T hT, add_zero]
            zero_mem' := fun T _ => map_zero T
            smul_mem' := fun c x hx T hT => by rw [map_smul, hx T hT, smul_zero] }, ?_, fun _ => Iff.rfl⟩
  have e : ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X) = ⋂ T ∈ 𝒯, T ⁻¹' {0} := by
    ext φ; simp
  change IsClosed ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X)
  rw [e]
  exact isClosed_biInter fun T _ => isClosed_singleton.preimage T.continuous

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem exists_heckeOp (w : Pl E) {h : GL (Fin a) (w.adicCompletion E) → ℂ} (hh : h ∈ Hecke ℂ (KGL w (n := a))) :
    ∃ T : XB E a →L[ℂ] XB E a, (∀ x, heckeVec (repW a w) (KGL w (n := a)) h x = T x) ∧
      ∀ A : XB E a →L[ℂ] XB E a, (∀ u, Commute A (Rt E a (fl a w u))) → Commute A T := by
  classical
  have hs := Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) hh.2
  refine ⟨∑ c ∈ hs.toFinset, h c.out • Rt E a (fl a w c.out), fun x => ?_, fun A hA => ?_⟩
  · rw [heckeVec, finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · simp
    · intro c hc
      refine Finset.mem_coe.2 (hs.mem_toFinset.2 fun h0 => hc (by simp [h0]))
  · exact Commute.sum_right _ _ _ fun c _ => (hA c.out).smul_right _

theorem hecke_eigenfunctions_closed : G0 → G2c := by
  intro h0 E _ _ _ a w B hB
  have hcomm : ∀ g : GA E a, cLoc w g = 1 → ∀ u, Commute (Rt E a g) (Rt E a (fl a w u)) := fun g hg u => by
    have e := (h0 E a).2.2.2.2.2.2.2.1 w g hg u
    change Rt E a g * Rt E a (fl a w u) = Rt E a (fl a w u) * Rt E a g
    rw [← map_mul, ← map_mul, e]
  choose T hT hC using fun (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ) =>
    exists_heckeOp (a := a) w (Tj_mem_hecke (n := a) p.2 j)
  obtain ⟨Y, hcl, hY⟩ := exists_closed_common_ker
    ({R | (∃ k ∈ KGL w (n := a), R = Rt E a (fl a w k) - 1) ∨
      ∃ (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ), j ≤ a ∧ R = T p j - satEig (qV E w) a B j • 1} :
      Set (XB E a →L[ℂ] XB E a))
  refine ⟨Y, hcl, fun g hg φ hφ => ?_, fun φ => ?_⟩
  · rw [hY] at hφ ⊢
    intro R hR
    have hRc : Commute (Rt E a g) R := by
      rcases hR with ⟨k, -, rfl⟩ | ⟨p, j, -, rfl⟩
      · exact (hcomm g hg k).sub_right (Commute.one_right _)
      · exact (hC p j _ (hcomm g hg)).sub_right ((Commute.one_right _).smul_right _)
    have e : R (Rt E a g φ) = Rt E a g (R φ) := (DFunLike.congr_fun hRc.eq φ).symm
    rw [e, hφ R hR, map_zero]
  · rw [hY]
    constructor
    · intro h
      by_cases hφ : φ = 0
      · exact Or.inl hφ
      · refine Or.inr ⟨hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hB, fun ϖ hϖ j hj => ?_⟩
        · have := h _ (Or.inl ⟨k, hk, rfl⟩)
          simpa [sub_eq_zero] using this
        · have := h _ (Or.inr ⟨⟨ϖ, hϖ⟩, j, hj, rfl⟩)
          rw [hT ⟨ϖ, hϖ⟩ j]
          simpa [sub_eq_zero] using this
    · rintro (rfl | ⟨-, hfix, -, heig⟩) R hR
      · exact map_zero R
      · rcases hR with ⟨k, hk, rfl⟩ | ⟨p, j, hj, rfl⟩
        · have := GlobalTheory.LGrp.mem_fixed.1 hfix k hk
          simpa [sub_eq_zero] using this
        · have := heig p.1 p.2 j hj
          rw [hT p j] at this
          simpa [sub_eq_zero] using this

end GlobalTheory.CompanionTheory.HeckeEigenspaces
end
end

namespace PositivityTheory.jumpWindows

theorem hecke_operator_of_automorphic : G0 → G2c :=
  GlobalTheory.CompanionTheory.HeckeEigenspaces.hecke_eigenfunctions_closed

end PositivityTheory.jumpWindows
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorsRegularRepresentation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RtMulApply
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.SmoReg

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem Rt_mul_apply (g h : GA E a) (φ : XB E a) : Rt E a (g * h) φ = Rt E a g (Rt E a h φ) := by
  rw [map_mul]; rfl

theorem polyBd_repI [_root_.NumberField.IsTotallyComplex E] : PolyBd (repI E a) :=
  ⟨1, 0, zero_le_one, fun g x => by
    have : ‖repI E a g x‖ = ‖x‖ := norm_Rt _ _
    simp [this]⟩

theorem conj_stab {G H X : Type} [Group G] [Group H] [TopologicalSpace H] [ContinuousMul H]
    (f : H →* G) (c : G →* H) (R : G → X → X) (hR : ∀ g h x, R (g * h) x = R g (R h x))
    (hf : ∀ u, c (f u) = u) (hcomm : ∀ g, c g = 1 → ∀ u, g * f u = f u * g)
    (g : G) (x : X) (hx : {u : H | R (f u) x = x} ∈ 𝓝 (1 : H)) :
    {u : H | R (f u) (R g x) = R g x} ∈ 𝓝 (1 : H) := by
  obtain ⟨k, hk⟩ : ∃ k, k = c g := ⟨_, rfl⟩
  have hg1 : c ((f k)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hf, ← hk, inv_mul_cancel]
  have hcont : Continuous fun u : H => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hat : Tendsto (fun u : H => k⁻¹ * u * k) (𝓝 1) (𝓝 1) := by
    have := hcont.tendsto 1
    simpa using this
  filter_upwards [hat hx] with u hu
  have key : f u * g = g * f (k⁻¹ * u * k) := by
    have h := hcomm _ hg1 (k⁻¹ * u * k)
    have e : f (k⁻¹ * u * k) = (f k)⁻¹ * f u * f k := by simp only [map_mul, map_inv]
    rw [e] at h ⊢
    have h2 := congrArg (f k * ·) h
    simpa only [mul_assoc, mul_inv_cancel_left] using h2.symm
  have hu' : R (f (k⁻¹ * u * k)) x = x := hu
  change R (f u) (R g x) = R g x
  rw [← hR, key, hR, hu']

theorem lev_Rt [_root_.NumberField.IsTotallyComplex E] (hfl : ∀ (w : Pl E) (u : GL (Fin a) (w.adicCompletion E)),
      cLoc w (fl a w u : GA E a) = u)
    (hcomm : ∀ (w : Pl E) (g : GA E a), cLoc w g = 1 → ∀ u, g * fl a w u = fl a w u * g)
    (S : Finset (Pl E)) (g : GA E a) (φ : XB E a) (hφ : Lev S φ) : Lev S (Rt E a g φ) := by
  intro w hw
  have hx := hφ w hw
  simp only [repW_apply] at hx ⊢
  exact conj_stab (fl a w) (cLoc w) (fun g x => Rt E a g x) Rt_mul_apply (hfl w) (hcomm w) g φ hx

theorem g5b : S2 → G0 → G5b := by
  intro hS2 hG0 E _ _ _ a S
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hG0 E a
  obtain ⟨-, -, -, hgrp, hT, -⟩ := hS2 _ a (XB E a) (repI E a) polyBd_repI
  refine ⟨?_, fun g φ hφ => lev_Rt h4 h8 S g φ hφ, ?_, ?_, ?_⟩
  · intro g φ hφ
    set y := cInf g with hy
    set gf : GA E a := (infGL E a y)⁻¹ * g with hgf
    have hgf1 : cInf gf = 1 := by
      rw [hgf, map_mul, map_inv, h1, ← hy, inv_mul_cancel]
    have hg : g = infGL E a y * gf := by rw [hgf, mul_inv_cancel_left]
    have hc : ∀ (z : GL (Fin a) (Cinf E)) (x : XB E a),
        Rt E a gf (repI E a z x) = repI E a z (Rt E a gf x) := by
      intro z x
      change Rt E a gf (Rt E a (infGL E a z) x) = Rt E a (infGL E a z) (Rt E a gf x)
      rw [← Rt_mul_apply, ← Rt_mul_apply, h7 gf hgf1 z]
    have := hgrp y _ (hT (Rt E a gf) hc φ hφ)
    have e : Rt E a g φ = repI E a y (Rt E a gf φ) := by
      change Rt E a g φ = Rt E a (infGL E a y) (Rt E a gf φ)
      rw [← Rt_mul_apply, ← hg]
    rw [e]
    exact this
  · intro c φ hφ w hw
    filter_upwards [hφ w hw] with u hu
    have hu' : repW a w u φ = φ := hu
    change repW a w u (c • φ) = c • φ
    rw [map_smul, hu']
  · intro φ φ' hφ hφ' w hw
    filter_upwards [hφ w hw, hφ' w hw] with u hu hu'
    have e : repW a w u φ = φ := hu
    have e' : repW a w u φ' = φ' := hu'
    change repW a w u (φ + φ') = φ + φ'
    rw [map_add (f := _), e, e']
  · intro w hw
    filter_upwards with u
    change repW a w u 0 = 0
    rw [map_zero]

end GlobalTheory.CompanionTheory.SmoReg

end
end

namespace PositivityTheory.jumpWindows

theorem smooth_vectors_regular_representation : S2 → G0 → G5b :=
  GlobalTheory.CompanionTheory.SmoReg.g5b

end PositivityTheory.jumpWindows
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CornerGLContinuity
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CornerGLContinuity

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem glmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : GL (Fin a) R) :
    GeneralLinearGroup.map (g.comp f) x = GeneralLinearGroup.map g (GeneralLinearGroup.map f x) := by
  ext i j; rfl

theorem cornerGL_blkU {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R) :
    cornerGL a s (blkU y) = blkU fun t => s (y t) := by
  apply Units.ext
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) +
    s ((1 + posM Subtype.val y) i j) = (1 + posM Subtype.val fun t => s (y t)) i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [posM, Matrix.add_apply, Matrix.sum_apply, map_add (f := _), map_sum, Matrix.single_apply,
    apply_ite s, map_zero]
  abel

theorem cLoc_eq (w : Pl E) (x : GA E a) :
    cLoc w x = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) :=
  glmap_comp _ _ x

theorem gf_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun w => ?_)
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x i j) (H w)

theorem locGL_mul_comm {v : Pl E} (h : GL (Fin a) (v.adicCompletion E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E v) k = 1) : locGL E a v h * k = k * locGL E a v h := by
  refine gf_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw
    rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hw, mul_one, one_mul]

open Classical in
theorem map_pLoc_prod (g : GA E a) (v : Pl E) : ∀ l : List (Pl E), l.Nodup →
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E a w (cLoc w g)).prod =
      if v ∈ l then cLoc v g else 1
  | [], _ => by simp
  | w :: l, h => by
    rw [List.map_cons, List.prod_cons, map_mul, map_pLoc_prod g v l (List.nodup_cons.1 h).2]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 h).1, mul_one]
      simp
    · rw [pLoc_locGL_of_ne hv, one_mul]
      simp [hv]

theorem continuous_glmap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL' {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

end CornerGLContinuity

open CornerGLContinuity in
theorem standard_stabiliser_bound : G0 := by
  intro E _ _ _ a
  have hpInf : Continuous (pInf E) :=
    (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        (continuous_apply w)).comp continuous_fst
  have hpLoc : ∀ w : Pl E, Continuous (pLoc E w) := fun w =>
    RestrictedProduct.continuous_eval (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) w
  have hfin : Continuous (finGL E a) :=
    continuous_cornerGL' _ (continuous_const.prodMk continuous_id :
      Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  have hinf : Continuous (infGL E a) :=
    continuous_cornerGL' _ ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine ⟨fun y => pInf_infGL y, fun w y => ?_, fun w u => pInf_finGL _, fun w u => ?_,
    fun w v u hvw => ?_, fun g h h1 h2 => ?_, fun g hg y => ?_, fun w g hg u => ?_,
    fun k y => cornerGL_blkU _ k y, fun w k y => ?_, fun S g => ?_, ?_, fun w => ?_, fun w => ?_, hinf⟩
  · rw [cLoc_eq, pFin_infGL, map_one]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL_of_ne hvw]
  · exact ga_ext h1 (gf_ext fun w => by rw [← cLoc_eq, ← cLoc_eq]; exact h2 w)
  · have hg' : GeneralLinearGroup.map (pInf E) g = 1 := hg
    exact ga_ext (by rw [map_mul, map_mul, hg', pInf_infGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, pFin_infGL, one_mul, mul_one])
  · have hg' : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) = 1 := by
      rw [← cLoc_eq]; exact hg
    exact ga_ext (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pInf_finGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pFin_finGL]; exact (locGL_mul_comm u hg').symm)
  · rw [fl, MonoidHom.comp_apply, locGL, cornerGL_blkU, finGL, cornerGL_blkU]
  · refine ⟨infGL E a (cInf g) * finGL E a (S.toList.map fun w => locGL E a w (cLoc w g)).prod, ?_, ?_, ?_⟩
    · change GeneralLinearGroup.map (pInf E) _ = _
      rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_pos (Finset.mem_toList.2 hw)]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_neg (fun h => hw (Finset.mem_toList.1 h))]
  · exact continuous_glmap _ hpInf
  · exact continuous_glmap _ ((hpLoc w).comp continuous_snd)
  · exact hfin.comp (continuous_cornerGL' _ (CuspSub.continuous_sLoc w))

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AveragingProjection
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AveragingProjection

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem avg_add (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    avg Γ (fun x => Φ x + Ψ x) = avg Γ Φ + avg Γ Ψ := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [h.choose_spec.2.2]; exact ENNReal.one_ne_top)
    exact integral_add (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))
  · simp

theorem avg_zero (Γ : AddSubgroup G) : avg Γ (fun _ => (0 : ℂ)) = 0 := by
  simpa using avg_const_mul Γ 0 (fun _ => (0 : ℂ))

theorem norm_avg_sub_le (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) {C : ℝ} (hC : 0 ≤ C) (hd : ∀ x, ‖Φ x - Ψ x‖ ≤ C) :
    ‖avg Γ Φ - avg Γ Ψ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have e1 : h.choose.1 h.choose.2 = 1 := h.choose_spec.2.2
    have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [e1]; exact ENNReal.one_ne_top)
    rw [← integral_sub (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))]
    calc _ ≤ C * h.choose.1.real h.choose.2 :=
          norm_setIntegral_le_of_norm_le_const (by rw [e1]; exact ENNReal.one_lt_top) fun x _ => hd x
      _ = C := by simp [Measure.real, e1]
  · simpa using hC

theorem continuous_avg {X : Type} [TopologicalSpace X] (Γ : AddSubgroup G) {u : G → X} (hu : Continuous u) :
    Continuous fun φ : X →ᵇ ℂ => avg Γ (fun x => φ (u x)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun φ ψ => ?_).continuous
  rw [dist_eq_norm, NNReal.coe_one, one_mul]
  exact norm_avg_sub_le Γ (φ.continuous.comp hu) (ψ.continuous.comp hu) (B := max ‖φ‖ ‖ψ‖)
    (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
    (fun x => (ψ.norm_coe_le_norm _).trans (le_max_right _ _)) dist_nonneg
    (fun x => by rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist (f := φ) (g := ψ) (u x))

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

def P (ψ : AddChar (Ad E) ℂ) (φ : XB E a) : Prop :=
  Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g

theorem P_zero : P ψ (0 : XB E a) := by
  refine ⟨⟨(0 : XB E a).continuous, fun γ _ g => rfl, fun k _ y g => by simp, fun r _ _ g => ?_⟩, fun γ g => rfl⟩
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  exact avg_zero _

theorem P_add {φ φ' : XB E a} (h : P ψ φ) (h' : P ψ φ') : P ψ (φ + φ') := by
  refine ⟨⟨(φ + φ').continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.left γ hγ g, h'.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.law k hk y g, h'.1.law k hk y g, mul_add]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    rw [avg_add _ (Φ := fun x => φ (blkU x * g)) (Ψ := fun x => φ' (blkU x * g)) (φ.continuous.comp ((continuous_posU _).mul continuous_const))
      (φ'.continuous.comp ((continuous_posU _).mul continuous_const)) (B := max ‖φ‖ ‖φ'‖)
      (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
      (fun x => (φ'.norm_coe_le_norm _).trans (le_max_right _ _)),
      h.1.van r hr hr' g, h'.1.van r hr hr' g, add_zero]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.2 γ g, h'.2 γ g]

theorem P_smul (c : ℂ) {φ : XB E a} (h : P ψ φ) : P ψ (c • φ) := by
  refine ⟨⟨(c • φ).continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, h.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul, h.1.law k hk y g]
    ring
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [avg_const_mul, h.1.van r hr hr' g, mul_zero]
  · simp only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, h.2 γ g]

theorem P_rt (k : GA E a) {φ : XB E a} (h : P ψ φ) : P ψ (Rt E a k φ) := by
  refine ⟨⟨(Rt E a k φ).continuous, fun γ hγ g => ?_, fun j hj y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [Rt_apply, mul_assoc]; exact h.1.left γ hγ (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.law j hj y (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.van r hr hr' (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.2 γ (g * k)

theorem isClosed_P : IsClosed {φ : XB E a | P ψ φ} := by
  have key : {φ : XB E a | P ψ φ} =
      (⋂ (γ : GL (Fin a) E), ⋂ (g : GA E a), {φ : XB E a | φ (ratGL E a γ * g) = φ g}) ∩
      ((⋂ (k : ℕ), ⋂ (_ : a - 1 < k), ⋂ (y : UnipotentBlockColumnIndex a k k → Ad E), ⋂ (g : GA E a),
          {φ : XB E a | φ (blkU y * g) = ψ (dot (eLast a k) y) * φ g}) ∩
        (⋂ (r : ℕ), ⋂ (_ : 0 < r), ⋂ (_ : r ≤ a - 1), ⋂ (g : GA E a),
          {φ : XB E a | avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => φ (blkU x * g)) = 0})) := by
    ext φ
    simp only [P, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hG, hl⟩
      exact ⟨hl, hG.law, hG.van⟩
    · rintro ⟨hl, hlaw, hvan⟩
      exact ⟨⟨φ.continuous, fun γ _ g => hl γ g, hlaw, hvan⟩, hl⟩
  rw [key]
  refine (isClosed_iInter fun γ => isClosed_iInter fun g => ?_).inter
    ((isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun y => isClosed_iInter fun g => ?_).inter
      (isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun g => ?_))
  · exact isClosed_eq (continuous_eval_const _) (continuous_eval_const _)
  · exact isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const _))
  · exact isClosed_eq (continuous_avg _ ((continuous_posU _).mul continuous_const)) continuous_const

end AveragingProjection

open AveragingProjection in
theorem averaging_projection_linear : G2a := by
  intro E _ _ _ a ψ _
  refine ⟨{ carrier := {φ | P ψ φ}, add_mem' := P_add, zero_mem' := P_zero, smul_mem' := P_smul },
    isClosed_P, fun g φ h => P_rt g h, fun φ => Iff.rfl⟩

end PositivityTheory.jumpWindows

end
end
