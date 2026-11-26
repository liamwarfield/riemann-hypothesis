module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowTwoPowSubOneGe
namespace GlobalTheory.PowerTwoNormLowerBound

theorem norm_pow_two_pow_sub_one_ge {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < (1 / 2 : ℝ)) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw1 : ‖w - 1‖ < 1 / 2 := h _
    have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
      have := norm_sub_le (w + 1) (w - 1)
      rw [← e] at this
      have n2 : ‖(2 : ℂ)‖ = 2 := by simp
      linarith
    have eq : z ^ (2 ^ (k + 1)) - 1 = (w - 1) * (w + 1) := by
      rw [hw, pow_succ, pow_mul]; ring
    rw [eq, norm_mul, pow_succ]
    have h0 : 0 ≤ ‖z - 1‖ := norm_nonneg _
    have h0' : 0 ≤ (3 / 2 : ℝ) ^ k := by positivity
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : (1 / 2 : ℝ) < (3 / 2 : ℝ) ^ k * ‖z - 1‖ := (div_lt_iff₀ hpos).mp hk
  have h2 := norm_pow_two_pow_sub_one_ge h k
  have h3 := h (2 ^ k)
  linarith

end GlobalTheory.PowerTwoNormLowerBound
end

noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise

namespace GlobalTheory.WeilM

theorem eq_zero_of_mul_invariant {X : Type} [TopologicalSpace X] (l : (X → ℂ) →ₗ[ℂ] ℂ) (S : Set (X → ℂ))
    (hS : ∀ f ∈ S, IsLocallyConstant f) (hl : ∀ f ∈ S, ∀ φ ∈ SB X, l (f * φ) = l φ)
    {φ : X → ℂ} (hφ : φ ∈ SB X) (h : ∀ x, φ x ≠ 0 → ∃ f ∈ S, f x ≠ 1) : l φ = 0 := by
  have hind : ∀ U : Set X, IsClopen U → ∀ φ ∈ SB X, U.indicator φ ∈ SB X := by
    intro U hU φ hφ
    have : U.indicator φ = U.indicator 1 * φ := by
      funext x; by_cases hx : x ∈ U <;> simp [hx]
    rw [this]
    exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩
  have hsupp : IsClopen (Function.support φ) := (hφ.1.isClopen_fiber 0).compl
  have hc : IsCompact (Function.support φ) := by
    have := hφ.2
    rwa [HasCompactSupport, tsupport, hsupp.isClosed.closure_eq] at this
  have key : ∃ U : Set X, IsClopen U ∧ Function.support φ ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0 := by
    refine hc.induction_on (p := fun s => ∃ U : Set X, IsClopen U ∧ s ⊆ U ∧
      ∀ φ' ∈ SB X, Function.support φ' ⊆ U → l φ' = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, le_rfl, fun φ' _ h0 => ?_⟩
      rw [Set.subset_empty_iff, Function.support_eq_empty_iff] at h0
      rw [h0, map_zero]
    · rintro s t hst ⟨U, hU, htU, h'⟩
      exact ⟨U, hU, hst.trans htU, h'⟩
    · rintro s t ⟨U, hU, hsU, h1⟩ ⟨V, hV, htV, h2⟩
      refine ⟨U ∪ V, hU.union hV, Set.union_subset_union hsU htV, fun φ' hφ' hs => ?_⟩
      rw [← Set.indicator_self_add_compl U φ', map_add (f := _), h1 _ (hind U hU _ hφ') Set.support_indicator_subset,
        h2 _ (hind _ hU.compl _ hφ'), add_zero]
      rw [Set.support_indicator]
      rintro x ⟨hx, hx'⟩
      exact (hs hx').resolve_left hx
    · intro x hx
      obtain ⟨f, hf, hfx⟩ := h x hx
      have hU := (hS f hf).isClopen_fiber (f x)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hU.isOpen.mem_nhds rfl), _, hU, le_rfl, fun φ' hφ' hs => ?_⟩
      have h1 : f * φ' = f x • φ' := by
        funext y
        by_cases hy : φ' y = 0
        · simp [hy]
        · have : f y = f x := hs hy
          simp [this]
      have h2 := hl f hf φ' hφ'
      rw [h1, map_smul, smul_eq_mul] at h2
      have h3 : (f x - 1) * l φ' = 0 := by rw [sub_mul, h2, one_mul, sub_self]
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hfx)
  obtain ⟨U, -, hU, h'⟩ := key
  exact h' φ hφ hU

theorem eq_one_of_forall_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerTwoNormLowerBound.main
  | exact _root_.GlobalTheory.PowerTwoNormLowerBound.main
  | (apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerTwoNormLowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerTwoNormLowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerTwoNormLowerBound.main ..)

theorem isLocallyConstant_addChar {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V]
    (ψ : AddChar V ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have h0 : {x | ‖ψ x - 1‖ < 1 / 2} ∈ 𝓝 (0 : V) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
  have h1 : ∀ x ∈ K, ψ x = 1 := fun x hx => eq_one_of_forall_pow_near fun n => by
    rw [← AddChar.map_nsmul_eq_pow]
    exact hK (nsmul_mem hx n)
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have : (fun z => -x + z) ⁻¹' (K : Set V) ∈ 𝓝 x :=
    (K.isOpen.preimage (by fun_prop)).mem_nhds (by simp)
  filter_upwards [this] with z hz
  have h2 : z = x + (-x + z) := by abel
  rw [h2, AddChar.map_add_eq_mul, h1 _ hz, mul_one]

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nonarch_field : NonarchimedeanAddGroup F where
  is_nonarchimedean U hU := by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hU
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩, SplitWeil.neg_mem_cball⟩,
      SplitWeil.isOpen_cball s⟩, hs⟩

theorem nonarch_pi (κ : Type) [Fintype κ] : NonarchimedeanAddGroup (κ → F) where
  is_nonarchimedean U hU := by
    haveI := nonarch_field F
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := F) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup F),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

section Cov

variable {F} [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ) (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) = Measure.pi fun _ : κ => ν := by
  haveI := SplitWeil.secondCountable F
  haveI := SplitWeil.t2Space F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hM : M.det ≠ 0 := hu ▸ u.ne_zero
  revert u
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD u hu
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [det_diagonal] at hD hu
    have A : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have hu' : u = ∏ i, Units.mk0 (D i) (A i) := Units.ext (by simp [hu])
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => (Units.mk0 (D i) (A i))⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := Units.mk0 (D i) (A i))).symm
    rw [this, Measure.pi_pi, hu', map_prod, ENNReal.ofNNReal_finsetProd, smul_eq_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro t u hu
    have hu' : u = 1 := Units.ext (by simp [hu])
    rw [hu', map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    cases t with | mk t_i t_j t_hij t_c =>
    simp [transvection, add_mulVec, single_mulVec, t_hij.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x t_i xᵢ)]
  · intro A B hA hB IHA IHB u hu
    have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := Units.ext (by simp [hu])
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [hu', map_mul, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _), ← Measure.map_smul,
      IHB _ rfl, IHA _ rfl]
    exact (hm A).aemeasurable

theorem integral_comp_mulVec (g : GL κ F) (f : (κ → F) → ℂ) :
    ((distribHaarChar F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
      ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ : κ => ν) = ∫ x, f x ∂(Measure.pi fun _ : κ => ν) := by
  haveI := SplitWeil.secondCountable F
  have hm : ∀ A : Matrix κ κ F, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  let e : (κ → F) ≃ᵐ (κ → F) :=
    { toFun := g.val.mulVec, invFun := (g⁻¹).val.mulVec
      left_inv := fun x => by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := fun x => by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      measurable_toFun := hm _, measurable_invFun := hm _ }
  conv_rhs => rw [← smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl, integral_smul_measure]
  rw [show g.val.mulVec = e from rfl, integral_map_equiv]
  simp

end Cov

end GlobalTheory.WeilM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
open scoped TensorProduct
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginCut

def IsZTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) : Prop :=
  Module.Finite B D ∧ Module.Projective B D ∧ Module.FaithfullyFlat B D ∧
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)))

def originIdeal (T : Type) [CommRing T] [IsLocalRing T] : Ideal (Polynomial T) :=
  (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X}

end GlobalTheory.KeyOriginCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.WeilCont

variable (F : Type) [Field F] [NumberField F] {κ : Type}

def adeleJoin (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem pureA_adeleJoin (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (adeleJoin F x y) = f x * g y := by
  simp only [GlobalTheory.WeilM.pureA, adeleJoin, RingEquiv.apply_symm_apply]

theorem exists_slice [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ x, s x = Φ (adeleJoin F x y) := by
  unfold GlobalTheory.WeilM.schA at hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    exact ⟨g y • f, fun x => by rw [smul_apply, pureA_adeleJoin, smul_eq_mul, mul_comm]⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    exact ⟨s1 + s2, fun x => by rw [add_apply, hs1, hs2]; rfl⟩
  | smul c Φ _ h =>
    obtain ⟨s, hs⟩ := h
    exact ⟨c • s, fun x => by rw [smul_apply, hs]; rfl⟩

theorem isContOn_of_local [Fintype κ] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] {G : Type} [Group G] [TopologicalSpace G]
    {om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)}
    (hfin : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ p0 : G, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (hsl : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      ∃ s : G → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Continuous s ∧ ∀ p x, s p x = om p Φ (adeleJoin F x y)) :
    GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass F) om := by
  intro l hl φ hφ
  change φ ∈ GlobalTheory.WeilM.schA F κ at hφ
  change ∀ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (GlobalTheory.WeilM.pureA F f g) = T f at hl
  rw [continuous_iff_continuousAt]
  intro p0
  obtain ⟨N, hN, m, g, y, hgSB, hgy, hrep⟩ := hfin φ hφ p0
  choose T hT using fun i => hl (g i) (hgSB i)
  choose s hs hsx using fun j => hsl φ hφ (y j)
  have hcont : Continuous fun p => ∑ i, T i (s i p) :=
    continuous_finsetSum _ (fun i _ => (T i).continuous.comp (hs i))
  refine hcont.continuousAt.congr ?_
  filter_upwards [hN] with p hp
  obtain ⟨f, hf⟩ := hrep p hp
  have hfs : ∀ j, f j = s j p := by
    intro j
    ext x
    rw [hsx, hf, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [pureA_adeleJoin, hgy j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [pureA_adeleJoin, hgy i j, if_neg hij, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hT, hfs])

end GlobalTheory.WeilCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
noncomputable section

open MeasureTheory
open scoped ENNReal Matrix

namespace GlobalTheory.WeilTr

open GlobalTheory.WeilM

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]

def trRep {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ)) :
    G →* Module.End ℂ ((κ → R) → ℂ) where
  toFun g := T.toLinearMap ∘ₗ om g ∘ₗ T.symm.toLinearMap
  map_one' := by
    ext φ x
    simp
  map_mul' g h := by
    ext φ x
    simp

theorem trRep_apply {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ))
    (g : G) (φ : (κ → R) → ℂ) : trRep T om g φ = T (om g (T.symm φ)) := rfl

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}

def IsGoodInt [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (d d₁ : Darboux B κ)
    (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  (∀ φ, φ ∈ C.sp κ ↔ T φ ∈ C.sp κ) ∧
  (∀ w, ∀ φ ∈ C.sp κ, T (d.rho ψ w φ) = d₁.rho ψ w (T φ)) ∧
  (∀ l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ, l ∈ C.adm κ ↔ l ∘ₗ T.toLinearMap ∈ C.adm κ) ∧
  ∀ μ : @Measure (κ → R) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ c : ℝ≥0∞, ∀ φ ∈ C.sp κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

section Dbl

variable {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

def HasDbl [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  ∀ dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ), IsDblCoord c ξ JA JB d dd →
    ∃ (dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (Td : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ))
      (S : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)), IsDblCoord c ξ JA JB d₁ dd₁ ∧ IsGoodInt C ψ dd dd₁ Td ∧
      (∀ φ, φ ∈ C.sp κ ↔ S φ ∈ C.sp κ) ∧
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, Td (boxFun φ₁ φ₂) = boxFun (T φ₁) (S φ₂)

end Dbl

theorem isUSplitting_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ} {d d₁ : Darboux B κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUSplitting C ψ d act om) : IsUSplitting C ψ d₁ act (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  have hrho : ∀ w, ∀ φ ∈ C.sp κ, T.symm (d₁.rho ψ w φ) = d.rho ψ w (T.symm φ) := fun w φ hφ => by
    rw [LinearEquiv.symm_apply_eq, hheis w _ (hinv φ hφ), LinearEquiv.apply_symm_apply]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ hμ g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [trRep_apply]
    exact (hsp _).1 (h.pres g _ (hinv φ hφ))
  · rw [trRep_apply, trRep_apply, hrho w φ hφ, h.impl g w _ (hinv φ hφ), hheis _ _ (h.pres g _ (hinv φ hφ))]
  · have h1 : l ∘ₗ T.toLinearMap ∈ C.adm κ := (hadm l).1 hl
    have h2 := h.adm g _ h1
    have h3 : (l ∘ₗ T.toLinearMap ∘ₗ om g) ∘ₗ T.symm.toLinearMap ∈ C.adm κ := by
      rw [hadm]
      convert h2 using 1
      ext φ
      simp
    convert h3 using 1
    ext φ
    simp [trRep_apply]
  · obtain ⟨c, hc⟩ := hunit μ hμ
    rw [trRep_apply, hc _ (h.pres g _ (hinv φ hφ)), h.unit μ hμ g _ (hinv φ hφ)]
    conv_rhs => rw [← LinearEquiv.apply_symm_apply T φ]
    rw [hc _ (hinv φ hφ)]
  · have := h.cont _ ((hadm l).1 hl) _ (hinv φ hφ)
    simpa [trRep_apply] using this

theorem siegelRule_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T)
    {χ : Eˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : SiegelRule c C ψ ξ JA JB d χ Cy om) : SiegelRule c C ψ ξ JA JB d₁ χ Cy (trRep T om) := by
  obtain ⟨hsp, hheis, hadm, -⟩ := hT
  have hinv : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hsp _).2 (by simpa using hφ)
  intro l hl hinvl p t hpt φ hφ
  have key := h (l ∘ₗ T.toLinearMap) ((hadm l).1 hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hheis _ _ hφ', hinvl z _ ((hsp _).1 hφ')]) p t hpt (T.symm φ) (hinv φ hφ)
  simpa [trRep_apply] using key

theorem isUWeilB_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsUWeilB c C ψ ξ JA JB d₁ χ (trRep T om) := by
  obtain ⟨hs, dd, omd, hdd, ⟨hL, hsd, hsg⟩, hbox⟩ := h
  obtain ⟨dd₁, Td, S, hdd₁, hTd, hS, hTbox⟩ := hD dd hdd
  have hinvT : ∀ φ ∈ C.sp κ, T.symm φ ∈ C.sp κ := fun φ hφ => (hT.1 _).2 (by simpa using hφ)
  have hinvS : ∀ φ ∈ C.sp κ, S.symm φ ∈ C.sp κ := fun φ hφ => (hS _).2 (by simpa using hφ)
  refine ⟨isUSplitting_trRep hT hs, dd₁, trRep Td omd, hdd₁, ⟨hL, isUSplitting_trRep hTd hsd, siegelRule_trRep hTd hsg⟩, fun g gd hg φ₁ hφ₁ φ₂ hφ₂ => ?_⟩
  have hb : Td.symm (boxFun φ₁ φ₂) = boxFun (T.symm φ₁) (S.symm φ₂) := by
    rw [LinearEquiv.symm_apply_eq, hTbox _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  rw [trRep_apply, hb, hbox g gd hg _ (hinvT φ₁ hφ₁) _ (hinvS φ₂ hφ₂),
    hTbox _ (hs.pres g _ (hinvT φ₁ hφ₁)) _ (hinvS φ₂ hφ₂), LinearEquiv.apply_symm_apply, trRep_apply]

theorem symp_transpose {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    symp c ξ JB JA x y = symp c ξ JA JB xᵀ yᵀ := by
  unfold symp hTens
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

def transpCoord {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [symp_transpose, d.form]
    rfl

theorem transpCoord_e {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) (x : Matrix α β E) : (transpCoord d).e xᵀ = d.e x := rfl

theorem isUWeilPair_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    (hD' : ∀ d' d₁' : Darboux (symp c ξ JB JA) κ, (∀ x : Matrix α β E, d'.e xᵀ = d.e x) → (∀ x : Matrix α β E, d₁'.e xᵀ = d₁.e x) →
      HasDbl c C ψ ξ JB JA d' d₁' T)
    {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsUWeilPair c C ψ ξ JA JB d₁ χA χB (trRep T om) := by
  have hsplit := isUSplitting_trRep hT h.isUSplitting
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  have hT' : IsGoodInt C ψ d' (transpCoord d₁) T := by
    obtain ⟨h1, h2, h3, h4⟩ := hT
    refine ⟨h1, fun w φ hφ => ?_, h3, h4⟩
    have e1 : d'.e w = d.e wᵀ := by rw [← hd', Matrix.transpose_transpose]
    have e2 : (transpCoord d₁).e w = d₁.e wᵀ := by rw [← transpCoord_e d₁ wᵀ, Matrix.transpose_transpose]
    have := h2 wᵀ φ hφ
    simp only [Darboux.rho] at this ⊢
    rw [e1, e2, this]
  exact ⟨isUWeilB_trRep hT hD hB, ⟨transpCoord d₁, transpCoord_e d₁, isUWeilB_trRep hT' (hD' d' _ hd' (transpCoord_e d₁)) hA⟩, hsplit.cont⟩

end GlobalTheory.WeilTr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
noncomputable section

open Matrix
open scoped NNReal Kronecker

namespace GlobalTheory.WeilM

variable {R : Type} [CommRing R]

theorem schr_schr [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * (mul_invOf_self (2 : R))


variable {α β κ : Type}

def flat (σ : κ ≃ α × β) : Matrix α β R ≃ₗ[R] (κ → R) where
  toFun X k := X (σ k).1 (σ k).2
  invFun u := of fun i j => u (σ.symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; simp
  right_inv u := by ext k; simp

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]




def dblNum (σ : κ ≃ α × β) : κ ⊕ κ ≃ α × (β ⊕ β) := (σ.sumCongr σ).trans (Equiv.prodSumDistrib α β β).symm

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_fromCols (σ : κ ≃ α × β) (X Y : Matrix α β R) :
    flat (dblNum σ) (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := by
  funext k
  cases k <;> rfl

end GlobalTheory.WeilM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.Act

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) :
    _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp [map_mul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.redGL_one (N : ℕ) : _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_vmul {N : ℕ} (x : Fin 2 → ZMod N) (α β : GL (Fin 2) (ZMod N)) :
    _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β) := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp [Matrix.vecMul_vecMul]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.vmul_one {N : ℕ} (x : Fin 2 → ZMod N) : _root_.GlobalTheory.WpFam.vmul x 1 = x := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp

theorem isRAct_gact (N : ℕ) (D : GL (Fin 2) (ZMod N)) : IsRAct (gact N D) := by
  constructor
  · intro x; simp [gact, redGL_one]
  · intro x γ δ; simp only [gact, redGL_mul]; group


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.Act.rightActions : ∀ (N : ℕ), _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.vact N) ∧ (∀ D, _root_.GlobalTheory.QFam.IsRAct (_root_.GlobalTheory.WpFam.gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.WpFam.vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, _root_.GlobalTheory.WpFam.vmul (M • x) α = M • _root_.GlobalTheory.WpFam.vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ) ∧ _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  intro N
  refine ⟨?_, ?_, _root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.vmul_one, ?_, ?_, ?_,
    _root_.GlobalTheory.WpFam.Act.redGL_mul N, _root_.GlobalTheory.WpFam.Act.redGL_one N⟩
  · refine ⟨fun x => ?_, fun x γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one, _root_.GlobalTheory.WpFam.Act.vmul_one]
    · unfold _root_.GlobalTheory.WpFam.vact
      rw [_root_.GlobalTheory.WpFam.Act.vmul_vmul, _root_.GlobalTheory.WpFam.Act.redGL_mul]
  · intro D
    refine ⟨fun α => ?_, fun α γ δ => ?_⟩
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_one]
      group
    · unfold _root_.GlobalTheory.WpFam.gact
      rw [_root_.GlobalTheory.WpFam.Act.redGL_mul]
      group
  · intro x α
    constructor
    · intro h
      have key := congrArg (fun y => _root_.GlobalTheory.WpFam.vmul y α⁻¹) h
      simp only [_root_.GlobalTheory.WpFam.Act.vmul_vmul, mul_inv_cancel, _root_.GlobalTheory.WpFam.Act.vmul_one] at key
      rw [key]
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
    · rintro rfl
      unfold _root_.GlobalTheory.WpFam.vmul
      simp
  · intro M x α
    unfold _root_.GlobalTheory.WpFam.vmul
    rw [Matrix.smul_vecMul]
  · intro x a
    unfold _root_.GlobalTheory.WpFam.vmul _root_.GlobalTheory.WpFam.dg
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

end GlobalTheory.WpFam.Act
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActionsStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions : ∀ (N : ℕ), IsRAct (vact N) ∧ (∀ D, IsRAct (gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, vmul (vmul x α) β = vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, vmul (M • x) α = M • vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), vmul x (dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, redGL N (γ * δ) = redGL N γ * redGL N δ) ∧ redGL N 1 = 1 := by
  first | exact @GlobalTheory.WpFam.Act.rightActions | exact GlobalTheory.WpFam.Act.rightActions | (intros; apply GlobalTheory.WpFam.Act.rightActions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory.UCls
open scoped TensorProduct
open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isKM_mul {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  obtain ⟨⟨hd', hh'⟩, h2', h3'⟩ := hk'
  refine ⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hh, hh']
  · obtain ⟨y2, hy2, e2⟩ := h2' x hx
    have hx' : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y2 := by rw [← e2]; abel
      rw [this]; exact add_mem hx (nsmul_mem hy2 _)
    obtain ⟨y1, hy1, e1⟩ := h2 _ hx'
    refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e1, ← e2]; abel
  · obtain ⟨y1, hy1, e1⟩ := h3 x hx
    obtain ⟨y2, hy2, e2⟩ := h3' y1 hy1
    exact ⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩

theorem isKM_inv {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    IsKM c G L M k⁻¹ := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  have hkk : k * k⁻¹ = 1 := mul_nonsing_inv k hd
  have hkk' : k⁻¹ * k = 1 := nonsing_inv_mul k hd
  have hmem : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, e⟩ := h2 x hx
    have : k *ᵥ x = x + M • y := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hy _)
  refine ⟨⟨?_, fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [det_nonsing_inv]; exact hd.ringInverse
  · rw [← hh, mulVec_mulVec, mulVec_mulVec, hkk, one_mulVec, one_mulVec]
  · obtain ⟨y, hy, e⟩ := h3 x hx
    obtain ⟨z, hz, ez⟩ := h2 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    have : k⁻¹ *ᵥ x = y := by rw [← e, mulVec_mulVec, hkk', one_mulVec]
    rw [this, ← e, smul_neg, ← ez]; abel
  · exact ⟨k *ᵥ x, hmem x hx, by rw [mulVec_mulVec, hkk', one_mulVec]⟩

theorem tEquiv_refl (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t : RA F E) :
    TEquiv c G L M t t :=
  ⟨1, by simp, 1, isKM_one c G L M, by simp [Algebra.TensorProduct.one_def.symm]⟩

theorem tEquiv_symm {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' : RA F E}
    (h : TEquiv c G L M t t') : TEquiv c G L M t' t := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  refine ⟨u⁻¹, by rw [map_inv₀, ← mul_inv, hu, inv_one], k⁻¹, isKM_inv hk, ?_⟩
  have hd : IsUnit k.det := hk.1.1
  have e1 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu0, Algebra.TensorProduct.one_def]
  have e2 : k.det * k⁻¹.det = 1 := by rw [det_nonsing_inv, Ring.mul_inverse_cancel _ hd]
  calc t = (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u)) * t * (k.det * k⁻¹.det) := by
        rw [e1, e2, one_mul, mul_one]
    _ = _ := by ring

theorem tEquiv_trans {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ} {t t' t'' : RA F E}
    (h : TEquiv c G L M t t') (h' : TEquiv c G L M t' t'') : TEquiv c G L M t t'' := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  obtain ⟨u', hu', k', hk', rfl⟩ := h'
  refine ⟨u' * u, ?_, k * k', isKM_mul hk hk', ?_⟩
  · rw [map_mul]
    calc u' * u * (c u' * c u) = (u' * c u') * (u * c u) := by ring
      _ = 1 := by rw [hu, hu', one_mul]
  · have e : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (u' * u)) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u') * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] u) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [det_mul, e]; ring

theorem tEquiv_of_eqvGen {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    (a b : {t : RA F E // IsTA c t})
    (h : Relation.EqvGen (fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1) a b) :
    TEquiv c G L M a.1 b.1 :=
  (Equivalence.eqvGen_iff (r := fun a b : {t : RA F E // IsTA c t} => TEquiv c G L M a.1 b.1)
    ⟨fun a => tEquiv_refl c G L M a.1, fun h => tEquiv_symm h, fun h h' => tEquiv_trans h h'⟩).1 h

end GlobalTheory.UCls
end

theorem GlobalTheory.UCls.torus_eqvGen_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 :=
  by intro E _ _ _ r M G L a b h; exact GlobalTheory.UCls.tEquiv_of_eqvGen a b h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRelStatement
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivalence_generated_torus_rel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t}), Relation.EqvGen (fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G L M a.1 b.1) a b → TEquiv (IsCMField.complexConj E) G L M a.1 b.1 := by
  first | exact @GlobalTheory.UCls.torus_eqvGen_main | exact GlobalTheory.UCls.torus_eqvGen_main | (intros; apply GlobalTheory.UCls.torus_eqvGen_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory
open IsDedekindDomain
open scoped TensorProduct

theorem isTA_det_of_isUA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {r : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA F E))
    (hG : G.det ≠ 0) (hg : IsUA c G g) : IsTA c g.det := by
  set σ := sg (FiniteAdeleRing (𝓞 F) F) c with hσ
  set G' : Matrix (Fin r) (Fin r) (RA F E) := G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) with hG'
  have hM : gᵀ * G' * g.map σ = G' := by
    ext a b
    have h := hg.2 (Pi.single a 1) (Pi.single b 1)
    simp only [hermA, Matrix.mulVec_single_one] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    convert h using 1
    · rfl
    · simp [G', Pi.single_apply, apply_ite σ]
  have hdet := congrArg Matrix.det hM
  have hs : (g.map σ).det = σ g.det := by
    rw [show g.map σ = (σ : RA F E →+* RA F E).mapMatrix g from rfl, ← RingHom.map_det]; rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs] at hdet
  have hG'det : G'.det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det := by
    rw [hG', show G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) =
      ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) : E →+* RA F E).mapMatrix G from rfl,
      ← RingHom.map_det]; rfl
  have hu : IsUnit G'.det := by
    rw [hG'det]
    refine IsUnit.of_mul_eq_one ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det⁻¹) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hG]
    rfl
  unfold IsTA
  have : g.det * σ g.det * G'.det = 1 * G'.det := by
    rw [one_mul]; convert hdet using 1; ring
  exact hu.mul_right_cancel this

theorem unitary_det_isTA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det :=
  fun _ _ _ _ _ _ _ hG hg => isTA_det_of_isUA _ _ _ hG hg

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTAStatement
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTA_conj_det_of_isUA_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det := by
  first | exact @GlobalTheory.unitary_det_isTA | exact GlobalTheory.unitary_det_isTA | (intros; apply GlobalTheory.unitary_det_isTA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFun
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFun
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem gal_id_eq {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem hcTw_twisted_class {F : Type} [Field F] (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x y : GL (Fin n) F) :
    hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x := by
  unfold hcTw
  congr 1
  have h : ∀ z : GL (Fin n) F, z⁻¹ * (y⁻¹ * x * gal t n y) * gal t n z
      = (y * z)⁻¹ * x * gal t n (y * z) := by
    intro z; simp only [map_mul, mul_inv_rev]; group
  simp_rw [h]
  exact finsum_comp_equiv (Equiv.mulLeft y)
    (f := fun w : GL (Fin n) F => if InPar a (w⁻¹ * x * gal t n w) then
      α (tlG a (w⁻¹ * x * gal t n w)) * β (brG a b (w⁻¹ * x * gal t n w)) else 0)

theorem hc_isCl {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    IsCl (hc a b α β n) := by
  intro x y
  have := hcTw_twisted_class (RingHom.id F) a b n α β x y
  rw [gal_id_eq] at this
  exact this

theorem psiG_isCl {F : Type} [Field F] (S : F[X] → ℂ) (n : ℕ) : IsCl (psiG S n) := by
  intro x y
  unfold psiG
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    LinearEquiv.ofLinear (Matrix.toLin' ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (Matrix.toLin' ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
  have he : e.conj (Matrix.toLin' ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      Matrix.toLin' (((y⁻¹ * x * y : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) := by
    rw [LinearEquiv.conj_apply, Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    rfl
  rw [← he, psi_conj]

theorem chG_isCl {F : Type} [Field F] (S : F[X] → ℂ) (n : ℕ) : IsCl (chG S n) := by
  intro x y
  unfold chG
  congr 1
  have := Matrix.charpoly_units_conj (y⁻¹ : GL (Fin n) F) (x : Matrix (Fin n) (Fin n) F)
  rw [← this, Units.val_mul, Units.val_mul]
  congr 2
  rw [← Matrix.coe_units_inv, inv_inv]

theorem twisted_class_main : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  intro F _ _ t a b n α β
  exact ⟨fun x y => hcTw_twisted_class t a b n α β x y, hc_isCl a b n α β,
    fun S => ⟨psiG_isCl S n, chG_isCl S n⟩⟩

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  first | (exact @GlobalTheory.Shin.twisted_class_main) | (exact GlobalTheory.Shin.twisted_class_main) | (intros; apply GlobalTheory.Shin.twisted_class_main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

def chartHom {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] (u : Sp S ⟶ Y)
    (h : u ⁻¹ᵁ V = ⊤) : Γ(Y, V) →+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (u.appLE V ⊤ h.ge).hom

def IsCombIn {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) : Prop :=
  ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw : ∀ i, w i ⁻¹ᵁ V = ⊤), ∀ x : Γ(Y, V),
    chartHom V c hc x = chartHom V u hu x + ∑ i, a i * (chartHom V (w i) (hw i) x - chartHom V u hu x)

end GlobalTheory.SecGlue
end
end
