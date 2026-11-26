module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LiftFactorization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bridge

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PRankOne
namespace UpperTheory.V.Z.Mult.Pi

private lemma trace_idem {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (f : Module.End ℂ Y) (hf : f * f = f) (hx : ∀ x, ∃ c : ℂ, f * x * f = c • f) (h0 : f ≠ 0) :
    LinearMap.trace ℂ Y f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (LinearMap.ext h)
  have hidem : ∀ v, f (f v) = f v := fun v => by
    have := congrArg (fun g : Module.End ℂ Y => g v) hf
    simpa [Module.End.mul_apply] using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ (f y) = 1 := by
    have h1 : ¬ ∀ φ : Module.Dual ℂ Y, φ (f y) = 0 := fun h =>
      hy ((Module.forall_dual_apply_eq_zero_iff ℂ (f y)).1 h)
    push_neg at h1
    obtain ⟨ψ, hψ⟩ := h1
    refine ⟨(ψ (f y))⁻¹ • ψ, ?_⟩
    simp [hψ]
  have hr : LinearMap.range f = Submodule.span ℂ {f y} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := hx (φ.smulRight v)
      have h2 := congrArg (fun g : Module.End ℂ Y => g (f y)) hc
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, hidem, hφ,
        map_smul, one_smul] at h2
      exact Submodule.mem_span_singleton.2 ⟨c, h2.symm⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨y, rfl⟩
  have hp : LinearMap.IsProj (LinearMap.range f) f :=
    ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hidem v⟩
  rw [hp.trace, hr, finrank_span_singleton hy]
  simp

theorem rankOne_pf : RankOne := by
  intro Y _ _ _ f A hf hA hc hx
  by_cases h0 : f = 0
  · left
    simp [h0]
  right
  obtain ⟨c, hcA⟩ := hx A
  have hfA : f * A = c • f := by
    calc f * A = f * f * A := by rw [hf]
      _ = f * (f * A) := mul_assoc _ _ _
      _ = f * (A * f) := by rw [hc]
      _ = f * A * f := (mul_assoc _ _ _).symm
      _ = c • f := hcA
  have hsq : (c * c) • f = f := by
    calc (c * c) • f = (c • f) * (c • f) := by rw [smul_mul_smul_comm, hf]
      _ = (f * A) * (f * A) := by rw [hfA]
      _ = f * (A * f) * A := by simp only [mul_assoc]
      _ = f * (f * A) * A := by rw [hc]
      _ = (f * f) * (A * A) := by simp only [mul_assoc]
      _ = f := by rw [hf, hA, mul_one]
  have hcc : c * c = 1 := by
    have h3 : (c * c - 1) • f = 0 := by rw [sub_smul, one_smul, hsq, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h0
  have hn : ‖c‖ = 1 := by
    have h4 : ‖c‖ * ‖c‖ = 1 := by rw [← norm_mul, hcc, norm_one]
    nlinarith [norm_nonneg c, sq_nonneg (‖c‖ - 1)]
  rw [hfA, map_smul, trace_idem f hf hx h0, smul_eq_mul, mul_one, hn]

end UpperTheory.V.Z.Mult.Pi
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrA
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem lv_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) (hv : v ∈ fixed ρ K) :
    Lv ρ K ((K : Set G).indicator 1) v = v := by
  have hc : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := by
    have h : (QuotientGroup.mk (QuotientGroup.mk 1 : G ⧸ K).out : G ⧸ K) = QuotientGroup.mk 1 :=
      QuotientGroup.out_eq' _
    simpa using QuotientGroup.eq.1 h
  have hq : ∀ q : G ⧸ K, q ≠ QuotientGroup.mk 1 → q.out ∉ K := by
    intro q hne hmem
    apply hne
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using hmem)
  unfold Lv levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)
    (fun q hne => by rw [Set.indicator_of_notMem (hq q hne), zero_smul]),
    Set.indicator_of_mem (show _ ∈ (K : Set G) from hc)]
  simpa using hv ⟨_, hc⟩

private theorem trOn_of_id {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    [FiniteDimensional ℂ M] (L : V →ₗ[ℂ] V) (hL : ∀ v ∈ M, L v = v) :
    trOn M L = (Module.finrank ℂ M : ℂ) := by
  have h : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [hL v hv]; exact hv
  have hid : L.restrict h = LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, hL v.1 v.2]
  unfold trOn
  rw [dite_eq_left h, hid]
  exact LinearMap.trace_id ℂ _

private theorem finFn_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w) : (fun g => finFn S φ₁ φ₂ (g, 1)) = pf S (two φ₁ φ₂) := by
  funext g
  have h1 : ∀ w : Pl E, atW w ((g, 1) : Gf E n 0) = (qw n w false g, 1) :=
    fun w => Prod.ext rfl (map_one (GeneralLinearGroup.map (pLoc E w)))
  have h2 : ∀ w : Pl E, atW w (thP E n 0 (g, 1)) = (qw n w true g, 1) := by
    intro w
    refine Prod.ext rfl ?_
    simp [atW, thP]
  unfold finFn pf
  simp only [h1, h2]
  rfl

private theorem ind_hecke {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (M N' : Subgroup (GLw n w)) (ho : IsOpen (M : Set (GLw n w))) (hM : M ≤ KGL w (n := n)) (hN : N' ≤ M) :
    IsHecke N' ((M : Set (GLw n w)).indicator 1) := by
  have hcl : IsClosed (M : Set (GLw n w)) := M.isClosed_of_isOpen ho
  have hcomp : IsCompact (M : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2.of_isClosed_subset hcl hM
  refine ⟨hcomp.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal Set.support_indicator_subset hcl), fun k hk x => ?_⟩
  have a1 : k * x ∈ M ↔ x ∈ M := M.mul_mem_cancel_left (hN hk)
  have a2 : x * k ∈ M ↔ x ∈ M := M.mul_mem_cancel_right (hN hk)
  simp only [Set.indicator, SetLike.mem_coe, a1, a2, Pi.one_apply, and_self]

theorem _root_.UpperTheory.V.Z.Mult.Pi.levelTrA : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Mult.Pi.ZTrA → UpperTheory.V.Z.Mult.Pi.SeenTrA → TTr → UpperTheory.V.Z.Mult.Pi.LevelTrA := by
  intro hAdm hZ hSeen hT E _ _ _ n S Z N hSec hSp hG π y B τ hB hτ
  obtain ⟨hne, d₀, hd₀, hd⟩ := hZ E n S Z N hSec hSp hG π y τ hτ
  let c : Pl E → ℂ := fun w => (((N w).relIndex (KGL w (n := n)) : ℕ) : ℂ) ^ 2
  have hc : ∀ w ∈ Z, ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (two φ₁ φ₂ w false) * Lv (τ w).ρ (N w) (two φ₁ φ₂ w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) :=
    fun w hw => hSeen E n w (hSp w hw).2 (τ w) (N w) (hG w).1 (hG w).2.1
  refine ⟨?_, d₀ * ∏ w ∈ Z, c w, by simp [hd₀, c], ?_⟩
  · let φ₀ : ∀ w : Pl E, LF n 0 w := fun w p => (N w : Set (GLw n w)).indicator 1 p.1
    have h2 : ∀ w b, two φ₀ φ₀ w b = (N w : Set (GLw n w)).indicator 1 := by
      intro w b
      cases b <;> rfl
    refine ⟨φ₀, fun w _ N' hN' b => ?_, Finset.prod_ne_zero_iff.2 fun w hw h0 => ?_⟩
    · rw [h2]
      exact ind_hecke w (N w) N' (hG w).1 (hG w).2.1 hN'
    · haveI : FiniteDimensional ℂ (fixed (τ w).ρ (N w)) := hAdm E n w (τ w) (N w) (hG w).1
      have e := hc w hw φ₀ φ₀ fun b => by
        rw [h2]
        exact ind_hecke w (N w) (N w) (hG w).1 (hG w).2.1 le_rfl
      rw [h0, mul_zero, h2, h2, trOn_of_id _ _ fun v hv => by
        rw [Module.End.mul_apply, lv_unit _ _ v hv, lv_unit _ _ v hv]] at e
      exact hne w hw (Submodule.finrank_eq_zero.1 (Nat.cast_eq_zero.1 e))
  · intro φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    obtain ⟨h1, h2, h3⟩ := hT E n S Z N hSec hSp hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    have hF : ∀ w ∈ Z, ∀ b, two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w b = two φ₁ φ₂ w b := by
      intro w hw b
      cases b <;> simp [two, intersection_update_fsHerm_neg_one, hw]
    have hP : ∀ w ∈ Z, GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w))
        (Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w false) *
          Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) := by
      intro w hw
      rw [hF w hw, hF w hw]
      exact hc w hw φ₁ φ₂ (hφ w hw)
    rw [finFn_one S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)]
    refine ⟨h1, ?_⟩
    rw [h3, smul_mul_assoc, map_smul, hd _ h2, smul_eq_mul, Finset.prod_congr rfl hP, Finset.prod_mul_distrib]
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PiTermAOf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

namespace UpperTheory.V.Z.Mult.Pi

attribute [local instance] borelG borelF borelA borelH

private theorem lev_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    {N N' : ∀ w : Pl E, Subgroup (GLw n w)} (h : ∀ w, N w ≤ N' w) : Lev S N ≤ Lev S N' := by
  intro g hg
  simp only [Lev, Subgroup.mem_iInf] at hg ⊢
  exact fun i => h _ (hg i)

theorem piTermA_of (h1 : GlobalTwistedTraceBound) (hθ : ThetaFixOf) (h2 : WtEx) (h3 : LevTop) (h4 : LevFix) (h5 : LcLevel) (h6 : ToYdA)
    (h7 : LevelTrA) (h8 : TwUniq) (h9 : LevIdx) (h10 : VolIdx) (hK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
      IsOpen (Kf E n : Set (GF E n)) ∧ IsCompact (Kf E n : Set (GF E n))) : PiTermA := by
  intro E _ _ _ _ n hn l u hu μC μ _ _
  obtain ⟨hFo, hFc⟩ := hK E n
  let K₀ : TopologicalSpace.PositiveCompacts (GF E n) :=
    ⟨⟨(Kf E n : Set (GF E n)), hFc⟩, by
      show (interior (Kf E n : Set (GF E n))).Nonempty
      rw [hFo.interior_eq]
      exact ⟨1, (Kf E n).one_mem⟩⟩
  let μf : Measure (GF E n) := Measure.haarMeasure K₀
  haveI : μf.IsHaarMeasure := inferInstance
  have hμ1 : μf (Kf E n : Set (GF E n)) = 1 := Measure.haarMeasure_self (K₀ := K₀)
  obtain ⟨c₀, hc₀, hG⟩ := h1 E n μC μf μ
  refine ⟨c₀, hc₀, fun π hreg hd hl S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨lamE, hlam⟩ := h2 E n π hreg
  have hch : ∀ w : InfinitePlace E,
      HasInfCharGL π.V w.embedding (Multiset.map (infOf (l w).w true) Finset.univ.val) ∧
      HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding) (Multiset.map (infOf (l w).w false) Finset.univ.val) := fun w => ⟨by
    rw [map_infOf_true]
    exact hl w, by
    rw [map_infOf_false, ← GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E n π π hd w.embedding _ _ (hl w) (hlam _)]
    exact hlam _⟩
  have level : ∀ N : ∀ w : Pl E, Subgroup (GLw n w), Good Z N → (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ Lev S N, finRep E n k ψ = ψ) →
      (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
        (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
      ∃ c : ℂ, ‖c‖ = c₀ ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
        ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
          (k : ∀ v, Mat n → ((lefE n (l v).w).V →L[ℂ] (lefE n (l v).w).V)) (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
          TEv S T e₂ → (∀ v, IsMult μC (lefE n (l v).w) (k v) (vl v) R) →
          IsTwTr μ π (phiProd (fun v => (l v).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
            (c * (∏ v, vl v (infOf (l v).w)) * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0) := by
    intro N hN hfix
    obtain ⟨hKo, hKc, -, -⟩ := h3 E n S Z N hS hZ hN
    obtain ⟨hKθ, hY⟩ := h6 E n S Z N hS hZ hN π u hu
    obtain ⟨Y, ρ, A, cK, hYπ, hfd, hne, hYfix, hact, hsimple, hsq, htw, hcK, htr⟩ :=
      hG hn π hreg (hθ E n hn π hd) (fun v => (l v).w) (fun v => (l v).anti) hch (Lev S N) hKo hKc hKθ hfix
    obtain ⟨y, v, hv, hyv⟩ := hY μf inferInstance Y ρ A hYπ hfd hne hYfix hact hsimple hsq htw
    obtain ⟨href, d, hd0, hdtr⟩ := h7 E n S Z N hS hZ hN π y B τ hB hτ
    obtain ⟨hle, hidx⟩ := h9 E n S Z N hS hZ hN
    have hvol := h10 (GF E n) μf (Kf E n) (Lev S N) hKo hFc hle
    rw [hμ1, hidx] at hvol
    refine ⟨href, cK * v * d, ?_, ?_⟩
    · rw [norm_mul, norm_mul, hcK, hv, hd0, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_assoc]
      push_cast at hvol
      rw [hvol]
      simp
    intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
    obtain ⟨hH, hTr⟩ := hdtr φ₁ φ₂ hφ T hT e₁ e₂ hE
    obtain ⟨hHF, hTrY⟩ := hyv _ hH
    have key := htr k vl (fun _ => R) hM _ hHF
    rw [hTrY, hTr] at key
    have e : cK * (∏ w : InfinitePlace E, vl w (infOf (l w).w)) *
        (v * (d * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)) =
        cK * v * d * (∏ v : InfinitePlace E, vl v (infOf (l v).w)) *
          (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0 := by ring
    rw [e] at key
    exact key
  obtain ⟨N₀, hN₀, ψ, hψ, hψ0, hψfix⟩ := h4 E n π S Z hS hZ fun w hw => ⟨B w, hB w hw⟩
  obtain ⟨⟨φr, hr, hrne⟩, c₁, hc₁, hlev₀⟩ := level N₀ hN₀ ⟨ψ, hψ, hψ0, hψfix⟩
  refine ⟨c₁, hc₁, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨N, hN, hle, hHecke⟩ := h5 E n Z N₀ hN₀ φ₁ φ₂ hφ
  obtain ⟨-, c, -, hlev⟩ := level N hN ⟨ψ, hψ, hψ0, fun g hg => hψfix g (lev_mono S hle hg)⟩
  have main := hlev φ₁ φ₂ hHecke T hT e₁ e₂ k vl R hE hM
  by_cases hP : (∏ v : InfinitePlace E, vl v (infOf (l v).w)) = 0
  · rw [hP] at main ⊢
    simpa using main
  have hcc : c = c₁ := by
    let e : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)) := fun _ => Ex.one
    have hEe : TEv S (∅ : Finset (Pl E)) e := ⟨by simp, by simp⟩
    have a₀ := hlev₀ φr φr (fun w hw b => hr w hw (N₀ w) le_rfl b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have a₁ := hlev φr φr (fun w hw b => hr w hw (N w) (hle w) b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have heq := h8 E n μ π _ _ _ a₁ a₀
    simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.val, Finset.prod_empty, mul_one] at heq
    exact mul_right_cancel₀ hP (mul_right_cancel₀ hrne heq)
  rw [hcc] at main
  exact main

theorem kf_top (h0 : SlotBasic) (h3 : LevTop) (hP : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsOpen (Kf E n : Set (GF E n)) ∧ IsCompact (Kf E n : Set (GF E n)) := by
  obtain ⟨S, hS⟩ := (hP E).1
  have hG : Good (∅ : Finset (Pl E)) (fun w => KGL w (n := n)) := fun w =>
    ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).1, le_rfl,
      fun k hk x hx => mul_mem (mul_mem hk hx) (inv_mem hk), fun _ => rfl⟩
  obtain ⟨ho, hc, -, -⟩ := h3 E n S ∅ _ hS (fun _ h => absurd h (Finset.notMem_empty _)) hG
  have e : Lev S (fun w => KGL w (n := n)) = Kf E n := Subgroup.ext (h0 E n S hS).2.2.2.2.2.2
  rw [e] at ho hc
  exact ⟨ho, hc⟩

end UpperTheory.V.Z.Mult.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LiftRestrict
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F

private theorem lift_lift {J₀ J A : Type} [Ring A] [Algebra ℂ A] (v : J₀ → J) (e : J → A)
    (p : FreeAlgebra ℂ J₀) :
    FreeAlgebra.lift ℂ e (FreeAlgebra.lift ℂ (fun j => FreeAlgebra.ι ℂ (v j)) p) =
      FreeAlgebra.lift ℂ (fun j => e (v j)) p := by
  have h : (FreeAlgebra.lift ℂ e).comp (FreeAlgebra.lift ℂ (fun j => FreeAlgebra.ι ℂ (v j))) =
      FreeAlgebra.lift ℂ (fun j => e (v j)) := by
    apply FreeAlgebra.hom_ext
    funext j
    simp
  exact DFunLike.congr_fun h p

private theorem lift_restrict {V J : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V)
    (e : J → Module.End ℂ V) (r : J → Module.End ℂ P) (h : ∀ j (x : P), ((r j x : P) : V) = e j x)
    (p : FreeAlgebra ℂ J) : ∀ x : P, ((FreeAlgebra.lift ℂ r p x : P) : V) = FreeAlgebra.lift ℂ e p x := by
  refine FreeAlgebra.induction ℂ J (motive := fun p => ∀ x : P, ((FreeAlgebra.lift ℂ r p x : P) : V) = FreeAlgebra.lift ℂ e p x)
    ?_ ?_ ?_ ?_ p
  · intro c x
    simp [AlgHom.commutes, Module.algebraMap_end_apply]
  · intro j x
    simpa using h j x
  · intro a b ha hb x
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  · intro a b ha hb x
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]

private theorem list_restrict {V ι : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V)
    (e : ι → Module.End ℂ V) (r : ι → Module.End ℂ P) (h : ∀ i (x : P), ((r i x : P) : V) = e i x)
    (l : List ι) : ∀ x : P, (((l.map r).prod x : P) : V) = (l.map e).prod x := by
  induction l with
  | nil => intro x; rfl
  | cons a l ih =>
    intro x
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h, ih]

private theorem simple_of {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (W : Submodule ℂ P)
    (h : W.map P.subtype = ⊥ ∨ W.map P.subtype = P) : W = ⊥ ∨ W = ⊤ := by
  have inj := Submodule.map_injective_of_injective P.injective_subtype
  rcases h with h | h
  · left
    exact inj (by rw [h, Submodule.map_bot])
  · right
    exact inj (by rw [h, Submodule.map_subtype_top])

private theorem comm_res {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) (u v : Module.End ℂ P)
    (u' v' : Module.End ℂ V) (hu : ∀ x : P, ((u x : P) : V) = u' x) (hv : ∀ x : P, ((v x : P) : V) = v' x)
    (h : Commute u' v') : Commute u v := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((u (v x) : P) : V) = ((v (u x) : P) : V)
  rw [hu, hv, hv, hu]
  exact LinearMap.congr_fun h.eq (x : V)

private theorem prod_reorder {ι A : Type} [Monoid A] (Z : Finset ι) (c : ι × Bool → A)
    (hc : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), ∀ k ∈ Z ×ˢ (Finset.univ : Finset Bool), i ≠ k → Commute (c i) (c k)) :
    ((Z ×ˢ (Finset.univ : Finset Bool)).toList.map c).prod =
      ((Finset.univ : Finset Z).toList.map fun w => c (w.1, false) * c (w.1, true)).prod := by
  classical
  have step : ∀ l : List Z, ((l.flatMap fun w => [(w.1, false), (w.1, true)]).map c).prod =
      (l.map fun w => c (w.1, false) * c (w.1, true)).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons, List.prod_cons, mul_assoc]
      rw [ih]
  have hnd : ((Finset.univ : Finset Z).toList.flatMap fun w => [(w.1, false), (w.1, true)]).Nodup := by
    refine List.nodup_flatMap.2 ⟨fun w _ => by simp, ?_⟩
    refine (Finset.nodup_toList _).imp_of_mem ?_
    intro a b _ _ hab
    simp only [Function.onFun, List.disjoint_left]
    intro x hx hx'
    apply hab
    apply Subtype.ext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;> simpa using h
  have hperm : (Z ×ˢ (Finset.univ : Finset Bool)).toList.Perm
      ((Finset.univ : Finset Z).toList.flatMap fun w => [(w.1, false), (w.1, true)]) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hnd).2 ?_
    rintro ⟨w, b⟩
    simp only [Finset.mem_toList, Finset.mem_product, Finset.mem_univ, and_true, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro hw
      refine ⟨⟨w, hw⟩, trivial, ?_⟩
      cases b <;> simp
    · rintro ⟨a, -, h⟩
      have hw : w = a.1 := by
        rcases h with h | h <;> exact (Prod.ext_iff.1 h).1
      rw [hw]
      exact a.2
  rw [← step]
  refine List.Perm.prod_eq' (hperm.map c) ?_
  rw [List.pairwise_map]
  refine (Finset.nodup_toList _).imp_of_mem ?_
  intro a b ha hb hab
  exact hc a (Finset.mem_toList.1 ha) b (Finset.mem_toList.1 hb) hab

theorem UpperTheory.V.Z.Mult.Pi.zTrA :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → PfHecke → ProdOp → LocComm → YLoc → ZSimple → YSwap → Isot → SimpleFix → UpperTheory.V.Z.Mult.Pi.AbsCoreA → UpperTheory.V.Z.Mult.Pi.ZTrA := by
  intro hAdm hPf hPO hLC hYL hZS hYS hIs hSF hAC E _ _ _ n S Z N hS hZ hG π y τ hτ
  have hNo : ∀ w, IsOpen (N w : Set (GLw n w)) := fun w => (hG w).1
  have hNl : ∀ w, N w ≤ KGL w (n := n) := fun w => (hG w).2.1
  have hSl : ∀ w ∈ Z, ∀ b, Sl S (w, b) := fun w hw b => ⟨(hZ w hw).1, fun _ => (hZ w hw).2⟩
  have hZero : ∀ w, IsHecke (N w) (0 : GLw n w → ℂ) := fun w => ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have hLoc := hLC E n S Z N hS hZ hG
  have hfixY : ∀ w ∈ Z, ∀ b, ∀ x ∈ y.Y, x ∈ fixed (rw' n w b) (N w) := fun w hw b x hx =>
    ((hLoc (w, b) (hSl w hw b) 0 (hZero w)).1 x (y.fix hx)).1
  have part1 : ∀ w ∈ Z, fixed (τ w).ρ (N w) ≠ ⊥ := by
    intro w hw hbot
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot y.ne
    apply hx0
    have := hIs E n π w (τ w) (hτ w hw) (N w) (hNo w) (hNl w) 1 (fun v hv => by
      rw [hbot, Submodule.mem_bot] at hv
      simp [hv]) x (y.le hx) (hfixY w hw false x hx)
    simpa using this
  haveI : FiniteDimensional ℂ y.Y := y.fd
  haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne
  haveI : ∀ w : ↥Z, FiniteDimensional ℂ (fixed (τ w.1).ρ (N w.1)) := fun w =>
    hAdm E n w.1 (τ w.1) (N w.1) (hNo _)
  have hαinv : ∀ (w : ↥Z) (f : {f : GLw n w.1 → ℂ // IsHecke (N w.1) f}), ∀ x ∈ fixed (τ w.1).ρ (N w.1),
      Lv (τ w.1).ρ (N w.1) f.1 x ∈ fixed (τ w.1).ρ (N w.1) := fun w f x hx =>
    (hSF E n w.1 (τ w.1) (N w.1) (hNo _) (hNl _)).1 f.1 f.2 x hx
  have hYinv : ∀ (b : Bool) (w : ↥Z) (f : {f : GLw n w.1 → ℂ // IsHecke (N w.1) f}), ∀ x ∈ y.Y,
      Lw N w.1 b f.1 x ∈ y.Y := fun b w f x hx =>
    hYL E n S Z N hS hZ hG π y (w.1, b) (hSl w.1 w.2 b) f.1 f.2 x hx
  let α : ∀ w : ↥Z, {f : GLw n w.1 → ℂ // IsHecke (N w.1) f} → Module.End ℂ (fixed (τ w.1).ρ (N w.1)) :=
    fun w f => (Lv (τ w.1).ρ (N w.1) f.1).restrict (hαinv w f)
  let c : Bool → ∀ w : ↥Z, {f : GLw n w.1 → ℂ // IsHecke (N w.1) f} → Module.End ℂ y.Y :=
    fun b w f => (Lw N w.1 b f.1).restrict (hYinv b w f)
  have h1 : ∀ (i : ↥Z) (W : Submodule ℂ (fixed (τ i.1).ρ (N i.1))), (∀ f, ∀ x ∈ W, α i f x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro w W hW
    refine simple_of _ W ((hSF E n w.1 (τ w.1) (N w.1) (hNo _) (hNl _)).2 (W.map (Submodule.subtype _))
      (Submodule.map_subtype_le _ _) ?_)
    intro f hf x hx
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    exact Submodule.mem_map.2 ⟨α w ⟨f, hf⟩ x0, hW ⟨f, hf⟩ x0 hx0, rfl⟩
  have h2 : ∀ (i : ↥Z) (p : FreeAlgebra ℂ {f : GLw n i.1 → ℂ // IsHecke (N i.1) f}),
      FreeAlgebra.lift ℂ (α i) p = 0 → FreeAlgebra.lift ℂ (c false i) p = 0 := by
    intro i p hp
    have hz : ∀ x ∈ fixed (τ i.1).ρ (N i.1), FreeAlgebra.lift ℂ (Lv (τ i.1).ρ (N i.1))
        (FreeAlgebra.lift ℂ (fun j : {f : GLw n i.1 → ℂ // IsHecke (N i.1) f} => FreeAlgebra.ι ℂ j.1) p) x = 0 := by
      intro x hx
      rw [lift_lift Subtype.val, ← lift_restrict (fixed (τ i.1).ρ (N i.1)) _ (α i) (fun _ _ => rfl) p ⟨x, hx⟩, hp]
      rfl
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h3 := hIs E n π i.1 (τ i.1) (hτ i.1 i.2) (N i.1) (hNo _) (hNl _) _ hz x.1 (y.le x.2)
      (hfixY i.1 i.2 false x.1 x.2)
    rw [lift_lift Subtype.val] at h3
    have h4 := lift_restrict y.Y (fun j : {f : GLw n i.1 → ℂ // IsHecke (N i.1) f} => Lv (rw' n i.1 false) (N i.1) j.1)
      (c false i) (fun _ _ => rfl) p x
    rw [h3] at h4
    simpa using h4
  have h3 : ∀ (i k : ↥Z), i ≠ k → ∀ f g, Commute (c false i f) (c false k g) := by
    intro i k hik f g
    refine comm_res y.Y _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      ((hLoc (i.1, false) (hSl _ i.2 _) f.1 f.2).2 (k.1, false) (hSl _ k.2 _) ?_ g.1 g.2)
    intro h
    exact hik (Subtype.ext (Prod.ext_iff.1 h).1)
  have h4 : ∀ (i k : ↥Z) f g, Commute (c false i f) (c true k g) := by
    intro i k f g
    refine comm_res y.Y _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      ((hLoc (i.1, false) (hSl _ i.2 _) f.1 f.2).2 (k.1, true) (hSl _ k.2 _) (by simp) g.1 g.2)
  have h5 : ∀ (i : ↥Z) f, y.A * c false i f = c true i f * y.A := by
    intro i f
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact hYS E n S Z N hS hZ hG π y i.1 i.2 f.1 f.2 x (c false i f x) rfl
  have h6 : ∀ W : Submodule ℂ y.Y, (∀ (i : ↥Z) f, ∀ x ∈ W, c false i f x ∈ W ∧ c true i f x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine simple_of _ W (hZS E n S Z N hS hZ hG π y (W.map (Submodule.subtype _))
      (Submodule.map_subtype_le _ _) ?_)
    intro w hw b f hf x hx
    obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
    have := hW ⟨w, hw⟩ ⟨f, hf⟩ x0 hx0
    cases b
    · exact Submodule.mem_map.2 ⟨_, this.1, rfl⟩
    · exact Submodule.mem_map.2 ⟨_, this.2, rfl⟩
  obtain ⟨d, hd, key⟩ := hAC ↥Z (fun w : ↥Z => {f : GLw n w.1 → ℂ // IsHecke (N w.1) f})
    (fun w : ↥Z => ↥(fixed (τ w.1).ρ (N w.1))) y.Y α (c false) (c true) y.A h1 h2 h3 h4 y.sq h5 h6
  refine ⟨part1, d, hd, fun F hF => ?_⟩
  have hFh : ∀ w (_ : w ∈ Z) b, IsHecke (N w) (F w b) := fun w hw b =>
    (hF.1 (w, b) (by simp [hw])).2
  have hpf := hPf E n S Z N hS hZ hG _ F hF
  have hcomm : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), ∀ k ∈ Z ×ˢ (Finset.univ : Finset Bool), i ≠ k →
      Commute (Lw N i.1 i.2 (F i.1 i.2)) (Lw N k.1 k.2 (F k.1 k.2)) := by
    intro i hi k hk hik
    exact (hLoc i (hF.1 i hi).1 _ (hF.1 i hi).2).2 k (hF.1 k hk).1 hik _ (hF.1 k hk).2
  have e1 : y.r (pf S F) = (((Finset.univ : Finset ↥Z).toList.map fun i =>
      c false i ⟨F i.1 false, hFh _ i.2 _⟩ * c true i ⟨F i.1 true, hFh _ i.2 _⟩).prod) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [y.act _ hpf x, hPO E n S Z N hS hZ hG _ F hF x (y.fix x.2),
      prod_reorder Z (fun i => Lw N i.1 i.2 (F i.1 i.2)) hcomm]
    exact (list_restrict y.Y _ _ (fun _ _ => rfl) _ x).symm
  rw [e1, key (fun i => ⟨F i.1 false, hFh _ i.2 _⟩) (fun i => ⟨F i.1 true, hFh _ i.2 _⟩)]
  congr 1
  rw [← Finset.prod_coe_sort Z]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hinv : ∀ v ∈ fixed (τ w.1).ρ (N w.1), (Lv (τ w.1).ρ (N w.1) (F w.1 false) * Lv (τ w.1).ρ (N w.1) (F w.1 true)) v ∈
      fixed (τ w.1).ρ (N w.1) := fun v hv =>
    hαinv w ⟨_, hFh _ w.2 _⟩ _ (hαinv w ⟨_, hFh _ w.2 _⟩ v hv)
  rw [GlobalTheory.BCT.trOn, dite_eq_left hinv]
  rfl
end
