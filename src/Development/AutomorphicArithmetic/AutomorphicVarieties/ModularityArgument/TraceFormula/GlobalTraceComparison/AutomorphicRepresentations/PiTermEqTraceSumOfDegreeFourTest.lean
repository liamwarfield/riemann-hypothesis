module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDomInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.WtExPf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTranslF
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PJointFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.LiftRestrict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PProdOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PGenLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSphOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PAbsCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSatAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiFinOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PWtInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PEvalBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.GlobalHaarAverageTraceIdentity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.UnitOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLevelTr
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

theorem levelTr_pf : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → ZTr → SeenTr → TTr → LevelTr := by
  intro hAdm hZ hSeen hT E _ _ _ n S Z N hSec hSp hG π y B τ hB hτ
  obtain ⟨hne, d₀, hd₀, hd⟩ := hZ E n S Z N hSec hSp hG π y τ hτ
  have hc : ∀ w ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (two φ₁ φ₂ w false) * Lv (τ w).ρ (N w) (two φ₁ φ₂ w true)) =
        c * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) :=
    fun w hw => hSeen E n w (hSp w hw).2 (τ w) (N w) (hG w).1 (hG w).2.1
  choose! c hc0 hc using hc
  refine ⟨?_, d₀ * ∏ w ∈ Z, c w, mul_ne_zero hd₀ (Finset.prod_ne_zero_iff.2 hc0), ?_⟩
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

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTwUniq
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.twUniq_pf :
    TwUniq := by
  intro E _ _ _ n μ π φ t t' h₁ h₂
  obtain ⟨L₁, e₁, -, rfl⟩ := h₁
  obtain ⟨L₂, e₂, -, rfl⟩ := h₂
  obtain rfl : L₁ = L₂ := by
    refine LinearMap.ext fun ψ => Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [e₁ ψ x, e₂ ψ x]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PZSimple
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zSimple_pf :
    GenLoc → LocComm → SphOp → YLoc → ZSimple := by
  intro hG hC hS hY E _ _ _ n S Z N hSec hZ hN π y W hW hst
  have key : ∀ U : Submodule ℂ (Sm E n), U ≤ y.Y →
      (∀ i, Sl S i → ∀ f, IsHecke (N i.1) f → ∀ x ∈ U, Lw N i.1 i.2 f x ∈ U) →
      U = ⊥ ∨ U = y.Y := by
    intro U hU hUs
    have hgen := hG E n S Z N hSec hZ hN U (hU.trans y.fix) hUs
    have hs := y.simple (U.comap y.Y.subtype) (by
      intro h hh x hx
      have hmem : ((y.r h x : y.Y) : Sm E n) ∈ U := by
        rw [y.act h hh x]
        exact hgen h hh _ hx
      exact hmem)
    rcases hs with hs | hs
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hU hx⟩ : y.Y) ∈ U.comap y.Y.subtype := hx
      rw [hs] at hx'
      have h0 := (Submodule.mem_bot ℂ).1 hx'
      exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val h0)
    · right
      refine le_antisymm hU fun x hx => ?_
      have hx' : (⟨x, hx⟩ : y.Y) ∈ U.comap y.Y.subtype := by
        rw [hs]
        exact Submodule.mem_top
      exact hx'
  have scal : ∀ i, Sl S i → i.1 ∉ Z → ∀ f, IsHecke (N i.1) f →
      ∃ c : ℂ, ∀ x ∈ y.Y, Lw N i.1 i.2 f x = c • x := by
    intro i hi hiZ f hf
    haveI := y.fd
    haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne
    have hNw : N i.1 = KGL i.1 (n := n) := (hN i.1).2.2.2 hiZ
    let T : Module.End ℂ y.Y := (Lw N i.1 i.2 f).restrict
      (fun x hx => hY E n S Z N hSec hZ hN π y i hi f hf x hx)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    refine ⟨c, ?_⟩
    let U : Submodule ℂ (Sm E n) := y.Y ⊓ LinearMap.ker (Lw N i.1 i.2 f - c • LinearMap.id)
    have memU : ∀ x, x ∈ U ↔ x ∈ y.Y ∧ Lw N i.1 i.2 f x = c • x := by
      intro x
      simp [U, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hcomm : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ y.Y,
        Lw N i.1 i.2 f (Lw N k.1 k.2 g x) = Lw N k.1 k.2 g (Lw N i.1 i.2 f x) := by
      intro k hk g hg x hx
      by_cases hik : i = k
      · subst hik
        have hxf : x ∈ fixed (rw' n i.1 i.2) (N i.1) := ((hC E n S Z N hSec hZ hN i hi f hf).1 x (y.fix hx)).1
        rw [hNw] at hf hg hxf
        simp only [Lw]
        rw [hNw]
        exact hS E n i.1 (Sm E n) (rw' n i.1 i.2) f g hf hg x hxf
      · exact LinearMap.congr_fun ((hC E n S Z N hSec hZ hN i hi f hf).2 k hk hik g hg).eq x
    have hUs : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ U, Lw N k.1 k.2 g x ∈ U := by
      intro k hk g hg x hx
      obtain ⟨hxY, hxe⟩ := (memU x).1 hx
      refine (memU _).2 ⟨hY E n S Z N hSec hZ hN π y k hk g hg x hxY, ?_⟩
      rw [hcomm k hk g hg x hxY, hxe, map_smul]
    have hvU : (v : Sm E n) ∈ U := by
      refine (memU _).2 ⟨v.2, ?_⟩
      have h1 : T v = c • v := hv.apply_eq_smul
      exact congrArg Subtype.val h1
    rcases key U inf_le_left hUs with h0 | h1
    · exfalso
      rw [h0] at hvU
      exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hvU))
    · intro x hx
      rw [← h1] at hx
      exact ((memU x).1 hx).2
  refine key W hW fun i hi f hf x hx => ?_
  by_cases hiZ : i.1 ∈ Z
  · exact hst i.1 hiZ i.2 f hf x hx
  · obtain ⟨c, hc⟩ := scal i hi hiZ f hf
    rw [hc x (hW hx)]
    exact W.smul_mem c hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLvShift
noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (y : V) :
    y ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k y = y := by
  constructor
  · intro hy k hk
    have := hy ⟨k, hk⟩
    simpa using this
  · intro hy k
    simpa using hy k k.2

private theorem lv_apply (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (y : V)
    (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) :
    Lv ρ K f y = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out y := by
  have hs : (Function.support fun q : G ⧸ K =>
      f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite := hf.subset (by
    intro q hq hz
    apply hq
    simp [hz])
  simp only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  have := map_finsum (LinearMap.applyₗ y : (V →ₗ[ℂ] V) →ₗ[ℂ] V) hs
  simpa using this

private theorem reindex (K : Subgroup G) (σ : G ⧸ K ≃ G ⧸ K) (a : G → G)
    (hσ : ∀ g : G, σ (g : G ⧸ K) = (a g : G ⧸ K)) (ψ₁ ψ₂ : G → V)
    (hi : ∀ g, ∀ k ∈ K, ψ₁ (g * k) = ψ₁ g) (ha : ∀ g, ψ₁ (a g) = ψ₂ g) :
    ∑ᶠ q : G ⧸ K, ψ₁ q.out = ∑ᶠ q : G ⧸ K, ψ₂ q.out := by
  refine (finsum_comp_equiv σ (f := fun q : G ⧸ K => ψ₁ q.out)).symm.trans (finsum_congr fun q => ?_)
  have e : ((a q.out : G) : G ⧸ K) = ((σ q).out : G) := by
    rw [← hσ, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have hk : (a q.out)⁻¹ * (σ q).out ∈ K := QuotientGroup.eq.1 e
  show ψ₁ (σ q).out = ψ₂ q.out
  rw [← ha, ← hi (a q.out) _ hk, mul_inv_cancel_left]

private def rEquiv (K : Subgroup G) (u : G) (h₁ : ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h₂ : ∀ x ∈ K, u⁻¹ * x * u ∈ K) : G ⧸ K ≃ G ⧸ K where
  toFun := Quotient.map' (· * u) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := h₂ _ hab
    convert this using 1
    group)
  invFun := Quotient.map' (· * u⁻¹) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := h₁ _ hab
    convert this using 1
    group)
  left_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      show ((g * u * u⁻¹ : G) : G ⧸ K) = g
      rw [mul_inv_cancel_right]
  right_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      show ((g * u⁻¹ * u : G) : G ⧸ K) = g
      rw [inv_mul_cancel_right]

private theorem fin_supp [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (f : G → ℂ) (hf : HasCompactSupport f) :
    (Function.support fun q : G ⧸ K => f q.out).Finite := by
  obtain ⟨t, ht⟩ := hf.isCompact.elim_finite_subcover
    (fun x : G => (fun y => x⁻¹ * y) ⁻¹' (K : Set G))
    (fun x => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun x : G => (x : G ⧸ K))).subset ?_
  intro q hq
  have hm : q.out ∈ tsupport f := subset_tsupport _ hq
  obtain ⟨x, hx, hxq⟩ := Set.mem_iUnion₂.1 (ht hm)
  exact ⟨x, hx, (QuotientGroup.eq.2 hxq).trans (QuotientGroup.out_eq' q)⟩

end SlopeTestRemainingChoices

theorem lvShift_pf : LvShift := by
  intro G V _ _ _ _ _ ρ K hKo hKc u hu h hh
  have hc : ∀ x ∈ K, u * x * u⁻¹ ∈ K := fun x hx => (hu x).1 hx
  have hc' : ∀ x ∈ K, u⁻¹ * x * u ∈ K := fun x hx => (hu _).2 (by
    have e : u * (u⁻¹ * x * u) * u⁻¹ = x := by group
    rwa [e])
  have H1 : IsHecke K (fun g => h (g * u⁻¹)) := by
    refine ⟨hh.1.comp_homeomorph (Homeomorph.mulRight u⁻¹), fun k hk x => ⟨?_, ?_⟩⟩
    · show h (k * x * u⁻¹) = h (x * u⁻¹)
      rw [mul_assoc]
      exact (hh.2 k hk _).1
    · show h (x * k * u⁻¹) = h (x * u⁻¹)
      have e : x * k * u⁻¹ = x * u⁻¹ * (u * k * u⁻¹) := by group
      rw [e]
      exact (hh.2 _ (hc k hk) _).2
  have H2 : IsHecke K (fun g => h (u⁻¹ * g)) := by
    refine ⟨hh.1.comp_homeomorph (Homeomorph.mulLeft u⁻¹), fun k hk x => ⟨?_, ?_⟩⟩
    · show h (u⁻¹ * (k * x)) = h (u⁻¹ * x)
      have e : u⁻¹ * (k * x) = u⁻¹ * k * u * (u⁻¹ * x) := by group
      rw [e]
      exact (hh.2 _ (hc' k hk) _).1
    · show h (u⁻¹ * (x * k)) = h (u⁻¹ * x)
      rw [← mul_assoc]
      exact (hh.2 k hk _).2
  have H3 : IsHecke K ((K : Set G).indicator 1) := by
    refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
    · have e : Function.support ((K : Set G).indicator (1 : G → ℂ)) = (K : Set G) := by
        ext x
        by_cases hx : x ∈ (K : Set G) <;> simp [hx]
      show IsCompact (closure (Function.support ((K : Set G).indicator (1 : G → ℂ))))
      rw [e, (K.isClosed_of_isOpen hKo).closure_eq]
      exact hKc
    · have : k * x ∈ (K : Set G) ↔ x ∈ (K : Set G) := K.mul_mem_cancel_left hk
      by_cases hx : x ∈ (K : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun c => hx (this.1 c))]
    · have : x * k ∈ (K : Set G) ↔ x ∈ (K : Set G) := K.mul_mem_cancel_right hk
      by_cases hx : x ∈ (K : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun c => hx (this.1 c))]
  refine ⟨H1, H2, H3, fun y hy => ?_⟩
  have hy' := (mem_fixed_iff ρ K y).1 hy
  have hm : ∀ (a b : G) (v : V), ρ (a * b) v = ρ a (ρ b v) := fun a b v => by
    rw [map_mul]
    rfl
  have hinv : ∀ (f : G → ℂ), (∀ k ∈ K, ∀ x, f (x * k) = f x) → ∀ g, ∀ k ∈ K,
      f (g * k) • ρ (g * k) y = f g • ρ g y := fun f hf g k hk => by
    rw [hf k hk, hm, hy' k hk]
  refine ⟨(mem_fixed_iff ρ K _).2 fun k hk => ?_, ?_, ?_, ?_⟩
  · have e : k * u = u * (u⁻¹ * k * u) := by group
    rw [← hm, e, hm, hy' _ (hc' k hk)]
  · rw [lv_apply ρ K _ y (fin_supp K hKo _ H1.1), lv_apply ρ K h _ (fin_supp K hKo _ hh.1)]
    refine reindex K (rEquiv K u hc hc') (· * u) (fun g => rfl)
      (fun g => h (g * u⁻¹) • ρ g y) (fun g => h g • ρ g (ρ u y))
      (hinv (fun g => h (g * u⁻¹)) fun k hk x => (H1.2 k hk x).2) fun g => ?_
    show h (g * u * u⁻¹) • ρ (g * u) y = h g • ρ g (ρ u y)
    rw [mul_inv_cancel_right, hm]
  · have hs : (Function.support fun q : G ⧸ K => h q.out • ρ q.out y).Finite :=
      (fin_supp K hKo _ hh.1).subset (by
        intro q hq hz
        apply hq
        simp [hz])
    rw [lv_apply ρ K _ y (fin_supp K hKo _ H2.1), lv_apply ρ K h y (fin_supp K hKo _ hh.1),
      map_finsum (ρ u) hs]
    simp only [map_smul]
    refine reindex K (MulAction.toPerm u) (u * ·) (fun g => rfl)
      (fun g => h (u⁻¹ * g) • ρ g y) (fun g => h g • ρ u (ρ g y))
      (hinv (fun g => h (u⁻¹ * g)) fun k hk x => (H2.2 k hk x).2) fun g => ?_
    show h (u⁻¹ * (u * g)) • ρ (u * g) y = h g • ρ u (ρ g y)
    rw [inv_mul_cancel_left, hm]
  · rw [lv_apply ρ K _ y (fin_supp K hKo _ H3.1)]
    have h1 : ((1 : G) : G ⧸ K).out ∈ (K : Set G) := by
      have : ((((1 : G) : G ⧸ K).out : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := QuotientGroup.out_eq' _
      have := QuotientGroup.eq.1 this
      simpa using this
    rw [finsum_eq_single _ ((1 : G) : G ⧸ K)]
    · rw [Set.indicator_of_mem h1, hy' _ h1]
      simp
    · intro q hq
      have : q.out ∉ (K : Set G) := fun c => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using K.inv_mem c))
      rw [Set.indicator_of_notMem this, zero_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.ThetaInvolutionFacts
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abstract

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

private theorem list_eig (L : ι → Module.End ℂ M) (c : ι → ℂ) (x : M) (l : List ι)
    (h : ∀ i ∈ l, L i x = c i • x) : (l.map L).prod x = (l.map c).prod • x :=
  _root_.UpperTheory.Reformulated.B.Qk12.list_eig L c x l h

private theorem prod_split [DecidableEq ι] (L : ι → Module.End ℂ M) (I₀ I₁ : Finset ι) (hd : Disjoint I₀ I₁)
    (hc : ∀ i ∈ I₀ ∪ I₁, ∀ k ∈ I₀ ∪ I₁, i ≠ k → Commute (L i) (L k)) :
    ((I₀ ∪ I₁).toList.map L).prod = (I₀.toList.map L).prod * (I₁.toList.map L).prod := by
  have hp : (I₀ ∪ I₁).toList.Perm (I₀.toList ++ I₁.toList) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).2 ?_
    · exact List.nodup_append.2 ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb hab =>
        Finset.disjoint_left.1 hd (Finset.mem_toList.1 ha) (hab ▸ Finset.mem_toList.1 hb)⟩
    · intro a
      simp
  have hq := hp.map L
  rw [hq.prod_eq' ?_, List.map_append, List.prod_append]
  rw [List.pairwise_map]
  exact (Finset.nodup_toList _).imp_of_mem fun ha hb hab =>
    hc _ (Finset.mem_toList.1 ha) _ (Finset.mem_toList.1 hb) hab

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem two_in {Z T T' : Finset (Pl E)} {w : Pl E} (hw : w ∈ Z) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (b : Bool) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T' φ₂ e₂) w b = two φ₁ φ₂ w b := by
  cases b <;> funext g <;> simp [two, intersection_update_fsHerm_neg_one, hw]

private theorem slot_pair_functions_eq {Z T : Finset (Pl E)} {w : Pl E} (hw : w ∉ Z) (hT : w ∈ T) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w false = (fun g => fn2 n 0 w (e₁ w) (g, 1)) ∧
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w true = (fun g => fn2 n 0 w (e₂ w) (g, 1)) := by
  constructor <;> funext g <;> simp [two, intersection_update_fsHerm_neg_one, hw, hT]

private theorem two_off {Z T : Finset (Pl E)} {w : Pl E} (hw : w ∉ Z) (hT : w ∉ T) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (b : Bool) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w b = (KGL w (n := n) : Set (GLw n w)).indicator 1 := by
  have key : ∀ g : GLw n w, (K2 n 0 w : Set (GLw n w × GLw 0 w)).indicator (1 : GLw n w × GLw 0 w → ℂ) (g, 1) =
      (KGL w (n := n) : Set (GLw n w)).indicator 1 g := by
    intro g
    by_cases hg : g ∈ KGL w (n := n)
    · rw [Set.indicator_of_mem, Set.indicator_of_mem] <;> simp [hg, K2, Subgroup.mem_prod]
    · rw [Set.indicator_of_notMem, Set.indicator_of_notMem] <;> simp [hg, K2, Subgroup.mem_prod]
  cases b <;> funext g <;> simpa [two, intersection_update_fsHerm_neg_one, hw, hT] using key g

private def slots (S : Set (Pl E)) (Z T : Finset (Pl E)) : Finset (Pl E × Bool) :=
  Z ×ˢ Finset.univ ∪ (T ×ˢ Finset.univ).filter (Sl S)

private theorem fam_positions (hEx : Ex2Act) {S : Set (Pl E)} {Z : Finset (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)}
    (hZ : SplitIn S Z) (hG : Good Z N) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (hφ : ∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) (T : Finset (Pl E)) (hT : Disjoint T Z)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) :
    Fam S N (slots S Z T) (two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)) := by
  constructor
  · intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · have hw := (Finset.mem_product.1 h).1
      refine ⟨⟨(hZ _ hw).1, fun _ => (hZ _ hw).2⟩, ?_⟩
      rw [two_in hw]
      exact hφ _ hw _
    · obtain ⟨h1, hs⟩ := Finset.mem_filter.1 h
      have hwT := (Finset.mem_product.1 h1).1
      have hwZ : i.1 ∉ Z := Finset.disjoint_left.1 hT hwT
      refine ⟨hs, ?_⟩
      rw [(hG i.1).2.2.2 hwZ]
      obtain ⟨w, b⟩ := i
      cases b
      · rw [(slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).1]
        exact (hEx E n w (e₁ w)).1
      · rw [(slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).2]
        exact (hEx E n w (e₂ w)).1
  · intro i hs hi
    have hwZ : i.1 ∉ Z := fun h => hi (Finset.mem_union_left _ (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩))
    have hwT : i.1 ∉ T := fun h => hi (Finset.mem_union_right _
      (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩, hs⟩))
    rw [two_off hwZ hwT, (hG i.1).2.2.2 hwZ]

private def cv (B : Pl E → Multiset ℂˣ) (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (i : Pl E × Bool) : ℂ :=
  if i.2 then ev2 n 0 i.1 (e₂ i.1) (inv (B (cPl i.1))) 0 else ev2 n 0 i.1 (e₁ i.1) (B i.1) 0

private theorem prod_cv {S : Set (Pl E)} (T : Finset (Pl E)) (B : Pl E → Multiset ℂˣ)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (hT : TEv S T e₂) :
    ∏ i ∈ (T ×ˢ Finset.univ).filter (Sl S), cv B e₁ e₂ i = val T e₁ e₂ B 0 := by
  rw [Finset.prod_filter, Finset.prod_product, val]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hS := hT.1 w hw
  rw [Fintype.prod_bool]
  by_cases hs : IsSplitAt w
  · have h1 : Sl S (w, true) := ⟨hS, fun _ => hs⟩
    have h2 : Sl S (w, false) := ⟨hS, by simp⟩
    simp [h1, h2, cv, inv, mul_comm]
  · have h1 : ¬ Sl S (w, true) := fun h => hs (h.2 rfl)
    have h2 : Sl S (w, false) := ⟨hS, by simp⟩
    have h3 : ev2 n 0 w (e₂ w) (inv (B (cPl w))) (inv ((0 : Pl E → Multiset ℂˣ) (cPl w))) = 1 := hT.2 w hw hs _
    simp only [h1, h2, if_true, if_false, cv, one_mul]
    rw [h3, mul_one]
    simp

private theorem off_of (hPl : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places) {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S)
    (hZ : SplitIn S Z) {w : Pl E} (hw : w ∈ S) (hwZ : w ∉ Z) : Off Z w ∧ Off Z (cPl w) := by
  have hc : cPl w ∉ Z := fun h => by
    have := ((hPl E).2.2.2 S hS w).2 hw (hZ _ h).1
    exact hwZ (this ▸ h)
  exact ⟨⟨hwZ, hc⟩, hc, by rwa [((hPl E).2.1 w).1]⟩

theorem tTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → PfHecke → ProdOp → LocComm → YLoc → Ex2Act → SatAll → TTr := by
  intro hPl hPf hPO hLC _ hEx hSat E _ _ _ n S Z N hS hZ hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hT
  have hF := fam_positions hEx hZ hG φ₁ φ₂ hφ T hTZ e₁ e₂
  have hF0 : Fam S N (Z ×ˢ Finset.univ) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂)) := by
    simpa [slots] using fam_positions (S := S) hEx hZ hG φ₁ φ₂ hφ ∅ (Finset.disjoint_empty_left _) e₁ e₂
  have hH := hPf E n S Z N hS hZ hG _ _ hF
  have hH0 := hPf E n S Z N hS hZ hG _ _ hF0
  refine ⟨hH, hF0, LinearMap.ext fun x => Subtype.ext ?_⟩
  have hxf := y.fix x.2
  rw [LinearMap.smul_apply, Submodule.coe_smul, y.act _ hH x, y.act _ hH0 x,
    hPO E n S Z N hS hZ hG _ _ hF _ hxf, hPO E n S Z N hS hZ hG _ _ hF0 _ hxf]
  set F := two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) with hFdef
  set L : Pl E × Bool → Module.End ℂ (Sm E n) := fun i => Lw N i.1 i.2 (F i.1 i.2) with hL
  have hd : Disjoint (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ((T ×ˢ Finset.univ).filter (Sl S)) := by
    refine Finset.disjoint_left.2 fun i h1 h2 => ?_
    exact Finset.disjoint_left.1 hTZ (Finset.mem_product.1 (Finset.mem_filter.1 h2).1).1 (Finset.mem_product.1 h1).1
  have hcomm : ∀ i ∈ (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S),
      ∀ k ∈ (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S), i ≠ k → Commute (L i) (L k) := by
    intro i hi k hk hik
    exact (hLC E n S Z N hS hZ hG i (hF.1 i hi).1 _ (hF.1 i hi).2).2 k (hF.1 k hk).1 hik _ (hF.1 k hk).2
  have hsame : ((Z ×ˢ Finset.univ : Finset (Pl E × Bool)).toList.map fun i =>
      Lw N i.1 i.2 (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) i.1 i.2)) =
      (Z ×ˢ Finset.univ : Finset (Pl E × Bool)).toList.map L := by
    refine List.map_congr_left fun i hi => ?_
    have hw := (Finset.mem_product.1 (Finset.mem_toList.1 hi)).1
    simp only [hL, hFdef, two_in hw]
  have heig : ∀ i ∈ ((T ×ˢ Finset.univ).filter (Sl S)).toList, L i x.1 = cv B e₁ e₂ i • x.1 := by
    intro i hi
    obtain ⟨h1, hs⟩ := Finset.mem_filter.1 (Finset.mem_toList.1 hi)
    have hwT := (Finset.mem_product.1 h1).1
    have hwZ : i.1 ∉ Z := Finset.disjoint_left.1 hTZ hwT
    by_cases hx0 : x.1 = 0
    · simp [hx0]
    have hmem : i ∈ slots S Z T := Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h1, hs⟩)
    have hfx := ((hLC E n S Z N hS hZ hG i hs _ (hF.1 i hmem).2).1 x.1 hxf).1
    rw [(hG i.1).2.2.2 hwZ] at hfx
    obtain ⟨ho, ho'⟩ := off_of hPl hS hZ hs.1 hwZ
    obtain ⟨w, b⟩ := i
    have hN : N w = KGL w (n := n) := (hG w).2.2.2 hwZ
    have hxV := y.le x.2
    cases b
    · have hv := (hSat E n π w (B w) x.1 hxV hx0).1 (hB w ho) hfx
      have := (hEx E n w (e₁ w)).2 _ _ x.1 (B w) hv
      simp only [hL, hFdef, (slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).1, cv, Lw, hN]
      simpa using this
    · have hv := (hSat E n π w (B (cPl w)) x.1 hxV hx0).2 (by
        have := hB (cPl w) ho'
        exact this) hfx
      have := (hEx E n w (e₂ w)).2 _ _ x.1 _ hv
      simp only [hL, hFdef, (slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).2, cv, Lw, hN]
      simpa using this
  have hI : slots S Z T = (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S) := rfl
  rw [hsame, hI, prod_split L _ _ hd hcomm, Module.End.mul_apply, list_eig L (cv B e₁ e₂) x.1 _ heig,
    Finset.prod_map_toList, prod_cv T B e₁ e₂ hT, map_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiTermOf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelG borelF borelA borelH

private theorem lev_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    {N N' : ∀ w : Pl E, Subgroup (GLw n w)} (h : ∀ w, N w ≤ N' w) : Lev S N ≤ Lev S N' := by
  intro g hg
  simp only [Lev, Subgroup.mem_iInf] at hg ⊢
  exact fun i => h _ (hg i)

private theorem level_term (h1 : ThetaFixedGlobalWeights) (h3 : LevTop) (h6 : ToYd) (h7 : LevelTr)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n) (π : CuspSub E n)
    (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (lamE : (E →+* ℂ) → DomWeight n)
    (hlam : ∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))) {S : Set (Pl E)} (hS : IsSection S)
    {Z : Finset (Pl E)} (hZ : SplitIn S Z) {B : Pl E → Multiset ℂˣ} {τ : ∀ w : Pl E, SmIrr (GLw n w)}
    (hB : ∀ w, Off Z w → (CG.mk π).HasSat w (B w)) (hτ : ∀ w ∈ Z, π.IsLocComp w (τ w))
    {u : GL (Fin n) E} (hu : IsTransl u) (μC : Measure (G n)) (μ : Measure (H E n 0))
    [μC.IsHaarMeasure] [μ.IsHaarMeasure] {N : ∀ w : Pl E, Subgroup (GLw n w)} (hN : Good Z N)
    (hfix : ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ Lev S N, finRep E n k ψ = ψ) :
    (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
      (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
        (k : ∀ v : InfinitePlace E, Mat n → ((lefE n (lamE v.embedding).w).V →L[ℂ] (lefE n (lamE v.embedding).w).V))
        (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
        TEv S T e₂ → (∀ v : InfinitePlace E, IsMult μC (lefE n (lamE v.embedding).w) (k v) (vl v) R) →
        IsTwTr μ π (phiProd (fun v => (lamE v.embedding).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
          (c * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
            (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0) := by
  obtain ⟨hKo, hKc, -, -⟩ := h3 E n S Z N hS hZ hN
  obtain ⟨hKθ, hY⟩ := h6 E n S Z N hS hZ hN π u hu
  let K₀ : TopologicalSpace.PositiveCompacts (GF E n) :=
    ⟨⟨(Lev S N : Set (GF E n)), hKc⟩, by
      show (interior (Lev S N : Set (GF E n))).Nonempty
      rw [hKo.interior_eq]
      exact ⟨1, (Lev S N).one_mem⟩⟩
  let μf : Measure (GF E n) := Measure.haarMeasure K₀
  haveI : μf.IsHaarMeasure := inferInstance
  obtain ⟨Y, ρ, A, cK, hYπ, hfd, hne, hYfix, hact, hsimple, hsq, htw, hcK, htr⟩ :=
    h1 E n hn π hreg hd lamE hlam (Lev S N) hKo hKc hKθ hfix μC μf μ
  obtain ⟨y, v, hv, hyv⟩ := hY μf inferInstance Y ρ A hYπ hfd hne hYfix hact hsimple hsq htw
  obtain ⟨href, d, hd0, hdtr⟩ := h7 E n S Z N hS hZ hN π y B τ hB hτ
  refine ⟨href, cK * v * d, mul_ne_zero (mul_ne_zero hcK hv) hd0, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨hH, hTr⟩ := hdtr φ₁ φ₂ hφ T hT e₁ e₂ hE
  obtain ⟨hHF, hTrY⟩ := hyv _ hH
  have key := htr k vl (fun _ => R) hM _ hHF
  rw [hTrY, hTr] at key
  have e : cK * (∏ w : InfinitePlace E, vl w (infOf (lamE w.embedding).w)) *
      (v * (d * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)) =
      cK * v * d * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
        (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0 := by ring
  rw [e] at key
  exact key

theorem piTerm_of_weights_levels :
    ThetaFixedGlobalWeights → WtEx → LevTop → LevFix → LcLevel → ToYd → LevelTr → TwUniq → PiTerm := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 E _ _ _ _ n hn π hreg hd
  obtain ⟨lamE, hlam⟩ := h2 E n π hreg
  refine ⟨fun v => lamE v.embedding, fun v => hlam _, ?_⟩
  intro S hS Z hZ B τ hB hτ u hu μC μ _ _
  obtain ⟨N₀, hN₀, ψ, hψ, hψ0, hψfix⟩ := h4 E n π S Z hS hZ fun w hw => ⟨B w, hB w hw⟩
  obtain ⟨⟨φr, hr, hrne⟩, c₀, hc₀, hlev₀⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN₀
    ⟨ψ, hψ, hψ0, hψfix⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨N, hN, hle, hHecke⟩ := h5 E n Z N₀ hN₀ φ₁ φ₂ hφ
  obtain ⟨-, c, -, hlev⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN
    ⟨ψ, hψ, hψ0, fun g hg => hψfix g (lev_mono S hle hg)⟩
  have main := hlev φ₁ φ₂ hHecke T hT e₁ e₂ k vl R hE hM
  by_cases hP : (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) = 0
  · rw [hP] at main ⊢
    simpa using main

  have hcc : c = c₀ := by
    let e : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)) := fun _ => Ex.one
    have hEe : TEv S (∅ : Finset (Pl E)) e := ⟨by simp, by simp⟩
    have a₀ := hlev₀ φr φr (fun w hw b => hr w hw (N₀ w) le_rfl b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have a₁ := hlev φr φr (fun w hw b => hr w hw (N w) (hle w) b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have heq := h8 E n μ π _ _ _ a₁ a₀
    simp only [val, Finset.prod_empty, mul_one] at heq
    exact mul_right_cancel₀ hP (mul_right_cancel₀ hrne heq)
  rw [hcc] at main
  exact main

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.HeckeComp
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F
open PositivityTheory.RgTw (Mat G)

private theorem hecke_comp {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {φ : G → G} (hc : Continuous φ)
    (hi : ∀ g, φ (φ g) = g) (hm : ∀ a b, φ (a * b) = φ a * φ b) (hK : ∀ k ∈ K, φ k ∈ K) {h : G → ℂ}
    (hh : IsHecke K h) : IsHecke K (fun g => h (φ g)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · let e : G ≃ₜ G :=
      { toFun := φ, invFun := φ, left_inv := hi, right_inv := hi,
        continuous_toFun := hc, continuous_invFun := hc }
    exact hh.1.comp_homeomorph e
  · simp only [hm]
    exact hh.2 _ (hK k hk) _

private theorem core {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (hS : LvShift) (ρ : Representation ℂ G V) (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (u : G) (hu : ∀ x, x ∈ K ↔ u * x * u⁻¹ ∈ K) (θ : G → G)
    (hθc : Continuous θ) (hθi : ∀ g, θ (θ g) = g) (hθm : ∀ a b, θ (a * b) = θ a * θ b) (hθK : ∀ k ∈ K, θ k ∈ K)
    (hθu : θ u = u⁻¹) (Y : Submodule ℂ V) (hY : Y ≤ fixed ρ K) (r : (G → ℂ) → Module.End ℂ Y)
    (hact : ∀ h, IsHecke K h → ∀ y : Y, (r h y : V) = Lv ρ K h y)
    (A : Module.End ℂ Y) (hAA : A * A = 1)
    (hA : ∀ h, IsHecke K h → A * r h = r (fun g => h (θ g)) * A) :
    (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) = 1 ∧
    (∀ h, IsHecke K h → (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A) * r h =
      r (fun g => h (u * θ g * u⁻¹)) * (r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) * A)) ∧
    ∀ h, IsHecke K h → IsHecke K (fun g => h (g * u⁻¹)) ∧
      r (fun g => h (g * u⁻¹)) = r h * r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) := by
  have h0 : IsHecke K (0 : G → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have Sh := hS G V ρ K ho hc
  have hI : IsHecke K ((K : Set G).indicator 1) := (Sh u hu 0 h0).2.2.1
  have hu' : ∀ x, x ∈ K ↔ u⁻¹ * x * u⁻¹⁻¹ ∈ K := fun x => by
    rw [hu (u⁻¹ * x * u⁻¹⁻¹)]
    simp [mul_assoc]

  have a1 : ∀ v : G, (∀ x, x ∈ K ↔ v * x * v⁻¹ ∈ K) → ∀ y : Y,
      (r (fun g => (K : Set G).indicator 1 (v⁻¹ * g)) y : V) = ρ v y := fun v hv y => by
    obtain ⟨-, hl, -, -⟩ := Sh v hv _ hI
    obtain ⟨-, -, e1, e2⟩ := (Sh v hv _ hI).2.2.2 y (hY y.2)
    rw [hact _ hl, e1, e2]
  set Ru := r (fun g => (K : Set G).indicator 1 (u⁻¹ * g)) with hRu
  set Ru' := r (fun g => (K : Set G).indicator 1 (u * g)) with hRu'
  have b1 : ∀ y : Y, (Ru y : V) = ρ u y := a1 u hu
  have b2 : ∀ y : Y, (Ru' y : V) = ρ u⁻¹ y := fun y => by
    have := a1 u⁻¹ hu' y
    simpa only [inv_inv] using this
  have hRR : Ru * Ru' = 1 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show (Ru (Ru' y) : V) = y
    rw [b1, b2, ← Module.End.mul_apply, ← map_mul]
    simp
  have hAR : A * Ru = Ru' * A := by
    rw [hRu, hA _ (Sh u hu _ hI).2.1, hRu']
    congr 2
    funext g
    have e : u⁻¹ * θ g = θ (u * g) := by rw [hθm, hθu]
    have m : θ (u * g) ∈ K ↔ u * g ∈ K :=
      ⟨fun h => by simpa only [hθi] using hθK _ h, hθK _⟩
    rw [e]
    by_cases c : u * g ∈ K
    · rw [Set.indicator_of_mem (by exact_mod_cast m.2 c), Set.indicator_of_mem (by exact_mod_cast c)]
      rfl
    · rw [Set.indicator_of_notMem (by exact_mod_cast fun d => c (m.1 d)), Set.indicator_of_notMem (by exact_mod_cast c)]
  have hθu' : θ u⁻¹ = u := by rw [← hθu, hθi]
  refine ⟨?_, fun h hh => ?_, fun h hh => ?_⟩
  · calc (Ru * A) * (Ru * A) = Ru * (A * Ru) * A := by simp only [mul_assoc]
      _ = (Ru * Ru') * (A * A) := by rw [hAR]; simp only [mul_assoc]
      _ = 1 := by rw [hRR, hAA, one_mul]
  · have hf : IsHecke K (fun g => h (θ g)) := hecke_comp hθc hθi hθm hθK hh
    have hf' : IsHecke K (fun g => h (u * θ g * u⁻¹)) := by
      refine hecke_comp (φ := fun g => u * θ g * u⁻¹) (by fun_prop) (fun g => ?_) (fun a b => ?_) (fun k hk => ?_) hh
      · show u * θ (u * θ g * u⁻¹) * u⁻¹ = g
        rw [hθm, hθm, hθu, hθu', hθi]
        group
      · show u * θ (a * b) * u⁻¹ = u * θ a * u⁻¹ * (u * θ b * u⁻¹)
        rw [hθm]
        group
      · exact (hu _).1 (hθK k hk)
    have e : Ru * r (fun g => h (θ g)) = r (fun g => h (u * θ g * u⁻¹)) * Ru := by
      refine LinearMap.ext fun y => Subtype.ext ?_
      show (Ru (r (fun g => h (θ g)) y) : V) = (r (fun g => h (u * θ g * u⁻¹)) (Ru y) : V)
      obtain ⟨p1, p2, -⟩ := Sh u hu _ hf
      obtain ⟨q1, q2, -⟩ := Sh u hu _ hf'
      obtain ⟨-, -, e1, -⟩ := (Sh u hu _ hf).2.2.2 y (hY y.2)
      obtain ⟨-, e2, -, -⟩ := (Sh u hu _ hf').2.2.2 y (hY y.2)
      have ef : (fun g => h (θ (u⁻¹ * g))) = fun g => h (u * θ (g * u⁻¹) * u⁻¹) := by
        funext g
        rw [hθm, hθm, hθu']
        congr 1
        group
      rw [b1, hact _ hf, hact _ hf', b1, ← e1, ← e2, ef]
    calc (Ru * A) * r h = Ru * (A * r h) := by rw [mul_assoc]
      _ = (Ru * r (fun g => h (θ g))) * A := by rw [hA h hh, mul_assoc]
      _ = r (fun g => h (u * θ g * u⁻¹)) * (Ru * A) := by rw [e, mul_assoc]
  · obtain ⟨p1, -⟩ := Sh u hu h hh
    refine ⟨p1, LinearMap.ext fun y => Subtype.ext ?_⟩
    show (r (fun g => h (g * u⁻¹)) y : V) = (r h (Ru y) : V)
    obtain ⟨-, e2, -, -⟩ := (Sh u hu h hh).2.2.2 y (hY y.2)
    rw [hact _ p1, hact _ hh, b1, e2]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.toYd_pf :
    SlotBasic → LevTop → TranslF → HeckeSum → LvShift → ToYd := by
  intro hSl hLT hTF hHS hLS E _ _ _ n S Z N hS hZ hG π u hu
  obtain ⟨hO, hC, -, hNm⟩ := hLT E n S Z N hS hZ hG
  obtain ⟨t1, t2, κ, hκ, t3⟩ := hTF E n u hu
  have hinv := (hSl E n S hS).1
  have hcont := (hSl E n S hS).2.1
  have hthe : ∀ g, thetaF E n g = (ratF E n u)⁻¹ * thF E n g * ratF E n u := by
    intro g
    rw [t1 g]
    group
  have hnorm : ∀ x, x ∈ Lev S N ↔ ratF E n u * x * (ratF E n u)⁻¹ ∈ Lev S N := by
    intro x
    rw [t3 x]
    refine ⟨hNm κ hκ x, fun hx => ?_⟩
    have := hNm κ⁻¹ ((Kf E n).inv_mem hκ) _ hx
    simpa [mul_assoc] using this
  have hθK : ∀ k ∈ Lev S N, thetaF E n k ∈ Lev S N := by
    intro k hk
    refine (hnorm _).2 ?_
    have e : ratF E n u * thetaF E n k * (ratF E n u)⁻¹ = thF E n k := (t1 k).symm
    rw [e]
    exact (hLT E n S Z N hS hZ hG).2.2.1 k hk
  refine ⟨hθK, ?_⟩
  intro μf hμ Y ρ A hYπ hfd hne hfix hAct hsim hAA hAθ
  have hθm : ∀ a b, thetaF E n (a * b) = thetaF E n a * thetaF E n b := by
    intro a b
    simp only [hthe, map_mul]
    group
  have hθi : ∀ g, thetaF E n (thetaF E n g) = g := by
    intro g
    simp only [hthe, map_mul, map_inv, t2, hinv]
    group
  have hθu : thetaF E n (ratF E n u) = (ratF E n u)⁻¹ := by
    rw [hthe, t2]
    group
  have hθc : Continuous (thetaF E n) := by
    have : thetaF E n = fun g => (ratF E n u)⁻¹ * thF E n g * ratF E n u := funext hthe
    rw [this]
    exact (continuous_const.mul hcont).mul continuous_const
  have hv : (μf (Lev S N : Set (GF E n))).toReal ≠ 0 := by
    haveI := hμ
    exact (ENNReal.toReal_pos (hO.measure_pos μf ⟨1, (Lev S N).one_mem⟩).ne' hC.measure_lt_top.ne).ne'
  obtain ⟨v, hvdef⟩ : ∃ v : ℂ, v = (((μf (Lev S N : Set (GF E n))).toReal : ℝ) : ℂ) := ⟨_, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact_mod_cast hv
  have toF : ∀ {h : GF E n → ℂ}, IsHecke (Lev S N) h → IsHeckeF (Lev S N) h := fun hh =>
    ⟨hh.1, fun k₁ h₁ k₂ h₂ g => by rw [(hh.2 _ h₂ _).2, (hh.2 _ h₁ _).1]⟩
  have toH : ∀ {h : GF E n → ℂ}, IsHeckeF (Lev S N) h → IsHecke (Lev S N) h := fun hh =>
    ⟨hh.1, fun k hk x => ⟨by simpa using hh.2 k hk 1 (Lev S N).one_mem x,
      by simpa using hh.2 1 (Lev S N).one_mem k hk x⟩⟩
  have hY : Y ≤ fixed (finRep E n) (Lev S N) := fun y hy k => by
    simpa using hfix y hy k k.2
  have hact : ∀ h, IsHecke (Lev S N) h → ∀ y : Y,
      (((v⁻¹ • ρ h : Module.End ℂ Y) y : Y) : Sm E n) = Lv (finRep E n) (Lev S N) h y := by
    intro h hh y
    have e : ((ρ h y : Y) : Sm E n) = v • Lv (finRep E n) (Lev S N) h y := by
      refine Subtype.ext ?_
      have e1 := hAct h (toF hh) y
      have e2 := hHS E n (Lev S N) hO hC μf hμ h hh y (hY y.2)
      rw [e1, e2, hvdef]
      rfl
    show ((v⁻¹ • (ρ h y) : Y) : Sm E n) = _
    rw [Submodule.coe_smul, e, inv_smul_smul₀ hv0]
  obtain ⟨c1, c2, c3⟩ := core hLS (finRep E n) (Lev S N) hO hC (ratF E n u) hnorm (thetaF E n) hθc hθi hθm hθK hθu
    Y hY (fun h => v⁻¹ • ρ h) hact A hAA (fun h hh => by
      rw [mul_smul_comm, smul_mul_assoc, hAθ h (toF hh)])
  refine ⟨⟨Y, fun h => v⁻¹ • ρ h, _, hYπ, hfd, hne, hY, hact, ?_, c1, ?_⟩, v, hv0, fun h hh =>
    ⟨toF (c3 h hh).1, ?_⟩⟩
  · intro W hW
    refine hsim W fun h hh y hy => ?_
    exact (W.smul_mem_iff (inv_ne_zero hv0)).1 (hW h (toH hh) y hy)
  · intro h hh
    have e : (fun g => h (thF E n g)) = fun g => h (ratF E n u * thetaF E n g * (ratF E n u)⁻¹) :=
      funext fun g => by rw [t1 g]
    show _ * _ = (v⁻¹ • ρ (fun g => h (thF E n g))) * _
    rw [e]
    exact c2 h hh
  · have e2 : v⁻¹ • ρ (fun g => h (g * (ratF E n u)⁻¹)) = (v⁻¹ • ρ h) *
        (v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) := (c3 h hh).2
    have key : ρ (fun g => h (g * (ratF E n u)⁻¹)) * A = v • ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [← mul_assoc, ← e2, smul_mul_assoc, smul_inv_smul₀ hv0]
    have tr : LinearMap.trace ℂ Y (ρ (fun g => h (g * (ratF E n u)⁻¹)) * A) = v * LinearMap.trace ℂ Y ((v⁻¹ • ρ h) *
        ((v⁻¹ • ρ (fun g => (Lev S N : Set (GF E n)).indicator 1 ((ratF E n u)⁻¹ * g))) * A)) := by
      rw [key, LinearMap.map_smul, smul_eq_mul]
    exact tr
end

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem slotFacts : SlotBasic := slotFacts_pf places
theorem levTop : LevTop := levTop_pf slotFacts
theorem levFix : LevFix := levFix_pf places slotFacts (jointFix_pf slotFacts)
theorem toYd : ToYd := toYd_pf slotFacts levTop translF_pf heckeSum_pf lvShift_pf
theorem pfHecke : PfHecke := pfHecke_pf slotFacts levTop
theorem prodOp : ProdOp := prodOp_pf slotFacts levTop absStep_pf pfHecke
theorem locComm : LocComm := locComm_pf slotFacts levTop
theorem yLoc : YLoc := yLoc_pf pfHecke prodOp
theorem zSimple : ZSimple := zSimple_pf (genLoc_pf slotFacts levTop pfHecke prodOp) locComm (sphOp_pf cvOp) yLoc
theorem zTr : ZTr := zTr_pf adm pfHecke prodOp locComm yLoc zSimple (ySwap_pf slotFacts pfHecke prodOp) (isot_pf slotFacts)
  (simpleFix_pf cvOp) (absCore_pf traceForm_pf)
theorem tTr : TTr := tTr_pf places pfHecke prodOp locComm yLoc (ex2Act_pf exAct) satAll_pf
theorem levelTr : LevelTr := levelTr_pf adm zTr (seenTr_pf trLevel adm cvOp) tTr

theorem piTerm_eq_traceSum_of_degreeFourTest (h : ThetaFixedGlobalWeights) : PiTerm := piTerm_of_weights_levels h wtEx_pf levTop levFix lcLevel_pf toYd levelTr twUniq_pf

theorem piTerm_of (h : ThetaFixOf) : PiTerm := piTerm_eq_traceSum_of_degreeFourTest (aux_statement_11 UpperTheory.V.Z.GSp4Splitting.global_haarAverage_trace_identity h)

theorem piTerm_holds : PiTerm := piTerm_of UpperTheory.V.Z.Tf.GOne.thetaFixOf

theorem cvIn : CvIn := cvIn_pf basic_pf (aeEq_pf basic_pf)
theorem wtInd : WtInd := wtInd_pf basic_pf
theorem typeIn : TypeIn := typeIn_pf piAdm_pf detZero_pf evalBasis_pf cvIn (formEx_pf basic_pf (aeEq_pf basic_pf) wtInd)
  (orthZero_pf basic_pf (aeEq_pf basic_pf) wtInd) absType_pf

theorem piFin_holds : PiFin := piFinOf_pf piAdm_pf tensType_pf (cvType_pf detZero_pf evalBasis_pf) cvIn typeIn

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
