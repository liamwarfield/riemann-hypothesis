module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLieOp

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.RealLift

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem actsD_zero' (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _


open scoped Classical in
theorem actsD_comb (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f + g) ⇑(c • f₁ + g₁) := by
  have e : ∀ (r : (κ → AF F) → ℂ) (φ ψ : SInf F κ),
      tens (evI F) ⇑(c • φ + ψ) r = c • tens (evI F) ⇑φ r + tens (evI F) ⇑ψ r := by
    intro r φ ψ; funext y; simp [tens]; ring
  have key : ∀ r, Rest (evI F) ⇑f r → Rest (evI F) ⇑g r → ∀ x,
      HasDerivAt (fun t => L t (tens (evI F) ⇑(c • f + g) r) x) (tens (evI F) ⇑(c • f₁ + g₁) r x) 0 := by
    intro r h1 h2 x
    rw [e, e]
    have h := ((hf r h1 x).const_mul c).add (hg r h2 x)
    have hfun : (fun t => L t (c • tens (evI F) ⇑f r + tens (evI F) ⇑g r) x) =
        (fun t => c * L t (tens (evI F) ⇑f r) x) + (fun t => L t (tens (evI F) ⇑g r) x) := by
      funext t; simp [map_add (f := _), map_smul]
    rw [hfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h

  set g₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl
  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r₀ := fun φ =>
    ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨φ, g₀, hg₀, rfl⟩⟩
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  intro r hr x
  by_cases h0 : c • f + g = 0
  · have hz : c • f₁ + g₁ = 0 := by
      ext a
      have h := key r₀ (hrest₀ f) (hrest₀ g) (ptAt a 0)
      rw [h0, hzeroT] at h
      simp only [map_zero, Pi.zero_apply] at h
      have h' := h.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
      rw [htens₀, pureA_ptAt, hg₀0, mul_one] at h'
      simpa using h'
    rw [h0, hz, hzeroT]
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const _ _
  · have hR : (fun y => r (fun i => ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F), y i))) ∈ SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :=
      mem_SB_of_pureA_mem h0 (tens_eq_pureA _ hr.1 ▸ hr.2)
    have hrest : ∀ φ : SInf F κ, Rest (evI F) ⇑φ r := fun φ =>
      ⟨hr.1, by rw [tens_eq_pureA _ hr.1]; exact Submodule.subset_span ⟨φ, _, hR, rfl⟩⟩
    exact key r (hrest f) (hrest g) x

theorem actsD_add (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f f₁ g g₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) (hg : ActsD (evI F) (fun t => ⇑(L t)) ⇑g ⇑g₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(f + g) ⇑(f₁ + g₁) := by
  simpa only [one_smul] using actsD_comb L 1 hf hg

theorem actsD_smul (L : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ) {f f₁ : SInf F κ}
    (hf : ActsD (evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁) :
    ActsD (evI F) (fun t => ⇑(L t)) ⇑(c • f) ⇑(c • f₁) := by
  simpa only [add_zero] using actsD_comb L c hf (actsD_zero' L)

end GlobalTheory.RealLieOp

theorem GlobalTheory.RealLieOp.exists_realOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∃ T : Module.End ℂ R.Pi,
      (∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f₁ = T (R.p f)) ∧
      ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p' f₁' = T (R.p' f') := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM γ hγ
  let L : ℝ → Module.End ℂ ((Fin a × Fin (a + a') → AF F) → ℂ) := fun t => om (1, γ (Multiplicative.ofAdd t))
  let L' : ℝ → Module.End ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) := fun t => om' (1, γ (Multiplicative.ofAdd t))
  let S : Set (R.Pi × R.Pi) :=
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ z = (R.p f, R.p f₁)} ∪
    {z | ∃ f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')), f ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f ⇑f₁ ∧ z = (R.p' f, R.p' f₁)}
  have hspan : ∀ z ∈ Submodule.span ℂ S, ∃ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (f' f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L t)) ⇑f ⇑f₁ ∧ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑f' ⇑f₁' ∧
      z = (R.p f + R.p' f', R.p f₁ + R.p' f₁') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨f, f₁, hf, h1, rfl⟩ | ⟨f, f₁, hf, h1, rfl⟩
      · exact ⟨f, f₁, 0, 0, hf, h1, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', by simp⟩
      · exact ⟨0, 0, f, f₁, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, hf, h1, by simp⟩
    | zero => exact ⟨0, 0, 0, 0, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L, zero_mem _, GlobalTheory.RealLieOp.actsD_zero' L', Prod.ext (by simp) (by simp)⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      obtain ⟨g, g₁, g', g₁', hg, h2, hg', h2', rfl⟩ := hy
      refine ⟨f + g, f₁ + g₁, f' + g', f₁' + g₁', add_mem hf hg, GlobalTheory.RealLieOp.actsD_add L h1 h2,
        add_mem hf' hg', GlobalTheory.RealLieOp.actsD_add L' h1' h2', ?_⟩
      simp only [map_add (f := _), Prod.mk_add_mk]
      abel_nf
    | smul c x _ hx =>
      obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hx
      refine ⟨c • f, c • f₁, c • f', c • f₁', Submodule.smul_mem _ c hf, GlobalTheory.RealLieOp.actsD_smul L c h1,
        Submodule.smul_mem _ c hf', GlobalTheory.RealLieOp.actsD_smul L' c h1', ?_⟩
      simp only [map_smul, Prod.smul_mk, smul_add]
  have hgraph : ∀ z ∈ Submodule.span ℂ S, z.1 = 0 → z.2 = 0 := by
    intro z hz hz0
    obtain ⟨f, f₁, f', f₁', hf, h1, hf', h1', rfl⟩ := hspan z hz
    have e : R.p f + R.p' f' = 0 := hz0
    have e2 : R.p f = R.p' (-f') := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left e
    have hn : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => ⇑(L' t)) ⇑(-f') ⇑(-f₁') := by
      simpa only [neg_one_smul] using GlobalTheory.RealLieOp.actsD_smul L' (-1) h1'
    have := hM.real.lie γ hγ f hf (-f') (neg_mem hf') f₁ (-f₁') h1 hn e2
    show R.p f₁ + R.p' f₁' = 0
    rw [this, map_neg, neg_add_cancel]
  obtain ⟨T, hT⟩ := LinearMap.exists_extend (Submodule.span ℂ S).toLinearPMap.toFun
  have hT' : ∀ z ∈ Submodule.span ℂ S, T z.1 = z.2 := by
    intro z hz
    have hz' : z ∈ (Submodule.span ℂ S).toLinearPMap.graph := by
      rw [Submodule.toLinearPMap_graph_eq _ hgraph]; exact hz
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hz'
    rw [← hy1, ← hy2]
    exact LinearMap.congr_fun hT y
  refine ⟨T, fun f hf f₁ h1 => ?_, fun f hf f₁ h1 => ?_⟩
  · exact (hT' (R.p f, R.p f₁) (Submodule.subset_span (Or.inl ⟨f, f₁, hf, h1, rfl⟩))).symm
  · exact (hT' (R.p' f, R.p' f₁) (Submodule.subset_span (Or.inr ⟨f, f₁, hf, h1, rfl⟩))).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_lie_operator_theta_quotient_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∃ T : Module.End ℂ R.Pi,
      (∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f₁ = T (R.p f)) ∧
      ∀ f' ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f' f₁' → R.p' f₁' = T (R.p' f') := by
  first | exact @GlobalTheory.RealLieOp.exists_realOp | exact GlobalTheory.RealLieOp.exists_realOp | (intros; apply GlobalTheory.RealLieOp.exists_realOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.AlgStable

theorem isStable_span {D : D7} (θ : InfFam D) (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ))
    (s : Set (Z → ℂ)) (h1 : ∀ g ∈ GfC X, ∀ Φ ∈ s, ρ g Φ ∈ Submodule.span ℂ s)
    (h2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ s, ∃ Φ' ∈ Submodule.span ℂ s, GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X ρ τ Y Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsStable θ X ρ (Submodule.span ℂ s) := by
  refine ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩
  · have hle : Submodule.span ℂ s ≤ (Submodule.span ℂ s).comap (ρ g) := Submodule.span_le.2 (h1 g hg)
    exact hle hΦ
  · induction hΦ using Submodule.span_induction with
    | mem x hx => exact h2 τ Y hY x hx
    | zero =>
      refine ⟨0, zero_mem _, fun z => ?_⟩
      simp only [map_zero]
      exact hasDerivAt_const _ _
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', dx⟩ := hx
      obtain ⟨y', hy', dy⟩ := hy
      refine ⟨x' + y', add_mem hx' hy', fun z => ?_⟩
      simp only [map_add (f := _)]
      exact (dx z).add (dy z)
    | smul a x _ hx =>
      obtain ⟨x', hx', dx⟩ := hx
      refine ⟨a • x', Submodule.smul_mem _ a hx', fun z => ?_⟩
      simp only [map_smul]
      exact (dx z).const_mul a

theorem isVacF_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (A : Fr S)
    (B : Fr T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {g : GA D S} (hg : g ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) {f : WO S T → ℂ}
    (hf : IsVacF ψ θ A B f) : IsVacF ψ θ A B (om (g, h) f) := by
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hW hθ g h τ z hf.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (inv_mem hg), Matrix.one_mul, Matrix.mul_one]
  refine ⟨hW.om_pres _ f hf.1, fun τ z => ?_⟩
  have h0 := hf.2 τ z
  unfold annih at h0 ⊢
  rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]

theorem algF_isStable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (Am : Fr M) (Bx : Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
      IsStable θ M (fun g => ω (g, 1)) (algF ψ θ ε Am Bx) ∧ IsStable θ X (fun h => ω (1, h)) (algF ψ θ ε Am Bx) := by
  intro D ψ θ _ hθ ε M X A B χ χ' ω hW
  have hW' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e0 : ∀ (g : GA D (sgn ε M)) (h : GA D X), (ω.toSgn ε) (g, h) = ω (ofSgn ε M g, h) := fun _ _ => rfl
  have hfin : ∀ g ∈ GfC M, ∀ h ∈ GfC X, ∀ f P, IsFinF ψ θ ε A B f →
      ω (g, h) (fockF ψ θ ε A B f P) ∈ algF ψ θ ε A B := by
    intro g hg h hh f P hf
    have hg' : (ofSgn ε M).symm g ∈ GfC (sgn ε M) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]; exact hg
    have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χ χ' (ω.toSgn ε) hW' θ hθ _ hg' h hh
      (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
    have hv := isVacF_om hθ (frSgn ε A) B hW' hg' hh hf
    rw [e0, MulEquiv.apply_symm_apply] at ht hv
    have : ω (g, h) (fockF ψ θ ε A B f P) = fockF ψ θ ε A B (ω (g, h) f) P := ht
    rw [this]
    exact hmem _ _ hv
  have hL := fun τ => GlobalTheory.LieFock.lieFockUpTo D (sgn ε M) X (frSgn ε A) B θ ψ χ χ' (ω.toSgn ε) τ hθ hW'
  refine ⟨isStable_span θ M _ _ ?_ ?_, isStable_span θ X _ _ ?_ ?_⟩
  · rintro g hg _ ⟨f, P, hf, rfl⟩
    exact hfin g hg 1 (one_mem _) f P hf
  · rintro τ Z hZ _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
    have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
      intro t
      rw [e0]
      unfold oneP
      rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
    have h := (hκ f hf).1 Z hZ' P
    simp only [e] at h
    exact ⟨_, hmem f _ hf, h⟩
  · rintro h hh _ ⟨f, P, hf, rfl⟩
    exact hfin 1 (one_mem _) h hh f P hf
  · rintro τ Y hY _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := fun h => by rw [e0, map_one]
    have h := (hκ f hf).2 Y hY P
    simp only [e1] at h
    exact ⟨_, hmem f _ hf, h⟩

end GlobalTheory.AlgStable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLieStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (Am : Fr M) (Bx : Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
      IsStable θ M (fun g => ω (g, 1)) (algF ψ θ ε Am Bx) ∧ IsStable θ X (fun h => ω (1, h)) (algF ψ θ ε Am Bx) := by
  first | exact @GlobalTheory.AlgStable.algF_isStable | exact GlobalTheory.AlgStable.algF_isStable | (intros; apply GlobalTheory.AlgStable.algF_isStable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOneParamLineTransposeGramUnitar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOneParamLineTransposeGramUnitar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TransportedLine

variable {D : D7}

theorem exp_mem_UH_of_lie {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit H.det) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * H + H * X = 0) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : (t • X)ᴴ = H * (-(t • X)) * H⁻¹ := by
    have h1 : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Xᴴ = -(H * X) * H⁻¹ := by rw [← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * H * NormedSpace.exp (t • X) = H
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem gramAt_det_isUnit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
  rw [this]
  exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit

variable (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e)

def toUXHom : GA D X →* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := GlobalTheory.TripleRead.toUX X e hJ
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X 1).submatrix e e = 1
    simp [Formalism.L2.Theta.mt]
  map_mul' a b := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X (a * b)).submatrix e e = (mt X a).submatrix e e * (mt X b).submatrix e e
    simp [Formalism.L2.Theta.mt, Matrix.submatrix_mul_equiv]

theorem continuous_toUX : Continuous (GlobalTheory.TripleRead.toUX X e hJ) := by
  have hm : Continuous fun g : GA D X => (matHom X g) := continuous_subtype_val
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · have hv : Continuous fun g : GA D X =>
        (matHom X g).1 := Units.continuous_val.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)
  · have hv : Continuous fun g : GA D X =>
        ((matHom X g)⁻¹).1 := Units.continuous_coe_inv.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)).congr fun g => ?_
    show ((matHom X g)⁻¹).1 (e i) (e j) = (mt X g⁻¹) (e i) (e j)
    simp [Formalism.L2.Theta.mt]

def finIncl (F : Type) [Field F] [NumberField F] : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F →ₗ[F] AF F where
  toFun a := ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((0, a + b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((0, b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((0, c • a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_snd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0) : u • x = 0 := by
  let e : AF F := ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have h1 : (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = 0 :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have hu' : u = u * e := by
    refine Prod.ext ?_ ?_
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 * 0
      rw [mul_zero]; exact h1
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 * 1
      rw [mul_one]
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (finIncl F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        ((0, (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).2) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact zero_mul _
      · exact one_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_smul, key, hx, map_zero, smul_zero]

theorem toUX_mem_UAt (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    {g : GA D X} (hg : g ∈ GinfC X) :
    GlobalTheory.TripleRead.toUX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have h1 : (finHom X g).val = 1 := by rw [show finHom X g = 1 from hg]; rfl
  have hM : ∀ a b, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 := by
    intro a b
    have e2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 ((congrArg id e2).trans ?_)
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.TripleRead.toUX X e hJ g) - 1 = (Formalism.L2.Theta.mt X g - 1).submatrix e e := by
    show (Formalism.L2.Theta.mt X g).submatrix e e - 1 = _
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_snd _ _ _ (hM _ _) u hu

theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end GlobalTheory.TransportedLine

namespace GlobalTheory.TransportedLine

theorem exists_line_toUX_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau),
    ∀ Y ∈ lieAt X τ, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Z,
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t) := by
  intro D θ hθ X k e Z hJ τ Y hY
  have hU : ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D X τ) :=
    exp_mem_UH_of_lie (gramAt_det_isUnit X τ) hY
  let φ : Multiplicative ℝ →* GA D X :=
    { toFun := fun t => oneP θ X τ Y (Multiplicative.toAdd t)
      map_one' := by
        show atTau θ X τ (NormedSpace.exp ((0 : ℝ) • Y)) = 1
        rw [zero_smul, NormedSpace.exp_zero]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ X τ
      map_mul' := fun s t => by
        show atTau θ X τ (NormedSpace.exp ((Multiplicative.toAdd s + Multiplicative.toAdd t) • Y)) =
          atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd s • Y)) * atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd t • Y))
        rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
        exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ X τ (hU _) (hU _) }
  refine ⟨(toUXHom X e hJ).comp φ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · have hc : Continuous fun t : ℝ => oneP θ X τ Y t :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ X τ).comp_continuous (continuous_exp_smul Y) hU
    exact (continuous_toUX X e hJ).comp (hc.comp continuous_toAdd)
  · exact toUX_mem_UAt X e Z hJ (GlobalTheory.PointAtPlaceHom.atTau_mem X τ _)

end GlobalTheory.TransportedLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOneParamLineTransposeGramUnitarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_one_param_line_transposeGramUnitary : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau),
    ∀ Y ∈ lieAt X τ, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Z,
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t) := by
  first | exact @GlobalTheory.TransportedLine.exists_line_toUX_oneP | exact GlobalTheory.TransportedLine.exists_line_toUX_oneP | (intros; apply GlobalTheory.TransportedLine.exists_line_toUX_oneP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
noncomputable section

namespace GlobalTheory.PolKer

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ T : Finset (Pl F), X.T ⊆ T ∧ ∃ (m : ℕ) (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) = 0

theorem sum_pure_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h : ∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) :
    ∑ i, pure (f i) (φ i) ∈ GlobalTheory.SquareAgree.algD M ψ emb := by
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, φ i, (h i).1, (h i).2.1, ?_, rfl⟩
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact (h i).2.2 v hv

theorem algD_of_polZero (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (h : PolZero B G X R Rf Φ) : Φ ∈ GlobalTheory.SquareAgree.algD G.M B.ψ B.emb := by
  obtain ⟨T, -, m, f, φ, hf, rfl, -⟩ := h
  exact sum_pure_mem_algD G.M B.ψ B.emb T f φ hf

end GlobalTheory.PolKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

variable {D : D7}

def embAt (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) (k : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  cmp θ τ (stabilizerEmbedding d (atTau θ Y τ k))

def mco {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (v₀ : M.H τ) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ℂ :=
  ⟪M.rep τ g₀ v₀, M.rep τ g (M.rep τ g₀ v₀)⟫_ℂ

def ptY {Y : HSp D} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (τ : D.what₂.Tau) (u : Formalism.REAL.UJ (M₀.ε τ)) :
    Matrix (Fin Y.rank) (Fin Y.rank) ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M₀ τ (Formalism.MainNotions.S.umat u)

structure LocOK (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S')
    (M : DSModel V S) (τ : D.what₂.Tau) (q : ℝ) (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ)
    (εB : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : M₀.H τ) (c : ℂ) : Prop where

  unitA : IsUnit A

  gramA : Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ

  unitB : IsUnit B

  gramB : Bᴴ * Formalism.REAL.Jm εB * B = gramAt D V τ

  adapted : ∀ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2

  real : g₀ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)

  kfin : v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ

  dec : DecayAt M τ v₀ v₀ (2 * V.rank ^ 2 + 1)

  sm : w ∈ M₀.sm τ

  ne : w ≠ 0

  cne : c ≠ 0

  act : ∀ b : M₀.H τ, ∫ u, mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u)) * ⟪b, M₀.rep τ (ptY M₀ τ u) w⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    c * ⟪b, w⟫_ℂ

  far : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))) (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖c‖

  lip : ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤ Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹)

end GlobalTheory.PackLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInvInert

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem idem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  have hβα : ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → β * α = α := by
    intro α hα
    apply RestrictedProduct.ext
    intro w
    show β w * α w = α w
    by_cases hw : w = v
    · subst hw
      have : β w = 1 := h1
      rw [this, one_mul]
    · have : α w = 0 := hα w hw
      rw [this, mul_zero]
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
      obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hw
      funext i j
      show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * _ = _
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      show ((0 * 0, β * α) : AF D.host.F) = (0, α)
      rw [mul_zero, hβα α hα]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

theorem mem_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u := by
  constructor
  · intro hu
    exact ⟨GlobalTheory.PlaceModel.latO_le_top _ hu, idem_smul_eq hε hu⟩
  · rintro ⟨hu, he⟩
    have := GlobalTheory.PlaceModel.placeIdem_smul_mem hε hu
    rwa [he] at this

theorem act_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) := by
  intro x y hxy
  unfold actO at hxy
  have hT : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have hS : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  calc x = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * x * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * x * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * y * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        rw [hxy]
    _ = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * y * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        simp only [Matrix.mul_assoc]
    _ = y := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]

theorem om_fixes_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ g h, SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT hη v ε hns hχS hχT g h hg hh hlat f hf hvac
  have hε : IsPlaceIdem D v ε := hns.1
  have key := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om hη hW v ε hns hχS hχT
  have hc : ∀ (c : AE D) (x : WO S T), actO S T g h (c • x) = c • actO S T g h x := by
    intro c x
    unfold actO
    rw [Matrix.mul_smul, Matrix.smul_mul]
  refine key g h hg hh ?_ f hf ?_
  · intro u
    rw [mem_place_iff hε, mem_place_iff hε]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hlat u).1 h1, by rw [← hc, h2]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(hlat u).2 h1, ?_⟩
      apply act_injective g h
      rw [hc]
      exact h2
  · intro u hu
    obtain ⟨a, ha, h2a⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
    have hu' := (mem_place_iff hε u).1 hu
    have hau := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu'.1
    have e2 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, h2a]
      exact hu'.2
    have := hvac.1 (a • u) hau
    rwa [e2] at this

end GlobalTheory.VecInvInert

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplitStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_lattice_stabiliser_fixes_vacuum_nonsplit : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ g h, SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = f := by
  first | exact @GlobalTheory.VecInvInert.om_fixes_vacuum | exact GlobalTheory.VecInvInert.om_fixes_vacuum | (intros; apply GlobalTheory.VecInvInert.om_fixes_vacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IwSplitFrame

section Frame

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

end Frame

theorem exists_compl {K : Type} [Field K] [CharZero K] {n r : ℕ} (e e' : Matrix (Fin n) (Fin r) K)
    (p a : Matrix (Fin r) (Fin n) K) (hpe : p * e = 1) (hpe' : p * e' = 0) (hae : a * e = 0) (hae' : a * e' = 1) :
    ∃ (k : ℕ) (i : Matrix (Fin n) (Fin k) K) (q : Matrix (Fin k) (Fin n) K), n = r + k + r ∧
      e * p + i * q + e' * a = 1 := by
  set π : Matrix (Fin n) (Fin n) K := 1 - e * p - e' * a with hπdef
  have hXX : e * p * (e * p) = e * p := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe, Matrix.one_mul]
  have hXY : e * p * (e' * a) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe', Matrix.zero_mul, Matrix.mul_zero]
  have hYX : e' * a * (e * p) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae, Matrix.zero_mul, Matrix.mul_zero]
  have hYY : e' * a * (e' * a) = e' * a := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae', Matrix.one_mul]
  have hπ : π * π = π := by
    simp only [hπdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hXX, hXY, hYX, hYY]
    abel
  have hid : IsIdempotentElem (Matrix.toLin' π) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hπ]
  set W := LinearMap.range (Matrix.toLin' π)
  set b := Module.finBasis K W
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict), ?_, ?_⟩
  · have h1 := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
    rw [Matrix.trace_toLin'_eq, hπdef, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm e,
      Matrix.trace_mul_comm e', hpe, hae', Matrix.trace_one, Matrix.trace_one] at h1
    simp only [Fintype.card_fin] at h1
    have h2 : ((r + Module.finrank K W + r : ℕ) : K) = n := by push_cast; rw [← h1]; ring
    exact (Nat.cast_injective h2).symm
  · rw [← LinearMap.toMatrix'_comp]
    have h3 : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict) =
        Matrix.toLin' π := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply,
        LinearMap.rangeRestrict, LinearMap.codRestrict_apply]
    rw [h3, LinearMap.toMatrix'_toLin', hπdef]
    abel

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mat_mul (g h : GLoc σ J v) : (HA.mat (F := F) (Fv F v) σ J (g * h)).1 =
    (HA.mat (F := F) (Fv F v) σ J g).1 * (HA.mat (F := F) (Fv F v) σ J h).1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, map_mul, Units.val_mul]

theorem mat_one : (HA.mat (F := F) (Fv F v) σ J 1).1 = 1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, map_one, Units.val_one]

def keepGrp (j : Matrix (Fin n) (Fin r) (Fv F v ⊗[F] E)) : Subgroup (GLoc σ J v) where
  carrier := {q | ∃ β : GL (Fin r) (Fv F v ⊗[F] E), (HA.mat (F := F) (Fv F v) σ J q).1 * j = j * β.1}
  mul_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    refine ⟨β * β', ?_⟩
    rw [mat_mul, Matrix.mul_assoc, hβ', ← Matrix.mul_assoc, hβ, Units.val_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, by rw [mat_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  inv_mem' := by
    rintro a ⟨β, hβ⟩
    refine ⟨β⁻¹, ?_⟩
    have h1 : (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J a).1 = 1 := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    calc (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * j
        = (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (j * β.1) * (β⁻¹).1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc j, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = j * (β⁻¹).1 := by rw [← hβ, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem keeps_of_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) {a a' : Matrix (Fin r) (Fin r) (Fv F v)}
    (h1 : (splitHom σ J τ g).1 * e.map τ = e.map τ * a)
    (h2 : (splitHom σ J (τ.comp σ) g).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a') :
    g ∈ keepGrp (σ := σ) (J := J) (v := v) (e.map (inclR (F := F) (Fv F v))) := by
  set j := e.map (inclR (F := F) (Fv F v))
  set P := p.map (inclR (F := F) (Fv F v))
  have hP : P * j = 1 := by
    rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ (t : E →ₐ[F] Fv F v) {b : Matrix (Fin r) (Fin r) (Fv F v)},
      (splitHom σ J t g).1 * e.map t = e.map t * b →
      (HA.mat (F := F) (Fv F v) σ J g).1.map ((splitProj t).toRingHom) * j.map ((splitProj t).toRingHom) =
        j.map ((splitProj t).toRingHom) * b := fun t b hb => by
    have e2 : j.map ((splitProj t).toRingHom) = e.map t := by
      ext k l
      simp [j, splitProj_inclR]
    rw [e2]
    exact hb
  have hk : (HA.mat (F := F) (Fv F v) σ J g).1 * j = j * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) := by
    ext k l
    exact split_ext h τ (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key τ h1)) k) l)
      (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key _ h2)) k) l)
  have hk' : (HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J g).1 = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
  have h3 : (P * ((HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * j)) * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, ← hk,
      ← Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, hk', Matrix.one_mul, hP]
  exact ⟨⟨_, _, mul_eq_one_comm.1 h3, h3⟩, hk⟩

end Local

end GlobalTheory.IwSplitFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows.RowRapidPf

theorem multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) :
    MultT θ M J χ ≤ MultT θ M ∅ 1 :=
  Submodule.map_mono (Submodule.span_mono fun _ h =>
    ⟨h.aut, h.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), h.equiv, h.cont⟩)

end GlobalTheory.SepRows.RowRapidPf

end
end
