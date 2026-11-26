module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitLocallyConstant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralSuccPositionEqExchange
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralSuccPositionEqExchange
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL step_two)

noncomputable section
namespace GlobalTheory.PosOne.RrStep

theorem rr_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (_ : ∀ Ψ v, B₁ Ψ v = exUp ν p σ (B Ψ) v) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG (p + 1) (tInt ψ ν μ (p + 1) σ B₁ F Φ.1) (exUp ν p ρ' Rr Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hc ψ hψ hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ B B₁ hB hB₁ F ρ' hρ' Rr hRr Φ
  have := hν.1
  have := secondCountable k
  have := t2Space k
  let ω : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :=
    (omR μ).comp (MonoidHom.inl _ _)
  obtain rfl : ρ' = ω :=
    MonoidHom.ext fun g => LinearMap.ext fun Φ => Subtype.ext (hρ' g Φ)
  have hω : IsSmoothRep ω := fun Φ =>
    (omR_smooth hμ Φ).preimage (continuous_id.prodMk continuous_const)

  let π' : Representation ℂ (GL n' k) (GL n' k →₀ ℂ) :=
    { toFun := fun g => Finsupp.lmapDomain ℂ ℂ (g * ·)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  let π : Representation ℂ (GL n k) (SB (Matrix n n' k)) := (omR μ).comp (MonoidHom.inr _ _)
  let θ : (GL n' k →₀ ℂ) →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n n' k) :=
    Finsupp.lsum ℂ fun g₀ => LinearMap.toSpanSingleton ℂ _ (omR μ (g₀⁻¹, 1))
  have hθ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ) := by
    intro g h φ Ψ Ψ' e
    obtain rfl : Ψ' = omR μ (g, h) Ψ := Subtype.ext e
    induction φ using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), LinearMap.add_apply, h₁, h₂]
    | single g₀ a =>
      simp only [π', MonoidHom.coe_mk, OneHom.coe_mk, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, θ, Finsupp.lsum_single,
        LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, map_smul, π, MonoidHom.coe_comp,
        Function.comp_apply, MonoidHom.inr_apply, omR_mul, smul_eq_mul]
      rw [show ((g * g₀)⁻¹ * g, 1 * h) = (1 * g₀⁻¹, h * 1) from Prod.ext (by group) (by group)]
  have hθ1 : ∀ Ψ, θ (Finsupp.single 1 1) Ψ = Ψ := fun Ψ => by
    simp only [θ, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul, inv_one]
    exact Subtype.ext (om_one μ Ψ.1)
  have hb : IsPos ψ p π σ B := ⟨hB.1, fun g φ v => hB.2 g φ (π g φ) v rfl⟩
  have happ : ∀ (q : ℕ) (B₀ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ)
      (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      tInt ψ ν μ q σ B₀ F Φ.1 = fun h => B₀ (opL hψ ν q (omR μ (1, h) Φ)) (σ h F) := by
    intro q B₀ Φ
    funext h
    exact GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe B₀ (opL hψ ν q (omR μ (1, h) Φ)) ▸ rfl
  have uniq := fun q h1 h2 f => (GlobalTheory.QuotInt.quotInt_unique_exists k n c q h1 h2 ν μX μG f).1
  have hRr' : ∀ Φ, IsQuotInt ν μX μG p (fun h => B (opL hψ ν p (omR μ (1, h) Φ)) (σ h F)) (Rr Φ) :=
    fun Φ => happ p B Φ ▸ hRr Φ

  have hL : IsNEquiv ψ p ω Rr := fun g hg Φ => by
    rw [← smul_eq_mul, ← map_smul]
    refine uniq p hp hc.le _ _ _ (hRr' _) ?_
    have e : ∀ h, opL hψ ν p (omR μ (1, h) (ω g Φ)) =
        opL hψ ν p (omR μ (1, h) ((ψ (simpleSum g) : ℂ) • Φ)) := fun h => by
      have := GlobalTheory.RootExSource.opE_om_source k n n' c p hp hc.le ψ ν μ (omR μ (1, h) Φ).1 g hg
      rw [← omR_val, omR_mul, mul_one, one_mul] at this
      show opL hψ ν p (omR μ (1, h) (omR μ (g, 1) Φ)) = _
      rw [omR_mul, mul_one, one_mul, map_smul, map_smul]
      exact Subtype.ext this
    exact (funext fun h => congrArg (fun Ψ => B Ψ (σ h F)) (e h)) ▸ hRr' _

  obtain ⟨C, hC, H⟩ := step_two hψ ν (Finsupp.single 1 1) F hp hc hψ1 hμ hσ μX μG hθ hb hB₁ Φ
  have s1 := ((ExchangeSupport.exchange_support k n' (c + 1) p hp (by omega) ψ hψ hψ1 ν _ ω hω Rr Φ).1 hL).1
  obtain ⟨χ, hχ, h1⟩ := _root_.GlobalTheory.RootEx.exists_mem_SB_eq_one_on_compact k n' _ (hC.union s1.2)
  have hT : IsLocallyConstant fun u : n' → k => χ u • ω (rowE (c + 1) p u) Φ :=
    (hχ.1.prodMk ((orbit_locallyConstant hω Φ).comp_continuous ExchangeSupport.continuous_rowE)).comp
      fun q => q.1 • q.2
  obtain ⟨Φ', hΦ'⟩ := _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
    (Measure.pi fun _ => ν) _ _ hT _ hχ.2
    fun u hu => by simp only [image_eq_zero_of_notMem_tsupport hu, zero_smul]
  simp only [map_smul, smul_eq_mul] at hΦ'
  obtain ⟨z, hz1, hz2⟩ := H χ hχ.1 (fun u hu => h1 u (Or.inl hu)) Φ' hΦ'
  have e : exUp ν p ω Rr Φ = Rr Φ' := by
    rw [hΦ', exUp]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ tsupport fun u : n' → k => Rr (ω (rowE (c + 1) p u) Φ)
    · simp only [h1 u (Or.inr hu), one_mul]
    · have := image_eq_zero_of_notMem_tsupport hu
      simp only [this, mul_zero]
  simp only [hθ1] at hz1 hz2
  rw [happ, e, ← uniq p hp hc.le _ _ _ hz1 (hRr' Φ')]
  exact hz2

end GlobalTheory.PosOne.RrStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralSuccPositionEqExchangeStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantIntegral_succ_position_eq_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (_ : ∀ Ψ v, B₁ Ψ v = exUp ν p σ (B Ψ) v) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG (p + 1) (tInt ψ ν μ (p + 1) σ B₁ F Φ.1) (exUp ν p ρ' Rr Φ) := by
  first | exact @GlobalTheory.PosOne.RrStep.rr_step | exact GlobalTheory.PosOne.RrStep.rr_step | (intros; apply GlobalTheory.PosOne.RrStep.rr_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotientInvariantIntegralExchangeToPositionOne
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOneIntegral

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def omRight (μ : kˣ →* ℂˣ) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ (1 : GL n' k) g Ψ.1, om_mem_SB μ 1 g Ψ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun z Φ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    exact om_one μ Ψ.1
  map_mul' g h := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    show om μ (1 : GL n' k) (g * h) Ψ.1 = om μ 1 g (om μ 1 h Ψ.1)
    rw [← om_mul μ 1 1 g h Ψ.1, mul_one]

variable {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]

theorem bilPos_iff_isPos (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (p : ℕ)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    BilPos ψ μ p σ B ↔ IsPos ψ p (omRight μ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRight μ g Ψ := Subtype.ext hΨ
    rw [this]
    exact h2 g Ψ v

end GlobalTheory.PosOneIntegral
end

open GlobalTheory.PosOneIntegral in
theorem GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) (hν : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (hρ' : IsSrc μ ρ') :
    ∀ q : ℕ, q + 1 ≤ c → ∀ (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ (q + 1) σ B →
      ∀ (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ),
      (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG (q + 1) (tInt ψ ν μ (q + 1) σ B F Φ.1) (Rr Φ)) →
      ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        IsQuotInt ν μX μG 1 (tIntOne ψ ν μ (q + 1) σ B F Φ.1) (toOne ν ρ' (q + 1) Rr Φ) := by
  haveI : ν.IsAddHaarMeasure := hν.1
  intro q
  induction q with
  | zero =>
    intro _ B _ Rr hRr Φ
    exact hRr Φ
  | succ q ih =>
    intro hqc B hB Rr hRr Φ
    have hq1 : 1 ≤ q + 1 := Nat.succ_le_succ (Nat.zero_le q)
    have hqlt : q + 1 < c := by omega

    obtain ⟨B₀, hB₀e, hB₀⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν A σ hσ).2.2
      (SB (Matrix n n' k)) (omRight μ) B).2 ((bilPos_iff_isPos ψ μ _ σ B).1 hB)
    have hB₀' : BilPos ψ μ (q + 1) σ B₀ := (bilPos_iff_isPos ψ μ _ σ B₀).2 hB₀
    have hB₀f : ∀ Ψ, (⇑(B₀ Ψ) : A → ℂ) = exDown ν (q + 1) σ (⇑(B Ψ)) := fun Ψ => funext (hB₀e Ψ)

    have hsm' : IsSmoothRep ρ' := (GlobalTheory.T.exists_weilSourceAction_and_smooth k (n' ⊕ Fin (c + 1)) (n ⊕ Fin c) μ hμ).2 ρ' hρ'
    obtain ⟨Rr₀, hRr₀, hRr₀N⟩ := GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n n' c (q + 1) hq1 hqlt.le ψ hψc hψ1 ν μ hμ μX μG A σ hσ B₀ hB₀' F ρ' hρ'
    have hIH := ih hqlt.le B₀ hB₀' Rr₀ hRr₀ Φ

    have hBup : ∀ Ψ v, B Ψ v = exUp ν (q + 1) σ (B₀ Ψ) v := by
      intro Ψ v
      rw [hB₀f Ψ]
      exact ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν A σ hσ (B Ψ) v).2
        (hB.1 Ψ)).symm

    have hRrup : ∀ Φ', Rr Φ' = exUp ν (q + 1) ρ' Rr₀ Φ' := by
      intro Φ'
      have hst := GlobalTheory.T.invariantIntegral_succ_position_eq_exchange k n n' c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ B₀ B hB₀' hBup F ρ' hρ' Rr₀ hRr₀ Φ'
      exact (GlobalTheory.QuotInt.quotInt_unique_exists k n c (q + 1 + 1) (by omega) hqc ν μX μG _).1 _ _ (hRr Φ') hst
    have hdown : exDown ν (q + 1) ρ' (⇑Rr) = ⇑Rr₀ := by
      funext v
      have hRrf : (⇑Rr : _ → ℂ) = exUp ν (q + 1) ρ' ⇑Rr₀ := funext hRrup
      rw [hRrf]
      exact (GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n' (c + 1) (q + 1) hq1 (by omega) ψ hψc hψ1 ν hν _ ρ' hsm' Rr₀ v).1 hRr₀N
    have hval : toOne ν ρ' (q + 1 + 1) Rr Φ = toOne ν ρ' (q + 1) Rr₀ Φ := by
      rw [toOne_succ, hdown]
    have hfun : tIntOne ψ ν μ (q + 1 + 1) σ B F Φ.1 = tIntOne ψ ν μ (q + 1) σ B₀ F Φ.1 := by
      funext h
      simp only [tIntOne]
      rw [toOne_succ]
      congr 1
      funext v
      by_cases hm : opE ψ ν 1 (om μ 1 h Φ.1) ∈ SB (Matrix n n' k)
      · simp only [app, hm, dite_true]
        exact congrFun (hB₀f _).symm v
      · simp [app, hm, exDown]
    rw [hfun, hval]
    exact hIH

theorem GlobalTheory.PosOneIntegral.isQuotInt_toOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (toOne ν ρ' P Rr Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP1 hPc ψ hψc hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ' Rr hRr Φ
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  exact GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step k n n' c ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ F ρ' hρ' q hPc B hB Rr hRr Φ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotientInvariantIntegralExchangeToPositionOneStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuotientInvariantIntegral_exchange_toPositionOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (toOne ν ρ' P Rr Φ) := by
  first | exact @GlobalTheory.PosOneIntegral.isQuotInt_toOne | exact GlobalTheory.PosOneIntegral.isQuotInt_toOne | (intros; apply GlobalTheory.PosOneIntegral.isQuotInt_toOne <;> assumption)
end
