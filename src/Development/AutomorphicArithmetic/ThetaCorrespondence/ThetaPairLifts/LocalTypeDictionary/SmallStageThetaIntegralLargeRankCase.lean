module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteChainFrameBottom
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageNonzeroAtFinitePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralsAgreeOfIntegrableKernel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockModelAdmissiblePolynomialExists
section
noncomputable section
namespace GlobalTheory.GoodFock
section Ring
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli Finset
variable {U : Type} [Ring U] [Algebra ℂ U] {n b : ℕ}
end Ring
section Poly
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
end Poly
section Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.ChainFr GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.MixModel Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
end Theta
section Quot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Matrix GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.RealQuot Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {M X : HSp D}
end Quot
section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links _root_.Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open _root_.Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem exists_admissible_fock_polynomial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  intro hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, q, q', -, hq', hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, q' P₀ = 0 → ∀ P, q' P = 0 := by
    by_cases h : ∃ P₀, q' P₀ ≠ 0
    · exact h.imp fun _ h h' => absurd h' h
    · push_neg at h
      exact ⟨0, fun _ => h⟩
  refine ⟨capelliC (quad (raiO τ (sgA A₁ τ) (B.ε τ)) (lowO τ (sgA A₁ τ) (B.ε τ)))
    ((W₁.rank : ℂ) - 1) P₀, fun α β htr hexp ωA ωB Pi rf rl p p' hm f hf => ⟨fun ν₁ 𝓕₁ hν => ?_, fun h0 P'' => ?_⟩⟩
  · obtain ⟨p₀, q₀, hsig, -, hlt⟩ := htr.sig
    have hW : IsWeilDatumO ψ (GlobalTheory.Grid.sgn false W₁) X α (α / β) (ωB.toSgn false) := hm.weilB
    have hk := killed_capelli hψ hθ (frSgn false A₁) B hf τ P₀
    refine GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain hP.siegelSetUnitary D ψ θ hθ false W₁ X _ _ ωB hm.weilB q₀ ⟨τ, (hsig τ).2.1⟩ (by omega) ν₁ 𝓕₁ hν _
      (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn false A₁) B hf.1 _) τ fun g h S₀ r d μ' 𝓕' hμ x i hx => ?_
    have := (hk.om hW hθ ((GlobalTheory.Grid.ofSgn false W₁).symm g) h).mixS_eq_zero hψ hθ d hμ x i hx
    exact this
  · have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨-, hco, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ)
      hm.weilB hexpB Pi rf rl p' hm.mapB
    have hc := LinearMap.congr_fun (comp_capelli (p' ∘ₗ fockF ψ θ false A₁ B f) _ _ ((W₁.rank : ℂ) - 1)
      (comp_quad A₁ B (fun τ => a τ - b τ) τ _ (hco f hf))) P₀
    obtain ⟨a', b', ha', hb', hgap⟩ := htr.gap τ
    rw [Formalism.L2.Fam.ThC.expU D α τ _ _ ha' (hexp τ).1, Formalism.L2.Fam.ThC.expU D β τ _ _ hb' (hexp τ).2] at hgap
    have hne : (∏ j : Fin W₁.rank, (-((X.rank : ℂ) / 2 + ((a τ - b τ : ℚ) : ℂ)) + ((W₁.rank : ℂ) - 1 - (j : ℕ)))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j _ h => ?_
      have hj : ((j : ℕ) : ℚ) + 1 ≤ W₁.rank := by exact_mod_cast j.2
      have h' : (-((X.rank : ℚ) / 2 + (a τ - b τ)) + ((W₁.rank : ℚ) - 1 - (j : ℕ))) = 0 := by
        refine Rat.cast_injective (α := ℂ) ?_
        push_cast at h ⊢
        exact h
      linarith
    have h1 : p' (fockF ψ θ false A₁ B f P₀) = 0 := (smul_eq_zero.1 (hc.symm.trans h0)).resolve_left hne
    obtain ⟨Pf, r, r', e, -, -, -, he⟩ := (hLM α β htr hexp).2 ωA ωB Pi rf rl p p' hm
    rw [he f hf] at h1 ⊢
    by_cases hz : q' P₀ = 0
    · rw [hP₀ hz, TensorProduct.zero_tmul, map_zero]
    · have h2 : q' P₀ ⊗ₜ[ℂ] r' f = 0 := e.injective (h1.trans (map_zero e).symm)
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hz
      have h3 := congrArg (fun x => TensorProduct.lid ℂ Pf (LinearMap.rTensor Pf l x)) h2
      have h4 : r' f = 0 := by simpa [hl] using h3
      rw [h4, TensorProduct.tmul_zero, map_zero]
end Main
end GlobalTheory.GoodFock
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  first | exact @_root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | exact _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | (intros; apply _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtLargeParameterThetaIntegral
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralLineHasDerivAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace GlobalTheory.ThetaIntegralLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
theorem thetaIntegral_line_hasDerivAt (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (χY χW : Chr F E) (om : Rep σ Y W)
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hw : M.IsWeil ψ χY χW om) (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ)
    (hcont : ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h)
    {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ Φ₁ ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) ∧
      ∀ h, HasDerivAt (fun t : ℝ => M.I om Φ (h * γ (Multiplicative.ofAdd t))) (M.I om Φ₁ h) 0 := by
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw).pres
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, fun h => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · have e : ∀ h', M.I om 0 h' = 0 := fun h' => by simpa using I_smul M om 0 0 h'
      simpa [e] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add Φ Ψ hΦ hΨ ihΦ ihΨ =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ihΦ
    obtain ⟨Ψ₁, m₂, p₂, q₂⟩ := ihΨ
    refine ⟨Φ₁ + Ψ₁, Submodule.add_mem _ m₁ m₂, fun x => ?_, fun h => ?_⟩
    · simpa only [map_add (f := _), Pi.add_apply] using (p₁ x).fun_add (p₂ x)
    · simpa only [I_add M om hpres hconv hΦ hΨ, I_add M om hpres hconv m₁ m₂] using (q₁ h).fun_add (q₂ h)
  | smul c Φ hΦ ih =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ih
    refine ⟨c • Φ₁, Submodule.smul_mem _ c m₁, fun x => ?_, fun h => ?_⟩
    · simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (p₁ x).const_mul c
    · simpa only [I_smul] using (q₁ h).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hφ, rfl⟩ := hΦ
    obtain ⟨c, c', h0, hlim, hacts⟩ := _root_.GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit hP M ψ χY χW om hcm hψ hw γ hγ f
    have hmem : ∀ u : SInf F (Fin n × Fin d), pureA F u φ ∈ schA F (Fin n × Fin d) :=
      fun u => Submodule.subset_span ⟨u, φ, hφ, rfl⟩
    have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => φ fun i => (x i).2) := by
      refine ⟨fun x z hz => congrArg φ (funext fun i => ?_), hmem f⟩
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at z hz i, add_zero]
    have hc : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (pureA F f φ) = pureA F (c t) φ := fun t => hacts t _ hR
    refine ⟨pureA F c' φ, hmem c', fun x => ?_, fun h => ?_⟩
    · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
        (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
      have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * φ fun i => (x i).2)
          (c' (fun j => evI F (x j)) * φ fun i => (x i).2) 0 := by
        rw [hasDerivAt_iff_tendsto_slope]
        refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
        rw [slope_def_module, h0]
        simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
        ring
      simp only [hc]
      exact h2
    · let L : SInf F (Fin n × Fin d) →ₗ[ℝ] ℂ :=
        { toFun := fun u => M.I om (pureA F u φ) h
          map_add' := fun u u' => by
            have e : pureA F ⇑(u + u') φ = pureA F u φ + pureA F u' φ := by
              funext x; simp [pureA, add_mul]
            rw [e, I_add M om hpres hconv (hmem u) (hmem u')]
          map_smul' := fun s u => by
            have e : pureA F ⇑(s • u) φ = (s : ℂ) • pureA F u φ := by
              funext x; simp [pureA, mul_assoc, Complex.real_smul]
            rw [e, I_smul, RingHom.id_apply, Complex.real_smul] }
      have hL : Continuous L := hcont φ hφ h
      have hcurve : (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) = fun t => L (c t) := by
        funext t
        rw [← I_om_one, hc]
        rfl
      rw [hcurve, hasDerivAt_iff_tendsto_slope]
      refine ((hL.tendsto c').comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, slope_def_module, h0, sub_zero, map_smul, map_sub]
end GlobalTheory.ThetaIntegralLine
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
noncomputable section
namespace GlobalTheory.ConvThetaNe
open GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section Over
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
theorem hasDerivAt_large_parameter_theta_integral (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam θ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om')
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {τ : D.what₂.Tau} {Y : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hY : Y ∈ lieAt X τ) {Φ Φ' : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (hΦ' : Φ' ∈ algF ψ θ true A B)
    (hd : IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ') (h : GA D X) :
    HasDerivAt (fun t : ℝ => thetaInt ωA ν 𝓕 Φ (h * oneP θ X τ Y t)) (thetaInt ωA ν 𝓕 Φ' h) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.OscLie.exists_lie_deriv_pol Bs Γ Xc om om' hT γ hγ
  obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
  obtain ⟨Φ'D, -, hD'⟩ := hO.algA Φ' hΦ'
  have hPD : ΦD ∈ GlobalTheory.ThK.PolData Bs Γ.M := by
    refine Submodule.span_mono ?_ hΦD
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, h1, φ, h2, h3, rfl⟩
  obtain ⟨T, m, f, φ, hf, rfl⟩ := GlobalTheory.ThK.CycGen.exists_decOn_some Γ.M ΦD hPD
  have e1 := _root_.GlobalTheory.SquareAgree.DatA.polarization_datum_lie_derivative hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ
    hγt hγ Φ Φ' hd T m f (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) hD Φ'D hD'
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil hC
  obtain ⟨Φ₁, -, hp, hI⟩ := _root_.GlobalTheory.ThetaIntegralLine.thetaIntegral_line_hasDerivAt hP Γ.M Bs.ψ _ _ om hT.base.cm hT.base.std hT.weil hC
    (fun g hg x => by
      obtain ⟨L, hL⟩ := hT.weil.isUSplitting.adm (1, x) l hla g hg
      refine L.continuous.congr fun u => ?_
      rw [GlobalTheory.BigNZ.I_eq_l hT hl (Submodule.subset_span ⟨u, g, hg, rfl⟩), ← hL u]
      rfl) hγ hD.1
  have hM := hT.geo.hM
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]
      exact (GlobalTheory.BigNZ.IsFinPart.fam (M := Γ.M) (T := T) (hf i).2).mem hM _⟩
  have e2 : Φ₁ = Φ'D := by
    funext x
    refine (hp x).unique ?_
    rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact HasDerivAt.fun_sum fun i _ => (hδ _ (hf i).1).2 _ (hrest i) x
  have := hI (kapX X e hO.JX h)
  rw [e2] at this
  simp only [int_eq hO hD, int_eq hO hD', GlobalTheory.KapXLine.kapX_mul, ← hγt]
  exact this
end Over
theorem convergent_theta_integral_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ algF ψ θ false A₁ B, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' ≠ 0 := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm Φ' hΦ' hint' hp' h0'
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hm.weilA hm.weilB
  have hC := (hK.1 _ _ _ Bs _ _ Γ Xc om om' hTD).1.1
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  set S := algF ψ θ true A B with hS
  have hint : ∀ Φ ∈ S, ∀ h, IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := fun Φ hΦ h => integrable_big hO hC hΦ h
  have tr : ∀ (Φ : WO W X → ℂ) (h k : GA D X), thetaInt ωA ν 𝓕 (ωA (1, k) Φ) h = thetaInt ωA ν 𝓕 Φ (h * k) := by
    intro Φ h k
    simp only [thetaInt, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have tadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, thetaInt ωA ν 𝓕 (Φ + Ψ) = thetaInt ωA ν 𝓕 Φ + thetaInt ωA ν 𝓕 Ψ := by
    intro Φ hΦ Ψ hΨ; funext h
    have e : (fun g => thetaKO ωA g h (Φ + Ψ)) = fun g => thetaKO ωA g h Φ + thetaKO ωA g h Ψ := by
      funext g; simp [thetaKO, map_add (f := _)]
    simp only [thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hint Φ hΦ h) (hint Ψ hΨ h)
  have tsmul : ∀ (s : ℂ) Φ, thetaInt ωA ν 𝓕 (s • Φ) = s • thetaInt ωA ν 𝓕 Φ := by
    intro s Φ; funext h
    have e : (fun g => thetaKO ωA g h (s • Φ)) = fun g => s * thetaKO ωA g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul s _
  let K : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {Φ | Φ ∈ S ∧ thetaInt ωA ν 𝓕 Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by rw [tadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨S.zero_mem, by funext h; simp [thetaInt, thetaKO]⟩
      smul_mem' := fun s a ha => ⟨S.smul_mem s ha.1, by rw [tsmul, ha.2, smul_zero]⟩ }
  have kill : ∀ Ψ ∈ S, p Ψ = 0 → thetaInt ωA ν 𝓕 Ψ = 0 := fun Ψ hΨ h0 => by
    rw [hc Ψ hΨ 0 (zero_mem _) (fun h => by simp [thetaKO]) (by rw [h0, map_zero])]
    funext h; simp [thetaInt, thetaKO]
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p, rf g x ∈ K.map p := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    refine ⟨ωA (1, g) Ψ, ⟨hm.mapA.stabX.1 g hg Ψ hΨS, ?_⟩, hm.mapA.eqf g hg Ψ hΨS⟩
    funext h
    rw [tr, hΨ0]
    rfl
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p, rl τ Y x ∈ K.map p := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    obtain ⟨Ψ', hΨ'S, hder⟩ := hm.mapA.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Ψ', ⟨hΨ'S, funext fun h => ?_⟩, hm.mapA.eql τ Y hY Ψ hΨS Ψ' hΨ'S hder⟩
    have h1 := _root_.GlobalTheory.ConvThetaNe.hasDerivAt_large_parameter_theta_integral hP hθ hO hTD hC hY hΨS hΨ'S hder h
    rw [hΨ0] at h1
    exact h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  rcases hm.irred.2 (K.map p) stf stl with hbot | htop
  · obtain ⟨Φ, hΦ, hpΦ⟩ : p' Φ' ∈ S.map p := hm.mapA.onto ▸ Submodule.mem_top
    have h1 : p Φ ∈ K.map p := ⟨Φ, ⟨hΦ, by rw [hc Φ hΦ Φ' hΦ' hint' hpΦ, h0', smul_zero]⟩, rfl⟩
    rw [hbot, Submodule.mem_bot, hpΦ] at h1
    exact hp' h1
  · obtain ⟨Φ, hΦ, hne⟩ := exists_big_ne hK hL hO hTD
    obtain ⟨Ψ, ⟨hΨS, hΨ0⟩, hΨp⟩ : p Φ ∈ K.map p := by rw [htop]; exact Submodule.mem_top
    have h1 := tadd _ (S.sub_mem hΦ hΨS) Ψ hΨS
    rw [sub_add_cancel, kill _ (S.sub_mem hΦ hΨS) (by rw [map_sub, hΨp, sub_self]), hΨ0, add_zero] at h1
    exact hne h1
end GlobalTheory.ConvThetaNe
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageSmallBig
theorem smallStage_thetaIntegral_of_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (_root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q0 A A' WW X hX _ => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, -, -, hD⟩ := hd W i j p q0 A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  obtain ⟨P0, hP0⟩ := _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW ea eb
  have key : ∀ t, (∀ h, IntegrableOn (X.ker' W.ψ W.θ t P0 h) X.fd' X.m') ∧ X.I' W.ψ W.θ t P0 ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, hk'⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p q0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    haveI : Nontrivial Pr := nontrivial_left e
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P1, rfl⟩ := hq' x
    obtain ⟨hint, hker⟩ := hP0 _ _ hTr hInf _ _ _ _ _ _ _ hm _ hf'
    have hint' := hint X.m' X.fd' hIs.meas'
    have hne : pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) ≠ 0 := fun h0 => by
      have h1 := hker h0 P1
      rw [hr' _ hf'] at h1
      exact e.map_ne_zero_iff.2 (tmul_ne_zero hx hy) h1
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    refine ⟨fun h => ?_, ?_⟩
    · have h1 := hint' h
      simp only [hk'] at h1
      exact h1
    · rw [← eI']
      exact _root_.GlobalTheory.ConvThetaNe.convergent_theta_integral_ne_zero hP hK hL D W.ψ W.θ hW W.θ_is A A' WW FA FA' FW _ _ hTr X.m' X.fd' hIs.meas'
        _ _ _ _ _ _ _ hm _ (Submodule.subset_span ⟨_, P0, hf', rfl⟩) hint' hne
  exact ⟨P0, fun t => (key t).1, fun t => (key t).2⟩
end GlobalTheory.StageSmallBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallStage_thetaIntegral_large_rank_case : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      1 ≤ q → ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | exact _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank | (intros; apply _root_.GlobalTheory.StageSmallBig.smallStage_thetaIntegral_of_large_rank <;> assumption)
end
