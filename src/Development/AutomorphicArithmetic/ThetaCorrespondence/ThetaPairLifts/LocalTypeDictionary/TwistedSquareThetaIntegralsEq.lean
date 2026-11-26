module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilFactorization
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelMatchOnOppositeParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfKer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.SquareAgree
open Topology in
private theorem conjU_measurableEmbedding' {D : D7} (S : HSp D) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (c : D.host.E) (hJ : J = c • S.gram) : MeasurableEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) := by
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  let κ : GL (Fin S.rank) (AE D) → GL (Fin S.rank) (AE D) := fun g => GeneralLinearGroup.map (cA D) g
  have hκc : Continuous κ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
    · exact Units.continuous_coe_inv.matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  have hκκ : Function.LeftInverse κ κ := fun g => by
    ext i j
    exact Formalism.L2.Theta.cA_cA _
  have hκe : IsEmbedding κ := hκκ.isEmbedding hκc hκc
  have hmat : IsEmbedding (matHom S) := IsEmbedding.subtypeVal
  have hcomp : (Subtype.val : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J → GL (Fin S.rank) (AE D)) ∘ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ =
      κ ∘ matHom S := rfl
  have hemb : IsEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) := by
    refine ⟨IsInducing.of_comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU S c hJ) continuous_subtype_val ?_, ?_⟩
    · rw [hcomp]; exact (hκe.comp hmat).isInducing
    · intro a b hab
      apply (hκe.comp hmat).injective
      rw [← hcomp]
      exact congrArg Subtype.val hab
  refine hemb.measurableEmbedding ?_
  have hrange : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) =
      (κ ∘ Subtype.val) ⁻¹' (HR (AF D.host.F) D.sp.cm.sig S.gram : Set (GL (Fin S.rank) (AE D))) := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      show κ (κ (matHom S g)) ∈ (HR (AF D.host.F) D.sp.cm.sig S.gram : Set (GL (Fin S.rank) (AE D)))
      rw [hκκ]
      exact g.2
    · intro hy
      refine ⟨(⟨κ y.1, hy⟩ : HR (AF D.host.F) D.sp.cm.sig S.gram), Subtype.ext ?_⟩
      exact hκκ y.1
  rw [hrange]
  exact ((PI.AdicCompletionValuation.isClosed_HR _ _ _).preimage (hκc.comp continuous_subtype_val)).measurableSet

private theorem thetaInt_eq_modelI' : ∀ (D : D7) (S X : HSp D) (d : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Wd) (c : D.host.E)
    (hJ : Y.J = c • S.gram)
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (ω : WRep S X) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Wd)
    (κ : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
    M.μ = ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) → M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕 →
    (∀ g h, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ g) (κ h) = thetaKO ω g h f) →
    ∀ h, thetaInt ω ν 𝓕 f h = M.I om Φ (κ h) := by
  intro D S X d Y Wd M c hJ ν 𝓕 ω om κ Φ f hμ hdom hθ h
  have he := conjU_measurableEmbedding' S c hJ
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I, hμ, hdom, he.restrict_map, Set.preimage_image_eq _ he.injective, he.integral_map]
  simp only [hθ]
  rfl

theorem twisted_theta_integrals_agree : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  intro hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨-, ⟨c, hc, -⟩, hc0⟩, hCo⟩ := hK' R Rf hR
  obtain ⟨s, hs0, hs⟩ := _root_.GlobalTheory.T.twisted_theta_kernels_agree_up_to_scalar hP.howeDualityReal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
    Pi rf rl p p' hM
  refine ⟨c * s, mul_ne_zero (hc0 c hc) hs0, fun Φ' hΦ' => ?_⟩
  obtain ⟨Φ₀, hΦ₀, hrel, Φ₀D, hD₀, hSo⟩ :=
    GlobalTheory.SquareAgree.CoinvPass.coinv_passage D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hTD R Rf hR hCo Φ' hΦ'
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D hSo
  refine ⟨Φ₀, hΦ₀, hrel, GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hTD Φ₀ Φ₀D hD₀
    hconv ?_, fun Φ hΦ hp => ?_⟩
  · obtain ⟨C, k, hC⟩ := hbd 0
    exact ⟨C, k, fun g h => by simpa using hC g h⟩
  · obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
    have hm := hs Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
    funext h
    rw [thetaInt_eq_modelI' D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h,
      _root_.Pi.smul_apply,
      thetaInt_eq_modelI' D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (kapX X e hO.JX) Φ₀D Φ₀ hO.measW₁ hO.domW₁ (hO.theta_eq_B hD₀) h,
      hc ΦD (s • Φ₀D) hm (kapX X e hO.JX h), I_smul, smul_eq_mul, mul_assoc]
end GlobalTheory.SquareAgree
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_square_theta_integrals_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  first | exact @_root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | exact _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree | (intros; apply _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StageUniqueOfArchimedeanTriple
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DerivativeEqZeroIffPolarizationMatch
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree
theorem derivative_eq_zero_iff_polarization_match : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := _root_.GlobalTheory.T.thetaSubspace_eq_ker_projDerivation_of_square hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := _root_.GlobalTheory.T.thetaSubgroup_of_ker_derivation hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, _root_.UpperTheory.Lit.HoweDuality.twisted_theta_jet_condition hR hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (_root_.GlobalTheory.T.thetaKernel_projection_isMax hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0
end GlobalTheory.SquareAgree
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemKerIffPolarizationMatchEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
theorem GlobalTheory.SquareAgree.mem_ker_iff_polarization_match_eq_zero : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hR hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := _root_.GlobalTheory.T.theta_subspace_kernel_maximal hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := _root_.GlobalTheory.T.thetaSubspace_contains_polKernel hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (_root_.UpperTheory.Lit.HoweDuality.twisted_theta_kernel_condition hR hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂
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
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageUniq
open GlobalTheory.SquareComm GlobalTheory.BotUniq
private theorem grid_bigness_mono {P Q : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨CF1, h1⟩ := hP
  refine ⟨CF1, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF hCF
  exact ⟨C1, x1, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (g1 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩
theorem stage_unique_of_archimedean_triple (hH : GlobalTheory.Published.HoweDualityReal) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) {A A' WW : HSp D} (α β : (AE D)ˣ →* Circle)
    (hT : IsTriple A A' WW α β) (m : MeasureTheory.Measure (GA D A)) (fd : Set (GA D A))
    (m' : MeasureTheory.Measure (GA D A')) (fd' : Set (GA D A'))
    (hme : IsHaarFD A m fd) (hme' : IsHaarFD A' m' fd') (ω : GlobalTheory.Grid.WRep A WW) (ω' : GlobalTheory.Grid.WRep A' WW)
    (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Pi₀ : ModuleCat.{0} ℂ) (rf₀ : GA D WW → Module.End ℂ Pi₀)
    (rl₀ : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi₀)
    (p₀ : (WO A WW → ℂ) →ₗ[ℂ] Pi₀) (p₀' : (WO A' WW → ℂ) →ₗ[ℂ] Pi₀)
    (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
    (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi)
    (hm₀ : IsMatch ψ θ FA FA' FW α β ω ω' Pi₀ rf₀ rl₀ p₀ p₀')
    (hm : IsMatch ψ θ FA FA' FW α β ω ω' Pi rf rl p p') :
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ algF ψ θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ algF ψ θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ := GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ A A' WW FA FA' FW _ _ hT m fd m' fd'
    hme hme' ω ω' hm.weilA hm.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs A.rank A'.rank Γ Xc om om' hTD
  have kA : ∀ Φ ∈ algF ψ θ true FA FW, p₀ Φ = 0 ↔ p Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
    rw [_root_.GlobalTheory.SquareAgree.mem_ker_iff_polarization_match_eq_zero hH hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      _root_.GlobalTheory.SquareAgree.mem_ker_iff_polarization_match_eq_zero hH hP D _ _ A A' WW FA FA' FW _ _ _ _
        _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  have kB : ∀ Φ ∈ algF ψ θ false FA' FW, p₀' Φ = 0 ↔ p' Φ = 0 := fun Φ hΦ => by
    obtain ⟨ΦD, hΦD, hD⟩ := hO.algB Φ hΦ
    rw [_root_.GlobalTheory.SquareAgree.derivative_eq_zero_iff_polarization_match hH hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀ Φ hΦ ΦD hΦD hD,
      _root_.GlobalTheory.SquareAgree.derivative_eq_zero_iff_polarization_match hH hP D _ _ A A' WW FA FA' FW _ _
        _ _ _ _ _ _ e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hm Φ hΦ ΦD hΦD hD]
  obtain ⟨EA, hEA⟩ := exists_equiv_of_ker _ p₀ p hm₀.mapA.onto hm.mapA.onto kA
  obtain ⟨EB, hEB⟩ := exists_equiv_of_ker _ p₀' p' hm₀.mapB.onto hm.mapB.onto kB
  have fA : ∀ h ∈ GfC WW, ∀ x, EA (rf₀ h x) = rf h (EA x) := fun h hh =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapA.stabX.1 h hh Φ hΦ, hm₀.mapA.eqf h hh Φ hΦ, hm.mapA.eqf h hh Φ hΦ⟩
  have fB : ∀ h ∈ GfC WW, ∀ x, EB (rf₀ h x) = rf h (EB x) := fun h hh =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ =>
      ⟨_, hm₀.mapB.stabX.1 h hh Φ hΦ, hm₀.mapB.eqf h hh Φ hΦ, hm.mapB.eqf h hh Φ hΦ⟩
  have lA : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EA (rl₀ τ Y x) = rl τ Y (EA x) := fun τ Y hY =>
    intertwine _ p₀ p EA hEA hm₀.mapA.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapA.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  have lB : ∀ τ, ∀ Y ∈ lieAt WW τ, ∀ x, EB (rl₀ τ Y x) = rl τ Y (EB x) := fun τ Y hY =>
    intertwine _ p₀' p' EB hEB hm₀.mapB.onto _ _ fun Φ hΦ => by
      obtain ⟨Φ', hΦ', hd⟩ := hm₀.mapB.stabX.2 τ Y hY Φ hΦ
      exact ⟨Φ', hΦ', hm₀.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd, hm.mapB.eql τ Y hY Φ hΦ Φ' hΦ' hd⟩
  let ι := {g // g ∈ GfC WW} ⊕ {x : D.what₂.Tau × Matrix (Fin WW.rank) (Fin WW.rank) ℂ // x.2 ∈ lieAt WW x.1}
  let ρ : ι → Module.End ℂ Pi₀ := Sum.elim (fun g => rf₀ g.1) (fun x => rl₀ x.1.1 x.1.2)
  have hrank : Module.rank ℂ Pi₀ ≤ Cardinal.aleph0 :=
    _root_.GlobalTheory.SquareAgree.rank_polarization_pi_le_aleph0 hH hP D _ _ A A' WW FA FA' FW _ _ _ _ _ _ _ _ e Bs Γ Xc om om'
      cA cB hθ hT hO hTD R Rf hR Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  have hirr : ∀ N : Submodule ℂ Pi₀, (∀ k, ∀ x ∈ N, ρ k x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    hm₀.irred.2 N (fun g hg x hx => hN (Sum.inl ⟨g, hg⟩) x hx) fun τ Y hY x hx => hN (Sum.inr ⟨(τ, Y), hY⟩) x hx
  have hcomm : ∀ k, ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) * ρ k =
      ρ k * ((EA.trans EB.symm : Pi₀ ≃ₗ[ℂ] Pi₀) : Module.End ℂ Pi₀) := by
    rintro (⟨g, hg⟩ | ⟨⟨τ, Y⟩, hY⟩)
    · exact comm_of_intertwine EA EB _ _ (fA g hg) (fB g hg)
    · exact comm_of_intertwine EA EB _ _ (lA τ Y hY) (lB τ Y hY)
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar ι Pi₀ ρ hrank hirr _ hcomm
  have hT' : ∀ x, EB.symm (EA x) = c • x := fun x => by
    have := LinearMap.congr_fun hc x
    simpa using this
  haveI : Nontrivial Pi₀ := hm₀.irred.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Pi₀)
    have h1 := hT' x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h1
    exact hx h1
  refine ⟨EB, c, hc0, fun Φ hΦ => ?_, fun Φ hΦ => hEB Φ hΦ⟩
  rw [hEA Φ hΦ, ← LinearEquiv.map_smul, ← hT', LinearEquiv.apply_symm_apply]
theorem _root_.GlobalTheory.T.theta_stage_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (a b : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j a b X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), ∀ (Pi₀ : ModuleCat.{0} ℂ) rf₀ rl₀ p₀ p₀' (Pi : ModuleCat.{0} ℂ) rf rl p p',
    GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi₀ rf₀ rl₀ p₀ p₀' →
    GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∃ (E : Pi₀ ≃ₗ[ℂ] Pi) (c : ℂ), c ≠ 0 ∧ (∀ Φ ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW, p Φ = c • E (p₀ Φ)) ∧
      ∀ Φ' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW, p' Φ' = E (p₀' Φ') := by
  intro hP _ hL
  refine grid_bigness_mono GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b _ H W i j a a' A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  obtain ⟨_, _, _, _, _, -, -, -, hall⟩ := H W i j a a' A A' WW X hX
  have hIs := hX.2.2.2.2.2.2.2
  exact _root_.GlobalTheory.StageUniq.stage_unique_of_archimedean_triple hP.howeDualityReal hP hL W.ψ W.θ hIs.isVac.2.inf _ _ (hall t).1 X.m X.fd X.m' X.fd'
    hIs.meas hIs.meas' (X.ω t) (X.ω' t) FA FA' FW Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
end GlobalTheory.StageUniq
end
end
end
