module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMemMultT
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopLift

open GlobalTheory.Mem.ColAd Filter Topology

section Comp

variable {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem finN_mem_UPts (g : GA D V) : finN V hn g ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn))
    (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  exact GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V g)

theorem finN_eq (g : GA D V) (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (h : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom V g)).1 i j = y.1 (finCongr hn i) (finCongr hn j)) : finN V hn g = y := by
  subst hn
  exact Units.ext (Matrix.ext h)

theorem infN_atTau (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) (atTau θ V τ g) ρ : Matrix (Fin n) (Fin n) ℂ) =
      (Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  have h : IsAtTau θ V τ g (atTau θ V τ g) := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  show Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ g) = Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ
  by_cases c : ρ = τ
  · subst c
    rw [Function.update_self]
    exact h.2.1
  · rw [Function.update_of_ne c]
    exact h.2.2 ρ c


end Comp

section Main

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} (θ : InfFam D)

def finPt (h : GA D D.sp.X') : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ⟨finN D.sp.X' (rankP D) h, finN_mem_UPts D.sp.X' (rankP D) h⟩

theorem finPt_mul (h k : GA D D.sp.X') : (finPt (h * k)).1 = (finPt h).1 * (finPt k).1 := map_mul (finN D.sp.X' (rankP D)) h k

abbrev infPt : GA D D.sp.X' →* (D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) := infN θ D.sp.X' (rankP D) (Equiv.refl _)

theorem finPt_of_hasMat {h : GA D D.sp.X'} {y} (hh : HasMat h y) : (finPt h).1 = y := finN_eq _ (rankP D) h y hh.2

variable {g : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → FrP D → ℂ}

theorem finPt_mul_inf (h : GA D D.sp.X') {k : GA D D.sp.X'} (hk : k ∈ GinfC D.sp.X') : finPt (h * k) = finPt h := by
  refine Subtype.ext ?_
  rw [finPt_mul, show (finPt k).1 = 1 from finN_of_inf (rankP D) hk, mul_one]

theorem infPt_of_fin {k : GA D D.sp.X'} (hk : k ∈ GfC D.sp.X') : infPt θ k = 1 := infN_of_fin θ (rankP D) _ hk

variable (Bf : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ)

end Main

end GlobalTheory.Core.Rk.TopLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.InertSym

theorem cosets_eq {G : Type} [Group G] (K : Subgroup G) {g g' : G} {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : g' = a * g * b) (c : G ⧸ K) :
    (∃ k ∈ K, c = ((k * g' : G) : G ⧸ K)) ↔ (∃ k ∈ K, c = ((k * g : G) : G ⧸ K)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, mul_mem hk ha, ?_⟩
    rw [e, show k * (a * g * b) = (k * a * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, mul_mem hk (inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = (k * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]

theorem cosetSym_of_inv {G : Type} [Group G] (K : Subgroup G)
    (h : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, g⁻¹ = a * g * b) : CosetSym K := by
  intro g
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun c => cosets_eq K ha hb e c)).symm

theorem inv_mem_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) (g : GU σ n) :
    ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g⁻¹ = a * g * b := by
  have hint : ∀ i j, Formalism.UG.antiJ L n i j ∈ Formalism.UG.intL L := by
    intro i j; unfold Formalism.UG.antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := Formalism.UG.P.cartan_exists_glint (Formalism.UG.intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := (GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm).1 L ϖ σ q n J hU hJ (by
    intro i j
    rw [hJe]
    simp only [Formalism.UG.antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (g : GL (Fin n) L) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

end GlobalTheory.ChainOnto.InertSym

namespace GlobalTheory.ChainOnto

theorem inert_cosetSym_heckeEven : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ n : ℕ, IsCommensurated (KU σ n) ∧ CosetSym (KU σ n) ∧ ∀ φ ∈ Hecke ℂ (KU σ n), ∀ g, φ g⁻¹ = φ g := by
  intro L _ _ _ ϖ σ q hU n
  refine ⟨Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n, InertSym.cosetSym_of_inv _ (InertSym.inv_mem_KU hU n), ?_⟩
  intro φ hφ g
  obtain ⟨a, ha, b, hb, e⟩ := InertSym.inv_mem_KU hU n g
  rw [e]
  exact hφ.1 ⟨a, ha⟩ ⟨b, hb⟩ g

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ n : ℕ, IsCommensurated (KU σ n) ∧ CosetSym (KU σ n) ∧ ∀ φ ∈ Hecke ℂ (KU σ n), ∀ g, φ g⁻¹ = φ g := by
  first | exact @GlobalTheory.ChainOnto.inert_cosetSym_heckeEven | exact GlobalTheory.ChainOnto.inert_cosetSym_heckeEven | (intros; apply GlobalTheory.ChainOnto.inert_cosetSym_heckeEven <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegrableBoundDoublingIntegrandQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegrableBoundDoublingIntegrandQuotient
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Dom

theorem exists_integrable_bound_dblIntegrandQ : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q := by
  intro D V μ m hm f₁ f₂ hf₁ hf₂ C' c hC' C N
  have hC'1 : 1 ≤ C' := by
    have h := hC' 1 1
    have e : io V ((1 : GA D V), (1 : GA D V)) = 1 := map_one (io V)
    simp only [e, GlobalTheory.Grow.height_one, mul_one, one_pow] at h
    exact h
  set K : ℝ := max C 0 * (C' * 4 ^ c) ^ N with hK
  have i₁ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₁ hf₁ (c * N)
  have i₂ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₂ hf₂ (c * N)
  refine ⟨fun q => K * ((GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * ‖f₁ q.1.out‖) *
      (GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N) * ‖f₂ q.2.out‖)), (i₁.mul_prod i₂).const_mul K, ?_⟩
  intro E hE hEb q
  obtain ⟨γ₁, hγ₁, h₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, h₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) *
      GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
    rw [hinv]
    refine (hEb _).trans ?_
    have hh := hC' (γ₁ * q.1.out) (γ₂ * q.2.out)
    have hprod : GlobalTheory.Grow.height V (γ₁ * q.1.out) * GlobalTheory.Grow.height V (γ₂ * q.2.out) ≤
        4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
      have := mul_le_mul h₁ h₂ (by linarith) (by linarith)
      linarith
    have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
        C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c := by
      refine hh.trans ?_
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hprod c) (by linarith)
    have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
    calc C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N
        ≤ max C 0 * (C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N) (le_max_right _ _)
      _ = K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
          rw [hK, pow_mul, pow_mul]; ring
  have hμ : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, norm_mul, hμ, mul_one, Complex.norm_conj]
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg (by linarith) (by positivity)) N)
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

end GlobalTheory.Core.Rk.Dom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegrableBoundDoublingIntegrandQuotientStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrable_bound_doubling_integrand_quotient : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q := by
  first | exact @GlobalTheory.Core.Rk.Dom.exists_integrable_bound_dblIntegrandQ | exact GlobalTheory.Core.Rk.Dom.exists_integrable_bound_dblIntegrandQ | (intros; apply GlobalTheory.Core.Rk.Dom.exists_integrable_bound_dblIntegrandQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AntiOfStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.HdNc

theorem anti_of_step {r : ℕ} (f : Fin r → ℝ) (h : ∀ (i : Fin r) (hi : i.1 + 1 < r), f ⟨i.1 + 1, hi⟩ < f i) :
    ∀ a b : Fin r, a ≤ b → f b ≤ f a := by
  have key : ∀ (d a : ℕ) (ha : a + d < r), f ⟨a + d, ha⟩ ≤ f ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; exact le_rfl
    | succ d ih =>
      intro a ha
      have h1 := h ⟨a + d, by omega⟩ (by simp only []; omega)
      have h2 := ih a (by omega)
      have e : (⟨(⟨a + d, by omega⟩ : Fin r).1 + 1, by simp only []; omega⟩ : Fin r) = ⟨a + (d + 1), ha⟩ := by
        ext; simp only []; omega
      rw [e] at h1
      linarith
  intro a b hab
  have hd := key (b.1 - a.1) a.1 (by omega)
  have e1 : (⟨a.1 + (b.1 - a.1), by omega⟩ : Fin r) = b := by ext; simp only []; omega
  rw [e1] at hd
  exact hd

theorem lamS_node (R : Ranks) (P : HCParam R) (j : ℕ) (hj : j < R.m) (hi : R.k - 1 + j < R.r) :
    lamS R P ⟨R.k - 1 + j, hi⟩ = -(((P.b ⟨j, hj⟩ : ℚ)) : ℝ) := by
  unfold lamS
  rw [dite_eq_right (by simp only []; omega)]
  have e : R.k - 1 + j - (R.k - 1) = j := by omega
  simp only [e, dif_pos hj]

theorem node_of_sign (R : Ranks) (a b : Fin R.r) (hab : a < b) (hne : epsS R a ≠ epsS R b) : R.k ≤ b.1 := by
  by_contra hb
  push_neg at hb
  apply hne
  have ha : a.1 < R.k - 1 := by
    have : a.1 < b.1 := hab
    omega
  unfold epsS
  rw [if_pos ha]
  by_cases h1 : b.1 < R.k - 1
  · rw [if_pos h1]
  · rw [if_neg h1]
    have : b.1 - (R.k - 1) = 0 := by omega
    simp [this]

theorem gap_lt {D : D7} {L C' Cl Cg cb Cu cT CT : ℝ} (H : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (τ : D.what₂.Tau) (a b : Fin D.R.r) (hab : a < b) (hne : epsS D.R a ≠ epsS D.R b) :
    Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤ lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b := by
  have hkb := node_of_sign D.R a b hab hne
  have hbr : b.1 < D.R.r := b.2
  have hm2 := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hgap := GlobalTheory.Core.Rk.HdGap.gap_of H τ (b.1 - D.R.k) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlam, -, -, hCl⟩ := H
  have hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r),
      lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i := by
    intro i hi
    have := hlam τ i hi
    have h0 : (0 : ℝ) ≤ Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 + (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by positivity
    linarith
  set j := b.1 - D.R.k with hj
  have hj1 : j + 1 < D.R.m := by omega
  have e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩ := by ext; simp only []; omega
  have hc : (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) ≤ b := by
    rw [Fin.le_def]; simp only []; omega
  have hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) := by
    rw [Fin.le_def]; simp only []; have : a.1 < b.1 := hab; omega
  have h1 := anti_of_step _ hstep _ _ hac
  have h2 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L ≤
      (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := hgap
  rw [lamS_node D.R (D.hc τ) j (by omega) (by omega)] at h1
  rw [e1, lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]
  linarith

theorem hd_nc : ∃ Cl₀ : ℝ, ∀ (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ), Cl₀ ≤ Cl → HD D L C' Cl Cg cb Cu cT CT →
    ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  refine ⟨1801, fun D L C' Cl Cg cb Cu cT CT hCl H X => ?_⟩
  have HL := H.2.2.1
  obtain ⟨hS, hr⟩ := GlobalTheory.Core.Rk.HdGap.scale_of hCl HL
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast (show 1 ≤ D.R.r by omega)
  have h4 : 100 * (D.R.r : ℝ) ^ 4 ≤ 1801 * (D.R.r : ℝ) ^ 19 := by
    have : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hr1 (by norm_num)
    have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
    linarith
  have key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b →
      100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b| := by
    intro τ a b hne
    have hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4 := by positivity
    rcases lt_trichotomy a b with h | h | h
    · have := gap_lt HL τ a b h hne
      rw [abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (by rw [h]) hne
    · have := gap_lt HL τ b a h (Ne.symm hne)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  intro v a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq]
  exact key _ _ _ hab

end GlobalTheory.Core.Rk.HdNc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CosetSymGL

abbrev Cos {G : Type} [Group G] (K : Subgroup G) (g : G) : Type :=
  {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)}

theorem card_cos_eq_of_mem {G : Type} [Group G] {K : Subgroup G} {g h a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : h = a * g * b) : Nat.card (Cos K h) = Nat.card (Cos K g) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, K.mul_mem hk ha, ?_⟩
    rw [e, ← mul_assoc, ← mul_assoc, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, K.mul_mem hk (K.inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = k * g * b by group, QuotientGroup.mk_mul_of_mem _ hb]

def quotEquiv {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) : G ⧸ K ≃ G ⧸ K :=
  Quotient.congr θ.toEquiv fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel K (θ a) (θ b)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul, hθ]

theorem quotEquiv_mk {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (x : G) :
    quotEquiv K θ hθ (x : G ⧸ K) = ((θ x : G) : G ⧸ K) := rfl

theorem card_cos_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (g : G) :
    Nat.card (Cos K g) = Nat.card (Cos K (θ g)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (quotEquiv K θ hθ) fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨θ k, (hθ k).2 hk, by rw [quotEquiv_mk, map_mul]⟩
  · rintro ⟨k, hk, e⟩
    refine ⟨θ.symm k, (hθ _).1 (by simpa using hk), (quotEquiv K θ hθ).injective ?_⟩
    rw [e, quotEquiv_mk, map_mul, MulEquiv.apply_symm_apply]

theorem cosetSym_of_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K)
    (h : ∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g⁻¹ * b) : CosetSym K := fun g => by
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (card_cos_aut K θ hθ g).trans (card_cos_eq_of_mem ha hb e)

end GlobalTheory.ChainOnto.CosetSymGL

namespace GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.LFun.ConjPlace in
theorem invT_of_symm {L : Type} [Field L] {n : ℕ} (d : GL (Fin n) L)
    (hd : (d : Matrix (Fin n) (Fin n) L)ᵀ = (d : Matrix (Fin n) (Fin n) L)) : invT (RingEquiv.refl L) n d = d⁻¹ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invT_val, RingEquiv.refl_apply, Matrix.coe_units_inv]
  conv_lhs => rw [← hd]
  rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]

open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_iff {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L) :
    invT (RingEquiv.refl L) n g ∈ Formalism.UG.GLint (Fin n) O ↔ g ∈ Formalism.UG.GLint (Fin n) O :=
  (mem_iff_invT (RingEquiv.refl L) (O := O) (O' := O) (fun _ => Iff.rfl) g).symm


open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_doset (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) : ∃ a ∈ KGL w (n := n), ∃ b ∈ KGL w (n := n),
      invT (RingEquiv.refl _) n g = a * g⁻¹ * b := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := E) w
  have hϖO : ϖ ∈ Formalism.UG.Ov E w := by
    change Valued.v ϖ ≤ 1
    unfold Formalism.UG.IsUnifV at hϖ
    rw [hϖ]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, hg⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  set d : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hd
  have hdv : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hd, Units.val_mul, Units.val_mul, hg, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc,
      Units.mul_inv, mul_one]
  have hsym : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hdv, Formalism.UG.diagPow, Matrix.diagonal_transpose]
  have hgd : g = k₁ * d * k₂ := by rw [hd]; group
  set θ := invT (RingEquiv.refl (w.adicCompletion E)) n
  refine ⟨θ k₁ * k₂, (KGL w (n := n)).mul_mem ((invT_mem_iff _ _).2 hk₁) hk₂,
    k₁ * θ k₂, (KGL w (n := n)).mul_mem hk₁ ((invT_mem_iff _ _).2 hk₂), ?_⟩
  have hθd : θ d = d⁻¹ := invT_of_symm d hsym
  rw [hgd, map_mul, map_mul, hθd, hd]
  group

end GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.ChainOnto.CosetSymGL GlobalTheory.LFun.ConjPlace in
theorem GlobalTheory.ChainOnto.kGL_commensurated_cosetSym : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w (n := n)) ∧ CosetSym (KGL w (n := n)) := fun E _ _ w n =>
  ⟨Formalism.UG.Final.GLintComm E w n, cosetSym_of_aut _ (invT (RingEquiv.refl _) n) (fun x => invT_mem_iff _ x)
    (invT_mem_doset E w n)⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymmStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w (n := n)) ∧ CosetSym (KGL w (n := n)) := by
  first | exact @GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | exact GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | (intros; apply GlobalTheory.ChainOnto.kGL_commensurated_cosetSym <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmaller
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslates
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.AvgHecke

open GlobalTheory.PRep

theorem exists_hecke_of_mem_span : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  classical
  intro G _ K hK M _ _ ρ s w hs hw hspan
  have hx : s ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hs
  have hy : w ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hw
  have hr : w ∈ LinearMap.range (GlobalTheory.LFun.HeckeScalar.orbitMap ρ K s) := by
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨g, rfl⟩
    exact ⟨Finsupp.single (g : G ⧸ K) 1, by rw [GlobalTheory.LFun.HeckeScalar.orbitMap_single hx, one_smul]⟩
  obtain ⟨φ, rfl⟩ := hr
  obtain ⟨ψ, hψ, e⟩ := GlobalTheory.LFun.HeckeScalar.exists_fixed_preimage _ (GlobalTheory.LFun.HeckeScalar.orbitMap_permRep hx)
    (GlobalTheory.LFun.HeckeScalar.mem_finOrbit hK φ) hy
  refine ⟨fun g => ψ g, ⟨fun a b g => ?_, ψ.support.image Quotient.out, fun g hg => ?_⟩, ?_⟩
  · have := GlobalTheory.LFun.HeckeScalar.permRep_apply (a : G) ψ (g : G ⧸ K)
    rw [GlobalTheory.LGrp.mem_fixed.1 hψ _ a.2] at this
    simpa using this
  · obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), 1, j⁻¹, by simp [hj]⟩
  · rw [← e, heckeVec, GlobalTheory.LFun.HeckeScalar.orbitMap, Finsupp.linearCombination_apply, Finsupp.sum,
      finsum_eq_sum_of_support_subset (s := ψ.support)]
    · simp
    · intro c hc
      by_contra h
      exact hc (by simp [Finsupp.notMem_support_iff.1 h])

end GlobalTheory.SphTheta.AvgHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslatesStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  first | exact @GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | exact GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | (intros; apply GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmaller
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LFun (heckeVec)

namespace GlobalTheory.ChainOnto


open Formalism.UG GlobalTheory.Hk3 GlobalTheory.SphTheta in
theorem heckeVec_howe : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  intro hH L _ _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS h' hh'
  have hU := hS.1.unr
  obtain ⟨-, hw2⟩ := hH L ϖ σ q δ n n' (antiG L n) (antiG L n') ψ M ρ ω hS.1 s hS.2.1 hS.2.2.1 hS.2.2.2
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hK' := P.isCommensurated_integral_unitary_of_unramified hU n'
  have f1 : ∀ k ∈ KU σ n, ω (k, 1) s = s := fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (one_mem _) s hS.2.2.1
  have f2 : ∀ k ∈ KU σ n', ω (1, k) s = s := fun k hk => hS.1.fix 1 k (one_mem _) (mem_KU_iff.1 hk) s hS.2.2.1
  set w := heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s with hw
  have w1 : ∀ k ∈ KU σ n, ω (k, 1) w = w := fun k hk => by
    rw [hw, GlobalTheory.LFun.map_heckeVec hK' hh' (ρ' := ω.comp (MonoidHom.inr _ _)) (ω (k, 1)) (fun g y => by
      show (ω (k, 1) * ω (1, g)) y = (ω (1, g) * ω (k, 1)) y
      rw [← map_mul, ← map_mul]
      simp), f1 k hk]
  have w2 : ∀ k ∈ KU σ n', ω (1, k) w = w := fun k hk => by
    have hs : s ∈ GlobalTheory.PRep.fixed (ω.comp (MonoidHom.inr _ _)) (KU σ n') := GlobalTheory.LGrp.mem_fixed.2 f2
    let e : GU σ n' ⧸ KU σ n' ≃ GU σ n' ⧸ KU σ n' := MulAction.toPerm k
    conv_rhs => rw [hw, GlobalTheory.LFun.heckeVec_eq_of_section hh'.1 hs (fun c => k * (e.symm c).out) (fun c => by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      exact e.apply_symm_apply c), ← finsum_comp_equiv e]
    rw [hw]
    refine ((ω (1, k)).toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK' hh' _ s)).trans (finsum_congr fun c => ?_)
    have := hh'.1 ⟨k, hk⟩ 1 c.out
    simp only [OneMemClass.coe_one, mul_one] at this
    simp only [Equiv.symm_apply_apply, this, map_mul, LinearMap.toAddMonoidHom_coe, map_smul]
    rfl
  obtain ⟨h, hh, e⟩ := GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates _ (KU σ n) hK M (ω.comp (MonoidHom.inl _ _)) s w f1 w1
    (hw2 w fun g hg => w2 g (mem_KU_iff.2 hg))
  exact ⟨h, hh, e⟩

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmallerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  first | exact @GlobalTheory.ChainOnto.heckeVec_howe | exact GlobalTheory.ChainOnto.heckeVec_howe | (intros; apply GlobalTheory.ChainOnto.heckeVec_howe <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotent
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

def stkRows {R : Type} {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) R) : Matrix (Fin (a + a)) (Fin k) R :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem stkRows_mul {R : Type} [CommRing R] {a k l : ℕ} (X Y : Matrix (Fin a) (Fin k) R) (B : Matrix (Fin k) (Fin l) R) :
    stkRows X Y * B = stkRows (X * B) (Y * B) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [stkRows, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp [Matrix.mul_apply]

theorem keepsDiag_mul_stkRows {R : Type} [CommRing R] {n k : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    (h : KeepsDiag finSumFinEquiv M) (X : Matrix (Fin n) (Fin k) R) :
    M * stkRows X X = stkRows (leviMat finSumFinEquiv M * X) (leviMat finSumFinEquiv M * X) := by
  have hk := (keepsDiag_iff finSumFinEquiv).1 h
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Matrix.mul_apply, stkRows, Matrix.submatrix_apply, id]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  rw [← Finset.sum_add_distrib]
  rcases s with a | a
  · simp only [Matrix.fromRows_apply_inl, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, add_mul]
  · simp only [Matrix.fromRows_apply_inr, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, ← add_mul, ← hk]

theorem rat_stackRows {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) D.host.E) :
    rat (stackRows X Y) = stkRows (rat X) (rat Y) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [rat, stackRows, stkRows, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp

theorem dblDec_jX (A : HSp D) : (dblDec A).jX = stkRows (giA A) (giA A) := rat_stackRows _ _

theorem siegel_mt_jX (A : HSp D) {g : GA D (dblSp A)} (hg : g ∈ siegel A) :
    mt (dblSp A) g ⬝ (dblDec A).jX =
      (dblDec A).jX ⬝ (gA A ⬝ leviMat finSumFinEquiv (mt (dblSp A) g) ⬝ giA A) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp A) g) := mem_siegelOf.1 hg
  rw [dblDec_jX, keepsDiag_mul_stkRows hk, stkRows_mul]
  simp only [← Matrix.mul_assoc, giA_mul_gA, Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem siegel_eq_levi_nC : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank),
    (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  intro D A p
  obtain ⟨p, hp⟩ := p
  obtain ⟨α, hα⟩ : ∃ α : Mx D A.rank A.rank, mt (dblSp A) p ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α := ⟨_, siegel_mt_jX A hp⟩
  obtain ⟨α', hα'⟩ : ∃ α' : Mx D A.rank A.rank, mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α' :=
    ⟨_, siegel_mt_jX A (inv_mem hp)⟩
  have e1 : α ⬝ α' = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α ⬝ α') := by
      calc (dblDec A).jX = mt (dblSp A) (p * p⁻¹) ⬝ (dblDec A).jX := by
            rw [mul_inv_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p ⬝ (mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α ⬝ α') := by rw [hα', ← Matrix.mul_assoc, hα, Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have e2 : α' ⬝ α = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α' ⬝ α) := by
      calc (dblDec A).jX = mt (dblSp A) (p⁻¹ * p) ⬝ (dblDec A).jX := by
            rw [inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p⁻¹ ⬝ (mt (dblSp A) p ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α' ⬝ α) := by rw [hα, ← Matrix.mul_assoc, hα', Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have u := GlobalTheory.MixModel.mt_unitary (dblSp A) p

  have h1 : adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 1 := by
    calc adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (mt (dblSp A) p ⬝ (dblDec A).jX) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) := by
          rw [hα, (dblDec A).pY_eq, adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (dblDec A).jX ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [u, (dblDec A).gram_XY]
  have hG : adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 0 := by
    calc adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (dblDec A).jY ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [u, (dblDec A).gram_YY]
  generalize hYdef : mt (dblSp A) p ⬝ (dblDec A).jY = Y at h1 hG
  have hpY : (dblDec A).pY ⬝ Y = adj α' := by
    calc (dblDec A).pY ⬝ Y = (adj α' ⬝ adj α) ⬝ ((dblDec A).pY ⬝ Y) := by
          rw [← adj_mul, e1, adj_one, Matrix.one_mul]
      _ = adj α' := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h0 : (dblDec A).j0 ⬝ (dblDec A).p0 = 0 :=
    Matrix.ext fun i j => by rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  generalize hu : (dblDec A).pX ⬝ Y = w
  have hY : Y = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
    calc Y = ((dblDec A).jX ⬝ (dblDec A).pX + (dblDec A).j0 ⬝ (dblDec A).p0 + (dblDec A).jY ⬝ (dblDec A).pY) ⬝ Y := by
          rw [(dblDec A).sum_eq_one, Matrix.one_mul]
      _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
          rw [h0, add_zero, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hpY, hu, add_comm]
  have hskew : adj (α' ⬝ w) = -(α' ⬝ w) := by
    rw [hY] at hG
    simp only [adj_add, adj_mul, adj_adj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₃ (dblDec A).gram_YY, cancel₃ (dblDec A).gram_YX, cancel₃ (dblDec A).gram_XY, cancel₃ (dblDec A).gram_XX,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero] at hG
    rw [adj_mul, eq_neg_iff_add_eq_zero]
    exact hG
  let a : GL (Fin A.rank) (AE D) := ⟨α, α', e1, e2⟩
  refine ⟨a, ⟨α' ⬝ w, mem_skewA.2 hskew⟩, (dblDec A).ga_ext ?_ ?_ ?_⟩
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jX, (dblDec A).levi_jX, hα]
  · exact Matrix.ext fun _ j => Fin.elim0 j
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jY, Matrix.mul_add, (dblDec A).levi_jY,
      ← Matrix.mul_assoc, (dblDec A).levi_jX, hYdef, hY]
    show _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ α ⬝ (α' ⬝ w)
    rw [Matrix.mul_assoc (dblDec A).jX, ← Matrix.mul_assoc α, e1, Matrix.one_mul]

end GlobalTheory.Core.Rk.SWLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotentStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSiegel_eq_levi_mul_unipotent : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | exact GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC | (intros; apply GlobalTheory.Core.Rk.SWLaw.siegel_eq_levi_nC <;> assumption)
end
end
