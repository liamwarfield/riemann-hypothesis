module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageRankFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalCompactificationPolarisedCharts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

theorem gbig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalIntegralHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedChartsForFan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg

theorem hasChart_of_hasPolChart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o)
    (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) (hn : n ≠ 0) (h : HasPolChart F s j e φ BD d x) :
    HasChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, ⟨hc, hz, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨hM, hX, hδ, hdef, hmon⟩, ha, hBD⟩ := h
  have hCN : IsCN R := ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2, hc, hz⟩
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0
    have := ht.2 (Pi.single i 1) (by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
      simp [h0]) i
    simp at this
  have hsym : ∀ i y z, ((n : ℤ) • δ i) y z = ((n : ℤ) • δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, (mem_balForms_int.1 (hδ.mem i)) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hδ.nonneg i y)
  have hpos : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    exact ⟨i, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hi⟩
  obtain ⟨R', _, _, _, ρ, r, D, ε, hCN', hinj, hfin, hloc, hr, href, hmon'⟩ :=
    GlobalTheory.T.refine_polarised_monomial_periods_monomial_data R Q m t (fun i => (n : ℤ) • δ i) hCN hmon ht.1 ht0 hsym hnn hpos
  obtain ⟨G', _, _, π, A, U, hU⟩ := hM.unif R' ρ hCN' hinj hfin D ε href
  let ϑ : Fin m → LinearMap.BilinForm ℤ D.toPre.X := fun i => pull ε.toIntLinearEquiv.toLinearMap (δ i)
  have hϑ : ∀ (k : ℤ) i, pull ε.toIntLinearEquiv.toLinearMap (k • δ i) = k • ϑ i := fun k i =>
    LinearMap.ext₂ fun y z => by simp [ϑ]
  refine ⟨R, inferInstance, inferInstance, b, ξ, m, t, R', inferInstance, inferInstance, inferInstance, ρ, r, G', inferInstance,
    inferInstance, π, D, A, U, ϑ, a, ⟨hc, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨⟨hCN'.1, inferInstance, hCN'.2.1, hCN'.2.2.1⟩, hCN'.2.2.2, hinj, hfin, hloc, hr⟩,
    ⟨hU, ?_, hδ.pull_equiv ε.toIntLinearEquiv, ?_⟩, fun i => ?_, hBD⟩
  · rw [LinearEquiv.finrank_eq ε.toIntLinearEquiv]; exact hX
  · convert hmon' using 2 with i
    rw [hϑ, ← mul_smul]
  · rw [ha i, ← hϑ, evalZ_pull φ ε.toIntLinearEquiv.surjective]

end GlobalTheory.PolDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSiegelChart_of_polarisedMonomialPeriodChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → HasPolChart F s j e φ BD d x → HasChart F s j e φ BD d x := by
  first | exact @GlobalTheory.PolDeg.hasChart_of_hasPolChart | exact GlobalTheory.PolDeg.hasChart_of_hasPolChart | (intros; apply GlobalTheory.PolDeg.hasChart_of_hasPolChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGenerated
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleTwistLarger

theorem isAmpleLB_tens_lbPow_succ {S : Scheme.{0}} {L M : LB S} {N m : ℕ} (hL : L.IsLB) (hM : M.IsLB)
    (hG : GlobalTheory.IsGenerated (lbPow L N)) (hA : GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * m)) M)) :
    GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * (m + 1))) M) := by
  have h₁ := GlobalTheory.isLB_lbPow hL (N * (m + 1))
  have h₂ := GlobalTheory.isLB_lbPow hL (N * m)
  have h₃ := GlobalTheory.isLB_lbPow hL N
  have hT := GlobalTheory.CechPic.isLB_tens h₁ hM
  have hS := GlobalTheory.CechPic.isLB_tens h₂ hM
  have hq := LB.isLB_div hT hS
  refine hA.tensor_isGenerated hG hT ((GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_div hq h₃)).1 ?_)
  rw [GlobalTheory.CechPic.cls_div hq h₃, GlobalTheory.CechPic.cls_div hT hS, GlobalTheory.CechPic.cls_tens h₁ hM,
    GlobalTheory.CechPic.cls_tens h₂ hM, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL,
    Nat.mul_succ, add_smul]
  abel

theorem isAmpleLB_tens_lbPow_of_le : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  intro S L M N k hL hM hG hA k' hk
  induction k', hk using Nat.le_induction with
  | base => exact hA
  | succ m _ ih => exact isAmpleLB_tens_lbPow_succ hL hM hG ih

end GlobalTheory.AmpleTwistLarger
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGeneratedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_lbPow_mono_of_generated : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  first | exact @GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le | exact GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le | (intros; apply GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem siegelToroidalIntegral_of_polCharts
    (hfan : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ)
    (h : GlobalTheory.Published.SiegelToroidalPolCharts) : GlobalTheory.Published.SiegelToroidalIntegral := by
  intro g hg
  obtain ⟨φ, hφ, hns⟩ := hfan g
  refine ⟨φ, hφ, fun n hn hodd => ?_⟩
  obtain ⟨F, S, s, j, hj, G, hG, e, BD, d, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, k, hk⟩ :=
    h g hg φ hφ hns n hn hodd
  have hn0 : n ≠ 0 := by omega
  refine ⟨F, S, s, j, hj, G, hG, e, BD, d, N, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun x => GlobalTheory.T.hasSiegelChart_of_polarisedMonomialPeriodChart F s j e φ BD d x hn0 (h10 x), h11, h12, k, fun k' hk' => ?_⟩
  exact GlobalTheory.T.isAmple_tensor_lbPow_mono_of_generated S (hodge G g) (CechPic.dual BD.lb) N k (isLB_hodge G g)
    (CechPic.isLB_dual BD.isLB_lb) h12 hk k' hk'

end GlobalTheory.PolDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelIntegralToroidal_of_polarisedCharts : (∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ) → GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral := by
  first | exact @GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts | exact GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts | (intros; apply GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedChartsForFan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem siegelToroidalIntegral_of_polCharts :
    GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral :=
  GlobalTheory.T.siegelIntegralToroidal_of_polarisedCharts GlobalTheory.T.exists_invariant_smoothProjFan_noSelfIntersections

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedChartsForFanStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelIntegralToroidal_of_polarisedChartsForFan : GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral := by
  first | exact @GlobalTheory.siegelToroidalIntegral_of_polCharts | exact GlobalTheory.siegelToroidalIntegral_of_polCharts | (intros; apply GlobalTheory.siegelToroidalIntegral_of_polCharts <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem siegelToroidalIntegral_holds : GlobalTheory.Published.SiegelToroidalIntegral :=
  GlobalTheory.T.siegelIntegralToroidal_of_polarisedChartsForFan GlobalTheory.T.siegelToroidalCompactification_polarisedCharts

end GlobalTheory
end
